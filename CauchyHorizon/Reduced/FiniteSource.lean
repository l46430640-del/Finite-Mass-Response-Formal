import CauchyHorizon.Reduced.IntegralEstimates

/-! The wave sources do not depend on the conformal first derivatives. -/

open Set

namespace CauchyHorizon

theorem exists_waveSource_bound (e Λ : ℝ) {ρ R L W N : ℝ}
    (hρ : 0 < ρ) (hW : 0 ≤ W) (hN : 0 ≤ N) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ z d w : WaveVector,
      ρ ≤ z 0 → z 0 ≤ R → |z 2| ≤ L → |w 0| ≤ W → |w 1| ≤ W → |d 0| ≤ N →
      ‖waveSource e Λ z d w‖ ≤ S * (|d 1| + 1) := by
  let lo : WaveVector × WaveVector := (![ρ, 0, -L], fun _ => -W)
  let hi : WaveVector × WaveVector := (![R, 0, L], fun _ => W)
  obtain ⟨C, _hLip, hC⟩ := wave_coefficients_control (lo := lo) (hi := hi) hρ e Λ
  refine ⟨C * (1 + N), mul_nonneg C.coe_nonneg (by positivity), ?_⟩
  intro z d w hzlo hzhi hz hw0 hw1 hd
  let Z : WaveVector := ![z 0, 0, z 2]
  let D : WaveVector := ![d 0, d 1, 0]
  let Wv : WaveVector := ![w 0, w 1, 0]
  have hbox : (Z, Wv) ∈ Icc lo.1 hi.1 ×ˢ Icc lo.2 hi.2 := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro i; fin_cases i
      · exact hzlo
      · exact le_rfl
      · exact (abs_le.1 hz).1
    · intro i; fin_cases i
      · exact hzhi
      · exact le_rfl
      · exact (abs_le.1 hz).2
    · intro i; fin_cases i
      · exact (abs_le.1 hw0).1
      · exact (abs_le.1 hw1).1
      · exact neg_nonpos.2 hW
    · intro i; fin_cases i
      · exact (abs_le.1 hw0).2
      · exact (abs_le.1 hw1).2
      · exact hW
  have hD : ‖D‖ ≤ N + |d 1| := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · exact hd.trans (le_add_of_nonneg_right (abs_nonneg _))
    · exact le_add_of_nonneg_left hN
    · change |(0 : ℝ)| ≤ N + |d 1|
      rw [abs_zero]
      exact add_nonneg hN (abs_nonneg _)
  have hp := (norm_fst_le (wavePotential e Λ Z, waveLinear Z Wv)).trans (hC (Z, Wv) hbox)
  have hl := (norm_snd_le (wavePotential e Λ Z, waveLinear Z Wv)).trans (hC (Z, Wv) hbox)
  calc
    _ = ‖waveSource e Λ Z D Wv‖ := by congr 1
    _ ≤ ‖wavePotential e Λ Z‖ + ‖waveLinear Z Wv‖ * ‖D‖ := by
      rw [waveSource_affine]
      exact (norm_add_le (wavePotential e Λ Z) (waveLinear Z Wv D)).trans
        (add_le_add_right ((waveLinear Z Wv).le_opNorm D) _)
    _ ≤ C + C * (N + |d 1|) := add_le_add hp (mul_le_mul hl hD (norm_nonneg D) C.coe_nonneg)
    _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg C.coe_nonneg hN) (abs_nonneg (d 1))]

end CauchyHorizon
