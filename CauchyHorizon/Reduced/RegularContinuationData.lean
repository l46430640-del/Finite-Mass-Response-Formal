import CauchyHorizon.Reduced.RegularWaveEnergy
import CauchyHorizon.Analysis.AffineContinuation

/-! Actual characteristic data cross regular time zero with an affine radius and constant scalar and lapse. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

noncomputable def radialHorizonVelocity {U ε : ℝ} (hεU : ε ≤ U)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ)) : C(Icc ε U, WaveVector) :=
  ⟨fun u => ![(-(anchoredAmplitude ⟨U, hεU, le_rfl⟩ Z) * O) u, 0, 0], by fun_prop⟩

def IsRegularContinuationData {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ)) (T b : ℝ)
    (z : C(Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b, C(Icc ε U, WaveVector)))
    (d : Lp C(Icc ε U, WaveVector) 2
      (volume.restrict (Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b))) : Prop :=
  IsAffineCharacteristicData (regularTime (anchoringLapse (hε.trans hεU) X) T) b
    (compactifiedWaveRow hε hεU X χ Z)
    (fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w))
    (radialHorizonVelocity hεU Z O) z d

def HasRegularContinuationData {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ)) (ρ T₀ : ℝ) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∀ T, T₀ ≤ T → 0 < T →
    ∃ z : C(Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b, C(Icc ε U, WaveVector)),
    ∃ d : Lp C(Icc ε U, WaveVector) 2
      (volume.restrict (Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b)),
      IsRegularContinuationData hε hεU X χ Z O T b z d ∧ ∀ w u, ρ / 2 ≤ z w u 0

set_option maxHeartbeats 800000 in
theorem regular_wave_continuation_data {U ε k ρ T₀ C : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (hρ : 0 < ρ) (X : (S : Ici (0 : ℝ)) → WaveState U S) (O : C(Icc ε U, ℝ))
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh)
    (hE : IsRegularWaveEnergy hε hεU k X χ Z T₀ C)
    (hfloor : ∀ (S : Ici (0 : ℝ)) u v, ρ ≤ (X S).1 u v 0)
    (hZ : ∀ u, ρ ≤ Z u 0) :
    HasRegularContinuationData hε hεU X χ Z O ρ T₀ := by
  let a := anchoringLapse (hε.trans hεU) X
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let F := fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)
  let Q := radialHorizonVelocity hεU Z O
  let b := (ρ / 2) / (‖Q‖ + 1)
  have hb : 0 < b := div_pos (half_pos hρ) (by positivity)
  have hsmall : b * ‖Q‖ ≤ ρ / 2 := by
    calc
      _ ≤ b * (‖Q‖ + 1) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hb.le
      _ = _ := div_mul_cancel₀ _ (by positivity : ‖Q‖ + 1 ≠ 0)
  have hΨzero (u : Icc ε U) : Ψ 0 u 0 = Z u 0 := by
    simp only [Ψ, compactifiedWaveRow, Function.update_self, waveNormalize_apply, Pi.sub_apply,
      if_neg (by decide : (0 : Fin 3) ≠ 2), sub_zero]
  refine ⟨b, hb, ?_⟩
  intro T hT hTpos
  have hV := hχ.2.2.2.2.2.1 T
  have hV0T := hχ.2.2.2.1 hTpos
  have hcont : ContinuousOn Ψ (Icc (regularTime a T) 0) :=
    hB.2.2.1.mono (fun w hw => ⟨hV0T.trans_le hw.1, hw.2⟩)
  have hderiv : ∀ w ∈ Ioo (regularTime a T) 0, HasDerivAt Ψ (F w) w :=
    fun w hw => hE.1 w ⟨hV0T.le.trans_lt hw.1, hw.2⟩
  have hLp : MemLp F 2 (volume.restrict (Icc (regularTime a T) 0)) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact (hE.2.1 T hT).1
  obtain ⟨z, d, hdata⟩ := exists_affine_characteristic_data hV.le hb.le hcont hderiv hLp Q
  refine ⟨z, d, hdata, ?_⟩
  intro w u
  by_cases hw : (w : ℝ) ≤ 0
  · rw [hdata.2.1 w hw]
    by_cases hw0 : (w : ℝ) = 0
    · rw [hw0, hΨzero]
      exact (half_le_self hρ.le).trans (hZ u)
    · have hw' : (w : ℝ) ∈ Ioo (regularTime a 0) 0 :=
        ⟨hV0T.trans_le w.property.1, lt_of_le_of_ne hw hw0⟩
      obtain ⟨ht, he, _hdχ⟩ := hχ.2.2.2.2.2.2.2.2.2.2.1 w hw'
      let S : Ici (0 : ℝ) := ⟨χ w, ht.le⟩
      have hf := hB.1 S (χ w) ht le_rfl u
      rw [he] at hf
      have hf0 := congrArg (fun v : WaveVector => v 0) hf
      simp only [Pi.sub_apply, if_neg (by decide : (0 : Fin 3) ≠ 2), sub_zero] at hf0
      change ρ / 2 ≤ compactifiedWaveRow hε hεU X χ Z w u 0
      rw [hf0]
      exact (half_le_self hρ.le).trans (hfloor S _ _)
  · have hw0 := (lt_of_not_ge hw).le
    rw [hdata.2.2.1 w hw0]
    change ρ / 2 ≤ Ψ 0 u 0 + (w : ℝ) * Q u 0
    rw [hΨzero]
    have hQ : -‖Q‖ ≤ Q u 0 := by
      have hn := (norm_le_pi_norm (Q u) 0).trans (Q.norm_coe_le_norm u)
      exact (abs_le.1 hn).1
    have hprod := mul_le_mul_of_nonneg_left hQ hw0
    have hwb := mul_le_mul_of_nonneg_right w.property.2 (norm_nonneg Q)
    nlinarith only [hZ u, hprod, hwb, hsmall]

end CauchyHorizon
