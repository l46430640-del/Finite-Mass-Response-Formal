import CauchyHorizon.Analysis.PacketCumulative

/-! The two-packet shape uses component energy, including when the combined input cancels. -/

open MeasureTheory Set

namespace CauchyHorizon

noncomputable def packetPairCumulative (ψ : ℝ → ℝ) (δ σ y : ℝ) : ℝ :=
  (∫ z in Iic y, (ψ z + σ * ψ (z - δ)) ^ 2) / (2 * ∫ z, ψ z ^ 2)

noncomputable def packetPairTotal (ψ : ℝ → ℝ) (δ σ : ℝ) : ℝ :=
  (∫ z, (ψ z + σ * ψ (z - δ)) ^ 2) / (2 * ∫ z, ψ z ^ 2)

theorem packet_pair_integrals {E L : ℝ} (hE : 0 ≤ E) (hL : 0 < L)
    (ψ : ℝ → ℝ) (hM : 0 < ∫ z, ψ z ^ 2) (t δ σ y : ℝ) :
    let P := fun x => Real.sqrt (E / ((∫ z, ψ z ^ 2) * L)) *
      (ψ ((x - t) / L) + σ * ψ ((x - t) / L - δ))
    (∫ x in Iic y, P x ^ 2) = 2 * E * packetPairCumulative ψ δ σ ((y - t) / L) ∧
      (∫ x, P x ^ 2) = 2 * E * packetPairTotal ψ δ σ := by
  dsimp only
  simp_rw [mul_pow, Real.sq_sqrt (div_nonneg hE (mul_pos hM hL).le)]
  constructor
  · rw [integral_const_mul,
      integral_Iic_translate_dilate hL (fun z => (ψ z + σ * ψ (z - δ)) ^ 2), packetPairCumulative]
    field_simp
  · rw [integral_const_mul,
      integral_sub_right_eq_self (fun x => (ψ (x / L) + σ * ψ (x / L - δ)) ^ 2) t,
      Measure.integral_comp_div (fun z => (ψ z + σ * ψ (z - δ)) ^ 2),
      abs_of_pos hL, smul_eq_mul, packetPairTotal]
    field_simp

theorem packet_pair_sum_eq {E L : ℝ} (hL : 0 < L)
    (ψ : ℝ → ℝ) (t δ σ x : ℝ) :
    Real.sqrt (E / ((∫ z, ψ z ^ 2) * L)) * ψ ((x - t) / L) +
      σ * (Real.sqrt (E / ((∫ z, ψ z ^ 2) * L)) * ψ ((x - (t + δ * L)) / L)) =
    Real.sqrt (E / ((∫ z, ψ z ^ 2) * L)) *
      (ψ ((x - t) / L) + σ * ψ ((x - t) / L - δ)) := by
  rw [show (x - (t + δ * L)) / L = (x - t) / L - δ by field_simp; ring]
  ring

theorem packetPairCumulative_opposite (ψ : ℝ → ℝ) (y : ℝ) :
    packetPairCumulative ψ 0 (-1) y = 0 ∧ packetPairTotal ψ 0 (-1) = 0 := by
  simp [packetPairCumulative, packetPairTotal]

end CauchyHorizon
