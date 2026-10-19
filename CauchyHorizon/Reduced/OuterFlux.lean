import CauchyHorizon.Reduced.LongitudinalFlux

/-! The horizontal radial flux keeps the horizon term in the outer coefficient comparison. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem IsWaveIntegral.outer_lambda_coefficient {U V e Λ S A ε : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hS : 0 < S)
    (v : Icc 0 V)
    (hbound : ∀ q : Icc 0 U,
      |x.1 q v 0 * (Real.exp (x.1 q v 2) * radialPotential (x.1 q v 0) e Λ) / S + A| ≤ ε)
    (u : Icc 0 U) :
    |x.2.1 u v 0 / x.1 u v 0 - x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 0 / (x.1 u v 0) ^ 2 +
      A * u * S / (x.1 u v 0) ^ 2| ≤ ε * u * S / (x.1 u v 0) ^ 2 := by
  let F := radialFluxField e Λ (flipRectangle x.1) (fun v u => hr u v) v
  have hFi := (intervalExtension hU F).continuous.intervalIntegrable (μ := volume) (0 : ℝ) u
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (u : ℝ))
    (f := fun t => intervalExtension hU F t / S + A)
    (fun t _ => by rw [Real.norm_eq_abs]; exact hbound (projIcc 0 U hU t))
  rw [intervalIntegral.integral_add (hFi.div_const S) intervalIntegrable_const,
    intervalIntegral.integral_div, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    abs_of_nonneg u.property.1, Real.norm_eq_abs] at hb
  have hflux := hx.horizontal_radial_flux hr hzin u v
  change x.1 u v 0 * x.2.1 u v 0 = x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 0 +
    (∫ t in (0 : ℝ)..u, intervalExtension hU F t) at hflux
  have heq : x.2.1 u v 0 / x.1 u v 0 - x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 0 / (x.1 u v 0) ^ 2 +
      A * u * S / (x.1 u v 0) ^ 2 =
      ((∫ t in (0 : ℝ)..u, intervalExtension hU F t) / S + u * A) * S / (x.1 u v 0) ^ 2 := by
    field_simp [hr u v, hS.ne']
    nlinarith only [hflux]
  rw [heq, abs_div, abs_mul, abs_of_pos hS, abs_of_nonneg (sq_nonneg (x.1 u v 0))]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hS.le) (sq_nonneg _)

end CauchyHorizon
