import CauchyHorizon.Reduced.FiniteRadialFlux

/-! Signed radial flux estimates retain the incoming contraction term. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
  {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
  (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)

include hx hr hzin hinu

theorem IsWaveIntegral.radial_gap_weighted_lower {n a : ℝ}
    (hν : ∀ (q : Icc 0 U) (w : Icc 0 V), n * Real.exp (a * w) ≤
      -radialNuField hV e Λ zIn x.1 hr q w) (u : Icc 0 U) (v : Icc 0 V) :
    n * u * Real.exp (a * v) ≤ x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0 := by
  rw [← hx.radial_horizontal_integral hr hzin hinu u v]
  have hc : Continuous (fun t => -intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v) := by fun_prop
  have hh := intervalIntegral.integral_mono_on (μ := volume) u.property.1
    (f := fun _ : ℝ => n * Real.exp (a * v)) intervalIntegrable_const (hc.intervalIntegrable _ _)
    (fun t _ => hν (projIcc 0 U hU t) v)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hh
  exact (show n * u * Real.exp (a * v) = (u : ℝ) * (n * Real.exp (a * v)) by ring).trans_le hh

omit hinu in
theorem IsWaveIntegral.radial_flux_negative_bound {ρ P O a : ℝ}
    (hρ : 0 ≤ ρ) (hP : 0 ≤ P) (hO : 0 ≤ O)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (v : Icc 0 V)
    (hpot : ∀ q, radialPotential (x.1 q v 0) e Λ ≤ -P)
    (hΩ : ∀ q, O * Real.exp (a * v) ≤ Real.exp (x.1 q v 2)) (u : Icc 0 U) :
    x.1 u v 0 * x.2.1 u v 0 ≤ x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 0 -
      ρ * P * O * u * Real.exp (a * v) := by
  let F := radialFluxField e Λ (flipRectangle x.1) (fun v u => hr u v) v
  have hsource (q : Icc 0 U) : F q ≤ -(ρ * P * O * Real.exp (a * v)) := by
    have hp := mul_le_mul_of_nonneg_left (hpot q)
      (mul_nonneg (hρ.trans (hlo q v)) (Real.exp_pos (x.1 q v 2)).le)
    have hprod := mul_le_mul (hlo q v) (hΩ q) (mul_nonneg hO (Real.exp_pos _).le) (hρ.trans (hlo q v))
    have hn := mul_le_mul_of_nonpos_left hprod (neg_nonpos.2 hP)
    change x.1 q v 0 * (Real.exp (x.1 q v 2) * radialPotential (x.1 q v 0) e Λ) ≤ _
    nlinarith only [hp, hn]
  have hb := intervalIntegral.integral_mono_on (μ := volume) u.property.1
    ((intervalExtension hU F).continuous.intervalIntegrable _ _) intervalIntegrable_const
    (fun t _ => hsource (projIcc 0 U hU t))
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hb
  rw [hx.horizontal_radial_flux hr hzin u v]
  change _ + continuousPrimitive hU F u ≤ _
  change continuousPrimitive hU F u ≤ (u : ℝ) * -(ρ * P * O * Real.exp (a * v)) at hb
  linarith only [hb]

end CauchyHorizon
