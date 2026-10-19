import CauchyHorizon.Reduced.MassFlux
import CauchyHorizon.Reduced.FiniteRadialRate
import CauchyHorizon.Characteristic.Outgoing

/-! Exact first-order radial laws for the actual renormalized mass. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem renormalizedMass_first_order {r ν : ℝ} (hr : r ≠ 0) (hν : ν ≠ 0) (l ell e Λ : ℝ) :
    l = (-Real.exp ell / (4 * ν)) * horizonFunction r (renormalizedMass r ν l ell e Λ) e Λ ∧
      Real.exp ell * radialPotential r e Λ / ν - l / r =
        2 * (-Real.exp ell / (4 * ν)) * horizonK r (renormalizedMass r ν l ell e Λ) e Λ := by
  constructor
  · rw [renormalizedMass_horizonFunction hr, Real.exp_neg]
    field_simp [hν, Real.exp_ne_zero]
  · unfold radialPotential horizonK renormalizedMass
    rw [Real.exp_neg]
    field_simp [hr, hν, Real.exp_ne_zero]
    ring

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem massField_lambda_eq_kappa (z w : WaveRectangle U V) (N : C(Icc 0 U, C(Icc 0 V, ℝ)))
    (hr : ∀ u v, z u v 0 ≠ 0) (hN : ∀ u v, N u v ≠ 0) (u : Icc 0 U) (v : Icc 0 V) :
    w u v 0 = (-Real.exp (z u v 2) / (4 * N u v)) *
      horizonFunction (z u v 0) (massField e Λ z w N hr u v) e Λ :=
  (renormalizedMass_first_order (hr u v) (hN u v) (w u v 0) (z u v 2) e Λ).1

theorem IsWaveIntegral.radialNu_mass_exponential
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hν : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v < 0) (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ zIn x.1 hr
    let m := massField e Λ x.1 x.2.1 N hr
    N u v = -Real.exp (∫ t in (0 : ℝ)..v,
      2 * (-Real.exp (intervalExtension hV (x.1 u) t 2) / (4 * intervalExtension hV (N u) t)) *
        horizonK (intervalExtension hV (x.1 u) t 0) (intervalExtension hV (m u) t) e Λ) := by
  dsimp only
  rw [hx.radialNu_exponential hr hν u v]
  apply congrArg (fun b => -Real.exp b)
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [intervalExtension_apply, massField_apply]
  exact (renormalizedMass_first_order (hr u (projIcc 0 V hV t))
    (ne_of_lt (hν u (projIcc 0 V hV t))) (x.2.1 u (projIcc 0 V hV t) 0)
    (x.1 u (projIcc 0 V hV t) 2) e Λ).2

end CauchyHorizon
