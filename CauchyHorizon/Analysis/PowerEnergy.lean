import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Integrating the two scalar powers against the early-region linear weight. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem linear_weight_power_energy {z u v ω γ D C F G s t : ℝ} {w ψ : ℝ → ℝ}
    (hz : 0 ≤ z) (hzu : z ≤ u) (hs : 0 < s) (ht : 0 < t)
    (hC : 0 ≤ C) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hi : IntervalIntegrable (fun x => w x * ψ x ^ 2) volume z u)
    (hw : ∀ᵐ x ∂volume.restrict (Ioc z u), w x ≤ C * Real.exp (γ * v) * x)
    (hψ : ∀ᵐ x ∂volume.restrict (Ioc z u),
      |ψ x| ≤ F * x ^ (s - 1) + G * x ^ (t - 1))
    (hwidth : u * Real.exp (ω * v) ≤ D) :
    (∫ x in z..u, w x * ψ x ^ 2) ≤
      C * (F ^ 2 * D ^ (2 * s) / s * Real.exp (-(2 * ω * s - γ) * v) +
        G ^ 2 * D ^ (2 * t) / t * Real.exp (-(2 * ω * t - γ) * v)) := by
  have hu : 0 ≤ u := hz.trans hzu
  have hpi (q : ℝ) (hq : 0 < q) : IntervalIntegrable (fun x : ℝ => x ^ (2 * q - 1)) volume z u :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith only [hq])
  let P := fun x : ℝ => C * Real.exp (γ * v) *
    (2 * F ^ 2 * x ^ (2 * s - 1) + 2 * G ^ 2 * x ^ (2 * t - 1))
  have hPi : IntervalIntegrable P volume z u :=
    (((hpi s hs).const_mul (2 * F ^ 2)).add ((hpi t ht).const_mul (2 * G ^ 2))).const_mul _
  have hpt : ∀ᵐ x ∂volume.restrict (Ioc z u), w x * ψ x ^ 2 ≤ P x := by
    filter_upwards [hw, hψ, ae_restrict_mem measurableSet_Ioc] with x hx hψx hxm
    have hx0 : 0 < x := hz.trans_lt hxm.1
    have hpow (q : ℝ) : x * (x ^ (q - 1)) ^ 2 = x ^ (2 * q - 1) := by
      calc
        _ = x ^ (1 : ℝ) * x ^ ((q - 1) * 2) := by
          rw [Real.rpow_one, Real.rpow_mul hx0.le, Real.rpow_two]
        _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
    have hsq : ψ x ^ 2 ≤ 2 * (F * x ^ (s - 1)) ^ 2 + 2 * (G * x ^ (t - 1)) ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (ψ x)) (by positivity)).2 hψx
      rw [sq_abs] at hh
      nlinarith only [hh, sq_nonneg (F * x ^ (s - 1) - G * x ^ (t - 1))]
    calc
      _ ≤ (C * Real.exp (γ * v) * x) *
          (2 * (F * x ^ (s - 1)) ^ 2 + 2 * (G * x ^ (t - 1)) ^ 2) :=
        mul_le_mul hx hsq (sq_nonneg _) (by positivity)
      _ = P x := by
        dsimp only [P]
        calc
          _ = C * Real.exp (γ * v) *
              (2 * F ^ 2 * (x * (x ^ (s - 1)) ^ 2) + 2 * G ^ 2 * (x * (x ^ (t - 1)) ^ 2)) := by ring
          _ = _ := by rw [hpow s, hpow t]
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hpt
  have hb := intervalIntegral.integral_mono_ae_restrict hzu hi hPi hpt
  have hpowI (q : ℝ) (hq : 0 < q) :
      (∫ x in z..u, x ^ (2 * q - 1)) ≤ u ^ (2 * q) / (2 * q) := by
    rw [integral_rpow (Or.inl (by linarith only [hq])), sub_add_cancel]
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg hz _)) (by positivity)
  have hscale (q : ℝ) (hq : 0 < q) :
      Real.exp (γ * v) * u ^ (2 * q) ≤ D ^ (2 * q) * Real.exp (-(2 * ω * q - γ) * v) := by
    have hh := Real.rpow_le_rpow (mul_nonneg hu (Real.exp_pos _).le) hwidth (by positivity : 0 ≤ 2 * q)
    rw [Real.mul_rpow hu (Real.exp_pos _).le, ← Real.exp_mul] at hh
    have he : ω * v * (2 * q) + -(2 * ω * q - γ) * v = γ * v := by ring
    have hb := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(2 * ω * q - γ) * v)).le
    rw [mul_assoc, ← Real.exp_add, he, mul_comm (u ^ (2 * q))] at hb
    exact hb
  dsimp only [P] at hb
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hpi s hs).const_mul _) ((hpi t ht).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hb
  have h1 := mul_le_mul_of_nonneg_left (hpowI s hs) (by positivity : 0 ≤ 2 * F ^ 2)
  have h2 := mul_le_mul_of_nonneg_left (hpowI t ht) (by positivity : 0 ≤ 2 * G ^ 2)
  have h3 := mul_le_mul_of_nonneg_left (hscale s hs) (div_nonneg (sq_nonneg F) hs.le)
  have h4 := mul_le_mul_of_nonneg_left (hscale t ht) (div_nonneg (sq_nonneg G) ht.le)
  have hfirst := hb.trans (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity))
  have hlast := mul_le_mul_of_nonneg_left (add_le_add h3 h4) hC
  apply hfirst.trans
  convert hlast using 1 <;> ring

end CauchyHorizon
