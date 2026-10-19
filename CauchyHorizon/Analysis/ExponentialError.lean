import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A decaying source and a width-controlled growing source have bounded integrals. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem linear_mul_exp_decay {η β t : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    (1 + β * t) * Real.exp (-η * t) ≤ (1 + 2 * β / η) * Real.exp (-(η / 2) * t) := by
  have h₀ : 1 ≤ Real.exp ((η / 2) * t) := Real.one_le_exp_iff.2 (by positivity)
  have h₁ : (η / 2) * t ≤ Real.exp ((η / 2) * t) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hh : 1 + β * t ≤ (1 + 2 * β / η) * Real.exp ((η / 2) * t) := by
    calc
      _ = 1 + (2 * β / η) * ((η / 2) * t) := by field_simp
      _ ≤ Real.exp ((η / 2) * t) + (2 * β / η) * Real.exp ((η / 2) * t) :=
        add_le_add h₀ (mul_le_mul_of_nonneg_left h₁ (by positivity))
      _ = _ := by ring
  calc
    _ ≤ ((1 + 2 * β / η) * Real.exp ((η / 2) * t)) * Real.exp (-η * t) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem quadratic_mul_exp_bound {η β t : ℝ} (hη : 0 < η) (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    (β * t) * ((1 + β * t) * Real.exp (-η * t)) ≤
      (2 * β / η) * (1 + 2 * β / η) := by
  have hlin := linear_mul_exp_decay hη hβ ht
  have hx : (η / 2) * t ≤ Real.exp ((η / 2) * t) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have htbound : β * t * Real.exp (-(η / 2) * t) ≤ 2 * β / η := by
    calc
      _ = (2 * β / η) * (((η / 2) * t) * Real.exp (-((η / 2) * t))) := by field_simp
      _ ≤ (2 * β / η) * (Real.exp ((η / 2) * t) * Real.exp (-((η / 2) * t))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le) (by positivity)
      _ = _ := by rw [← Real.exp_add]; simp
  calc
    _ ≤ (β * t) * ((1 + 2 * β / η) * Real.exp (-(η / 2) * t)) :=
      mul_le_mul_of_nonneg_left hlin (mul_nonneg hβ ht)
    _ = (β * t * Real.exp (-(η / 2) * t)) * (1 + 2 * β / η) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right htbound (by positivity)

theorem exponential_error_integral_bound {a u v C D δ : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hC : 0 ≤ C) (hD : 0 ≤ D) {f : ℝ → ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) v, |f t| ≤ C * Real.exp (-a * t) + D * u * Real.exp (a * t))
    (hw : u * Real.exp (a * v) ≤ δ) :
    (∫ t in (0 : ℝ)..v, |f t|) ≤ (C + D * δ) / a := by
  have hn : Continuous (fun t : ℝ => C * Real.exp (-a * t) + D * u * Real.exp (a * t)) := by fun_prop
  have he := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hv
    (f := fun t => |f t|) (g := fun t => C * Real.exp (-a * t) + D * u * Real.exp (a * t))
    (Filter.Eventually.of_forall (fun t ht => by simpa only [Real.norm_eq_abs, abs_abs] using hb t ⟨ht.1.le, ht.2⟩))
    (hn.intervalIntegrable _ _)
  have hneg : IntervalIntegrable (fun t : ℝ => C * Real.exp (-a * t)) volume 0 v := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).const_mul C).intervalIntegrable _ _
  have hpos : IntervalIntegrable (fun t : ℝ => D * u * Real.exp (a * t)) volume 0 v := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).const_mul (D * u)).intervalIntegrable _ _
  rw [Real.norm_eq_abs, intervalIntegral.integral_add hneg hpos,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.2 ha.ne'),
    intervalIntegral.integral_comp_mul_left _ ha.ne', integral_exp, integral_exp,
    mul_zero, mul_zero, Real.exp_zero, smul_eq_mul, smul_eq_mul, inv_neg] at he
  have h1 := mul_nonneg (mul_nonneg hC (inv_nonneg.2 ha.le)) (Real.exp_pos (-a * v)).le
  have h2 := mul_nonneg (mul_nonneg hD hu) (inv_nonneg.2 ha.le)
  have h3 := mul_le_mul_of_nonneg_left hw (mul_nonneg hD (inv_nonneg.2 ha.le))
  apply (le_abs_self _).trans (he.trans ?_)
  rw [div_eq_mul_inv]
  nlinarith only [h1, h2, h3]

end CauchyHorizon
