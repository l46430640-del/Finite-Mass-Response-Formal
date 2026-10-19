import CauchyHorizon.Analysis.IntegratingFactor
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Positivity

/-! Continuous weighted Volterra operators for integrable endpoint-singular kernels. -/

open MeasureTheory Set
open scoped Topology NNReal

namespace CauchyHorizon

variable {a b : ℝ} (hab : a ≤ b) {c w : ℝ → ℝ}

noncomputable def extendCurve (f : C(Icc a b, ℝ)) (t : ℝ) : ℝ :=
  f (projIcc a b hab t)

theorem continuous_extendCurve (f : C(Icc a b, ℝ)) : Continuous (extendCurve hab f) :=
  f.continuous.comp continuous_projIcc

theorem weighted_integrand_integrable (hc : IntervalIntegrable c volume a b)
    (hw : ContinuousOn w (uIcc a b)) (f : C(Icc a b, ℝ)) :
    IntervalIntegrable (fun t => c t * (w t * extendCurve hab f t)) volume a b :=
  hc.mul_continuousOn (hw.mul (continuous_extendCurve hab f).continuousOn)

noncomputable def weightedPrimitive (hc : IntervalIntegrable c volume a b)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ t ∈ uIcc a b, 0 < w t)
    (f : C(Icc a b, ℝ)) : C(Icc a b, ℝ) where
  toFun x := (∫ t in a..x, c t * (w t * extendCurve hab f t)) / w x
  continuous_toFun := by
    have hp := intervalIntegral.continuousOn_primitive_interval'
      (weighted_integrand_integrable hab hc hw f) left_mem_uIcc
    have hdiv := hp.div hw (fun x hx => (hwpos x hx).ne')
    rw [uIcc_of_le hab] at hdiv
    exact hdiv.domRestrict

theorem weightedPrimitive_sub (hc : IntervalIntegrable c volume a b)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ t ∈ uIcc a b, 0 < w t)
    (f g : C(Icc a b, ℝ)) :
    weightedPrimitive hab hc hw hwpos (f - g) =
      weightedPrimitive hab hc hw hwpos f - weightedPrimitive hab hc hw hwpos g := by
  ext x
  have hsub : uIcc a (x : ℝ) ⊆ uIcc a b := by
    rw [uIcc_of_le x.property.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl x.property.2
  change (∫ t in a..(x : ℝ), c t * (w t * (extendCurve hab f t - extendCurve hab g t))) /
      w x = _
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub
    ((weighted_integrand_integrable hab hc hw f).mono_set hsub)
    ((weighted_integrand_integrable hab hc hw g).mono_set hsub), sub_div]
  rfl

theorem weightedPrimitive_norm_le (hc : IntervalIntegrable c volume a b)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ t ∈ uIcc a b, 0 < w t)
    {K : ℝ} (hK : 0 ≤ K)
    (hkernel : ∀ x ∈ Icc a b, (∫ t in a..x, |c t| * w t) ≤ K * w x)
    (f : C(Icc a b, ℝ)) : ‖weightedPrimitive hab hc hw hwpos f‖ ≤ K * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hK (norm_nonneg f))).2
  intro x
  have hx : (x : ℝ) ∈ uIcc a b := by simpa only [uIcc_of_le hab] using x.property
  have hsub : uIcc a (x : ℝ) ⊆ uIcc a b := by
    rw [uIcc_of_le x.property.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl x.property.2
  have hi := ((hc.abs.mul_continuousOn hw).mul_const ‖f‖).mono_set hsub
  have hnorm : ‖∫ t in a..(x : ℝ), c t * (w t * extendCurve hab f t)‖ ≤
      (∫ t in a..(x : ℝ), |c t| * w t * ‖f‖) := by
    apply intervalIntegral.norm_integral_le_of_norm_le x.property.1 _ hi
    apply ae_of_all
    intro t ht
    have ht' : t ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact ⟨ht.1.le, ht.2.trans x.property.2⟩
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (hwpos t ht')]
    simpa only [← mul_assoc, extendCurve, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (projIcc a b hab t))
        (mul_nonneg (abs_nonneg (c t)) (hwpos t ht').le)
  rw [intervalIntegral.integral_mul_const] at hnorm
  change ‖(∫ t in a..(x : ℝ), c t * (w t * extendCurve hab f t)) / w x‖ ≤ _
  rw [norm_div, Real.norm_of_nonneg (hwpos x hx).le]
  apply (div_le_iff₀ (hwpos x hx)).2
  calc
    _ ≤ (∫ t in a..(x : ℝ), |c t| * w t) * ‖f‖ := hnorm
    _ ≤ (K * w x) * ‖f‖ := mul_le_mul_of_nonneg_right
      (hkernel x x.property) (norm_nonneg f)
    _ = _ := by ring

theorem weightedPrimitive_lipschitz (hc : IntervalIntegrable c volume a b)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ t ∈ uIcc a b, 0 < w t)
    (K : ℝ≥0)
    (hkernel : ∀ x ∈ Icc a b, (∫ t in a..x, |c t| * w t) ≤ (K : ℝ) * w x) :
    LipschitzWith K (weightedPrimitive hab hc hw hwpos) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [dist_eq_norm, ← weightedPrimitive_sub]
  exact weightedPrimitive_norm_le hab hc hw hwpos K.coe_nonneg hkernel (f - g)

theorem weightedPrimitive_nonneg (hc : IntervalIntegrable c volume a b)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ t ∈ uIcc a b, 0 < w t)
    (hcpos : ∀ t ∈ Icc a b, 0 ≤ c t) (f : C(Icc a b, ℝ)) (hf : 0 ≤ f) :
    0 ≤ weightedPrimitive hab hc hw hwpos f := by
  intro x
  apply div_nonneg
  · apply intervalIntegral.integral_nonneg x.property.1
    intro t ht
    have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.trans x.property.2⟩
    have ht'' : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht'
    exact mul_nonneg (hcpos t ht')
      (mul_nonneg (hwpos t ht'').le (hf (projIcc a b hab t)))
  · exact (hwpos x (by simpa only [uIcc_of_le hab] using x.property)).le

end CauchyHorizon
