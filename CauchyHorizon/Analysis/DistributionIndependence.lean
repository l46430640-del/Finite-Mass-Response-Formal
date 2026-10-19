import CauchyHorizon.Analysis.ProductWeakDerivative

/-! An integrable field has zero weak derivative in an absent coordinate. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

theorem rectangle_independent_derivatives {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {f g : ℝ → ℝ} (hf : IntegrableOn (fun w : ℝ × ℝ => f w.2) (Icc 0 U ×ˢ Icc 0 V))
    (hg : IntegrableOn (fun w : ℝ × ℝ => g w.1) (Icc 0 U ×ˢ Icc 0 V)) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1, 0)
      (rectangleDistribution U V (fun w => f w.2)) = 0 ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, 1)
      (rectangleDistribution U V (fun w => g w.1)) = 0 := by
  constructor
  · ext ψ
    let dψ : 𝓓(openRectangle U V, ℝ) := TestFunction.lineDerivCLM ℝ (1, 0) ψ
    have hi (v : ℝ) : (∫ u in (0 : ℝ)..U, dψ (u, v)) = 0 := by
      have hd (u : ℝ) : HasDerivAt (fun t => ψ (t, v)) (dψ (u, v)) u := by
        simp only [dψ, TestFunction.lineDerivCLM_eq_fderivCLM,
          TestFunction.fderivCLM_apply_of_le _ le_top]
        exact ((ψ.contDiff.differentiable (by simp)) (u, v)).hasFDerivAt.comp_hasDerivAt u
          (HasDerivAt.prodMk (hasDerivAt_id u) (hasDerivAt_const u v))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
        ((dψ.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)]
      rw [image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl U) (ψ.tsupport_subset h).1.2),
        image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (ψ.tsupport_subset h).1.1), sub_self]
    have hs : uIoc (0 : ℝ) U ×ˢ uIoc (0 : ℝ) V ⊆ Icc 0 U ×ˢ Icc 0 V := by
      rw [uIoc_of_le hU, uIoc_of_le hV]
      exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
    have hfi := (hf.mul_continuousOn dψ.continuous.continuousOn
      (isCompact_Icc.prod isCompact_Icc)).mono_set hs
    rw [Distribution.lineDerivCLM_apply, rectangleDistribution_apply hU hV hf]
    change -(∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, f v * dψ (u, v)) = 0
    rw [intervalIntegral_intervalIntegral_swap (F := fun u v => f v * dψ (u, v)) hfi]
    simp_rw [intervalIntegral.integral_const_mul, hi, mul_zero]
    simp only [intervalIntegral.integral_zero, neg_zero]
  · ext ψ
    let dψ : 𝓓(openRectangle U V, ℝ) := TestFunction.lineDerivCLM ℝ (0, 1) ψ
    have hi (u : ℝ) : (∫ v in (0 : ℝ)..V, dψ (u, v)) = 0 := by
      have hd (v : ℝ) : HasDerivAt (fun t => ψ (u, t)) (dψ (u, v)) v := by
        simp only [dψ, TestFunction.lineDerivCLM_eq_fderivCLM,
          TestFunction.fderivCLM_apply_of_le _ le_top]
        exact ((ψ.contDiff.differentiable (by simp)) (u, v)).hasFDerivAt.comp_hasDerivAt v
          (HasDerivAt.prodMk (hasDerivAt_const v u) (hasDerivAt_id v))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
        ((dψ.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
      rw [image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl V) (ψ.tsupport_subset h).2.2),
        image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (ψ.tsupport_subset h).2.1), sub_self]
    rw [Distribution.lineDerivCLM_apply, rectangleDistribution_apply hU hV hg]
    change -(∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, g u * dψ (u, v)) = 0
    simp_rw [intervalIntegral.integral_const_mul, hi, mul_zero]
    simp only [intervalIntegral.integral_zero, neg_zero]

theorem rectangle_product_right_derivative_zero {U V A B : ℝ} {f b : ℝ × ℝ → ℝ}
    {v : ℝ × ℝ} (hb : IntegrableOn b (Icc 0 A ×ˢ Icc 0 B))
    (hf : Integrable (fun w => f w.1 * b w.2) (rectangleProductMeasure U V A B))
    (hd : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v (rectangleDistribution A B b) = 0) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, v)
      (rectangleProductDistribution U V A B (fun w => f w.1 * b w.2)) = 0 := by
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  let ν := volume.restrict (Icc 0 A ×ˢ Icc 0 B)
  change Integrable (fun w => f w.1 * b w.2) (μ.prod ν) at hf
  ext ψ
  let dψ : 𝓓(openRectangleProduct U V A B, ℝ) := TestFunction.lineDerivCLM ℝ (0, v) ψ
  have hslice (x y : ℝ × ℝ) :
      (TestFunction.lineDerivCLM ℝ v (rectangleTestSliceRight ψ x) : 𝓓(openRectangle A B, ℝ)) y =
        dψ (x, y) := by
    simp only [dψ, TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ le_top]
    change fderiv ℝ (fun t => ψ (x, t)) y v = fderiv ℝ ψ (x, y) (0, v)
    exact congrArg (fun L => L v)
      (((ψ.contDiff.differentiable (by simp)) (x, y)).hasFDerivAt.comp y
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)).fderiv
  have hi (x : ℝ × ℝ) : (∫ y, b y * dψ (x, y) ∂ν) = 0 := by
    have hh := congrArg (fun T : 𝓓'(openRectangle A B, ℝ) => T (rectangleTestSliceRight ψ x)) hd
    rw [Distribution.lineDerivCLM_apply] at hh
    change -(TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) ν b _) = 0 at hh
    rw [TestFunction.integralAgainstBilinCLM_eq_integral
      (hb.locallyIntegrable.locallyIntegrableOn _)] at hh
    simp only [ContinuousLinearMap.mul_apply', hslice, neg_eq_zero] at hh
    simpa only [mul_comm] using hh
  obtain ⟨C, hC⟩ := dψ.continuous.bounded_above_of_compact_support dψ.hasCompactSupport
  have htest := hf.mul_bdd dψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  rw [Distribution.lineDerivCLM_apply]
  change -(TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) (μ.prod ν)
    (fun w => f w.1 * b w.2) dψ) = 0
  rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
  simp only [ContinuousLinearMap.mul_apply']
  simp_rw [mul_comm (dψ _) (f _ * b _)]
  rw [integral_prod _ htest]
  simp_rw [mul_assoc, integral_const_mul, hi, mul_zero]
  simp only [integral_zero, neg_zero]

end CauchyHorizon
