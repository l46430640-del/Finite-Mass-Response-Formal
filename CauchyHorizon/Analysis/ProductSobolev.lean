import CauchyHorizon.Analysis.ProductWeakDerivative

/-! The four-dimensional weak derivatives have the ordinary Lebesgue test identity. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

theorem rectangleProductMeasure_eq_volume (U V A B : ℝ) :
    rectangleProductMeasure U V A B =
      volume.restrict ((Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)) := by
  simp only [rectangleProductMeasure, Measure.volume_eq_prod, Measure.prod_restrict]

theorem HasL2ProductDerivatives.integral_identity {U V A B : ℝ}
    {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} {df : Fin 4 → (ℝ × ℝ) × (ℝ × ℝ) → ℝ}
    (h : HasL2ProductDerivatives U V A B f df) (i : Fin 4)
    (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
    let K := (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)
    IntegrableOn (fun w => f w * fderiv ℝ ψ w (productCoordinate i)) K ∧
      IntegrableOn (fun w => df i w * ψ w) K ∧
      (∫ w in K, f w * fderiv ℝ ψ w (productCoordinate i)) =
        -(∫ w in K, df i w * ψ w) := by
  let μ := rectangleProductMeasure U V A B
  let : IsFiniteMeasure μ := by
    dsimp only [μ, rectangleProductMeasure]
    simp only [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let dψ : 𝓓(openRectangleProduct U V A B, ℝ) :=
    TestFunction.lineDerivCLM ℝ (productCoordinate i) ψ
  have hdψ (w : (ℝ × ℝ) × (ℝ × ℝ)) : dψ w = fderiv ℝ ψ w (productCoordinate i) := by
    simp only [dψ, TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le ψ le_top]
  have hi : Integrable f μ := h.1.integrable (by norm_num)
  have hdi : Integrable (df i) μ := (h.2 i).1.integrable (by norm_num)
  have htest {g : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hg : Integrable g μ)
      (φ : 𝓓(openRectangleProduct U V A B, ℝ)) : Integrable (fun w => g w * φ w) μ := by
    obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
    exact hg.mul_bdd φ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hpair {g : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hg : Integrable g μ)
      (φ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B g φ = ∫ w, g w * φ w ∂μ := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ g φ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hg.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have he := congrArg (fun T : 𝓓'(openRectangleProduct U V A B, ℝ) => T ψ) (h.2 i).2
  rw [Distribution.lineDerivCLM_apply, hpair hi, hpair hdi] at he
  have he' : (∫ w, f w * dψ w ∂μ) = -(∫ w, df i w * ψ w ∂μ) := neg_eq_iff_eq_neg.1 he
  simpa only [μ, rectangleProductMeasure_eq_volume, hdψ, IntegrableOn] using
    (show Integrable (fun w => f w * dψ w) μ ∧ Integrable (fun w => df i w * ψ w) μ ∧
      (∫ w, f w * dψ w ∂μ) = -(∫ w, df i w * ψ w ∂μ) from
        ⟨htest hi dψ, htest hdi ψ, he'⟩)

end CauchyHorizon
