import CauchyHorizon.Analysis.ProductWeakDerivative

/-! L1 section derivatives lift to the null directions against arbitrary four-dimensional tests. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

set_option maxHeartbeats 1500000 in
theorem null_weighted_derivatives_of_sections {U V A B : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {f₁ f₂ g₁ g₂ : ℝ × ℝ → ℝ}
    (hf₁ : IntegrableOn f₁ (Icc 0 U ×ˢ Icc 0 V))
    (hf₂ : IntegrableOn f₂ (Icc 0 U ×ˢ Icc 0 V))
    (hg₁ : IntegrableOn g₁ (Icc 0 U ×ˢ Icc 0 V))
    (hg₂ : IntegrableOn g₂ (Icc 0 U ×ˢ Icc 0 V))
    (ha₁ : ∀ᵐ v ∂volume.restrict (Icc 0 V), AbsolutelyContinuousOnInterval (fun u => f₁ (u, v)) 0 U)
    (hd₁ : ∀ᵐ v ∂volume.restrict (Icc 0 V), ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (fun t => f₁ (t, v)) (g₁ (u, v)) (Icc 0 U) u)
    (ha₂ : ∀ᵐ u ∂volume.restrict (Icc 0 U), AbsolutelyContinuousOnInterval (fun v => f₂ (u, v)) 0 V)
    (hd₂ : ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ᵐ v ∂volume.restrict (Icc 0 V),
      HasDerivWithinAt (fun t => f₂ (u, t)) (g₂ (u, v)) (Icc 0 V) v)
    (b : ℝ × ℝ → ℝ) (hb : IntegrableOn b (Icc 0 A ×ˢ Icc 0 B)) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((1, 0), (0, 0))
      (rectangleProductDistribution U V A B (fun w => f₁ w.1 * b w.2)) =
        rectangleProductDistribution U V A B (fun w => g₁ w.1 * b w.2) ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 1), (0, 0))
      (rectangleProductDistribution U V A B (fun w => f₂ w.1 * b w.2)) =
        rectangleProductDistribution U V A B (fun w => g₂ w.1 * b w.2) := by
  have h₁ : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1, 0)
      (rectangleDistribution U V f₁) = rectangleDistribution U V g₁ := by
    ext ψ
    let ψu : 𝓓(openRectangle U V, ℝ) := TestFunction.lineDerivCLM ℝ (1, 0) ψ
    have hi : ∀ᵐ v ∂volume.restrict (Icc 0 V), (∫ u in (0 : ℝ)..U, g₁ (u, v) * ψ (u, v)) =
        -(∫ u in (0 : ℝ)..U, f₁ (u, v) * ψu (u, v)) := by
      filter_upwards [ha₁, hd₁] with v ha hd
      have hψ : ContDiff ℝ 1 (fun u => ψ (u, v)) :=
        (ψ.contDiff.of_le (by simp)).comp (contDiff_id.prodMk contDiff_const)
      have hψd (u : ℝ) (_hu : u ∈ Icc 0 U) :
          HasDerivWithinAt (fun t => ψ (t, v)) (ψu (u, v)) (Icc 0 U) u := by
        dsimp only [ψu]
        rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le ψ le_top]
        exact (((ψ.contDiff.differentiable (by simp)) (u, v)).hasFDerivAt.comp_hasDerivAt u
          (HasDerivAt.prodMk (hasDerivAt_id u) (hasDerivAt_const u v))).hasDerivWithinAt
      exact (integral_weak_derivative hU ha hd hψ hψd
        (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (ψ.tsupport_subset h).1.1))
        (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl U) (ψ.tsupport_subset h).1.2))).2
    have hs : uIoc (0 : ℝ) U ×ˢ uIoc (0 : ℝ) V ⊆ Icc 0 U ×ˢ Icc 0 V := by
      rw [uIoc_of_le hU, uIoc_of_le hV]
      exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
    have hgψ := (hg₁.mul_continuousOn ψ.continuous.continuousOn
      (isCompact_Icc.prod isCompact_Icc)).mono_set hs
    have hfψ := (hf₁.mul_continuousOn ψu.continuous.continuousOn
      (isCompact_Icc.prod isCompact_Icc)).mono_set hs
    rw [Distribution.lineDerivCLM_apply, rectangleDistribution_apply hU hV hf₁,
      rectangleDistribution_apply hU hV hg₁]
    change -(∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, f₁ (u, v) * ψu (u, v)) = _
    symm
    rw [intervalIntegral_intervalIntegral_swap (F := fun u v => g₁ (u, v) * ψ (u, v)) hgψ]
    rw [intervalIntegral.integral_congr_ae_restrict (ae_mono (Measure.restrict_mono
      (show uIoc (0 : ℝ) V ⊆ Icc 0 V by rw [uIoc_of_le hV]; exact Ioc_subset_Icc_self) le_rfl) hi)]
    rw [intervalIntegral.integral_neg,
      ← intervalIntegral_intervalIntegral_swap (F := fun u v => f₁ (u, v) * ψu (u, v)) hfψ]
  have h₂ : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, 1)
      (rectangleDistribution U V f₂) = rectangleDistribution U V g₂ := by
    ext ψ
    let ψv : 𝓓(openRectangle U V, ℝ) := TestFunction.lineDerivCLM ℝ (0, 1) ψ
    have hi : ∀ᵐ u ∂volume.restrict (Icc 0 U), (∫ v in (0 : ℝ)..V, g₂ (u, v) * ψ (u, v)) =
        -(∫ v in (0 : ℝ)..V, f₂ (u, v) * ψv (u, v)) := by
      filter_upwards [ha₂, hd₂] with u ha hd
      have hψ : ContDiff ℝ 1 (fun v => ψ (u, v)) :=
        (ψ.contDiff.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id)
      have hψd (v : ℝ) (_hv : v ∈ Icc 0 V) :
          HasDerivWithinAt (fun t => ψ (u, t)) (ψv (u, v)) (Icc 0 V) v := by
        dsimp only [ψv]
        rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le ψ le_top]
        exact (((ψ.contDiff.differentiable (by simp)) (u, v)).hasFDerivAt.comp_hasDerivAt v
          (HasDerivAt.prodMk (hasDerivAt_const v u) (hasDerivAt_id v))).hasDerivWithinAt
      exact (integral_weak_derivative hV ha hd hψ hψd
        (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (ψ.tsupport_subset h).2.1))
        (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl V) (ψ.tsupport_subset h).2.2))).2
    rw [Distribution.lineDerivCLM_apply, rectangleDistribution_apply hU hV hf₂,
      rectangleDistribution_apply hU hV hg₂]
    change -(∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, f₂ (u, v) * ψv (u, v)) = _
    rw [intervalIntegral.integral_congr_ae_restrict (ae_mono (Measure.restrict_mono
      (show uIoc (0 : ℝ) U ⊆ Icc 0 U by rw [uIoc_of_le hU]; exact Ioc_subset_Icc_self) le_rfl) hi)]
    rw [intervalIntegral.integral_neg]
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  let ν := volume.restrict (Icc 0 A ×ˢ Icc 0 B)
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have htest {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) : Integrable (fun w => f w * ψ w) (μ.prod ν) := by
    obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
    exact hf.mul_bdd ψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hpair {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B f ψ = ∫ w, f w * ψ w ∂(μ.prod ν) := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) (μ.prod ν) f ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hpairL {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) (ψ : 𝓓(openRectangle U V, ℝ)) :
      rectangleDistribution U V f ψ = ∫ w, f w * ψ w ∂μ := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ f ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hlift {f g : ℝ × ℝ → ℝ} {v : ℝ × ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
      (hd : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v (rectangleDistribution U V f) =
        rectangleDistribution U V g) :
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (v, 0)
        (rectangleProductDistribution U V A B (fun w => f w.1 * b w.2)) =
        rectangleProductDistribution U V A B (fun w => g w.1 * b w.2) := by
    ext ψ
    let dψ : 𝓓(openRectangleProduct U V A B, ℝ) := TestFunction.lineDerivCLM ℝ (v, 0) ψ
    have hslice (x y : ℝ × ℝ) :
        (TestFunction.lineDerivCLM ℝ v (rectangleTestSliceLeft ψ y) : 𝓓(openRectangle U V, ℝ)) x =
          dψ (x, y) := by
      simp only [dψ, TestFunction.lineDerivCLM_eq_fderivCLM,
        TestFunction.fderivCLM_apply_of_le _ le_top]
      change fderiv ℝ (fun t => ψ (t, y)) x v = fderiv ℝ ψ (x, y) (v, 0)
      exact congrArg (fun L => L v)
        (((ψ.contDiff.differentiable (by simp)) (x, y)).hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)).fderiv
    have hi (y : ℝ × ℝ) : -(∫ x, f x * dψ (x, y) ∂μ) = ∫ x, g x * ψ (x, y) ∂μ := by
      have hh := congrArg (fun T : 𝓓'(openRectangle U V, ℝ) => T (rectangleTestSliceLeft ψ y)) hd
      rw [Distribution.lineDerivCLM_apply, hpairL hf, hpairL hg] at hh
      simp_rw [hslice] at hh
      exact hh
    rw [Distribution.lineDerivCLM_apply, hpair (hf.mul_prod hb), hpair (hg.mul_prod hb)]
    change -(∫ w, f w.1 * b w.2 * dψ w ∂(μ.prod ν)) = _
    rw [integral_prod_symm _ (htest (hf.mul_prod hb) dψ),
      integral_prod_symm _ (htest (hg.mul_prod hb) ψ), ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      simp_rw [mul_right_comm (f _) (b y), mul_right_comm (g _) (b y)]
      rw [integral_mul_const, integral_mul_const, ← neg_mul, hi]
  exact ⟨hlift hf₁ hg₁ h₁, hlift hf₂ hg₂ h₂⟩

theorem null_derivatives_of_sections {U V A B : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {f₁ f₂ g₁ g₂ : ℝ × ℝ → ℝ}
    (hf₁ : IntegrableOn f₁ (Icc 0 U ×ˢ Icc 0 V))
    (hf₂ : IntegrableOn f₂ (Icc 0 U ×ˢ Icc 0 V))
    (hg₁ : IntegrableOn g₁ (Icc 0 U ×ˢ Icc 0 V))
    (hg₂ : IntegrableOn g₂ (Icc 0 U ×ˢ Icc 0 V))
    (ha₁ : ∀ᵐ v ∂volume.restrict (Icc 0 V), AbsolutelyContinuousOnInterval (fun u => f₁ (u, v)) 0 U)
    (hd₁ : ∀ᵐ v ∂volume.restrict (Icc 0 V), ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (fun t => f₁ (t, v)) (g₁ (u, v)) (Icc 0 U) u)
    (ha₂ : ∀ᵐ u ∂volume.restrict (Icc 0 U), AbsolutelyContinuousOnInterval (fun v => f₂ (u, v)) 0 V)
    (hd₂ : ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ᵐ v ∂volume.restrict (Icc 0 V),
      HasDerivWithinAt (fun t => f₂ (u, t)) (g₂ (u, v)) (Icc 0 V) v) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((1, 0), (0, 0))
      (rectangleProductDistribution U V A B (fun w => f₁ w.1)) =
        rectangleProductDistribution U V A B (fun w => g₁ w.1) ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 1), (0, 0))
      (rectangleProductDistribution U V A B (fun w => f₂ w.1)) =
        rectangleProductDistribution U V A B (fun w => g₂ w.1) := by
  simpa only [mul_one] using null_weighted_derivatives_of_sections hU hV hf₁ hf₂ hg₁ hg₂
    ha₁ hd₁ ha₂ hd₂ (fun _ => 1)
    (continuous_const.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))

end CauchyHorizon
