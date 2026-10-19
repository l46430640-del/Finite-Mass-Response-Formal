import CauchyHorizon.Analysis.RectangleDistribution
import CauchyHorizon.Analysis.WeakDerivative
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Square-integrable section derivatives identify the two distributional derivatives. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

def HasL2FirstDerivatives (U V : ℝ) (f f₁ f₂ : ℝ × ℝ → ℝ) : Prop :=
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  MemLp f 2 μ ∧ MemLp f₁ 2 μ ∧ MemLp f₂ 2 μ ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1, 0) (rectangleDistribution U V f) =
      rectangleDistribution U V f₁ ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, 1) (rectangleDistribution U V f) =
      rectangleDistribution U V f₂

theorem l2_first_derivatives_of_sections {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {f f₁ f₂ : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Icc 0 U ×ˢ Icc 0 V)))
    (h₁ : MemLp f₁ 2 (volume.restrict (Icc 0 U ×ˢ Icc 0 V)))
    (h₂ : MemLp f₂ 2 (volume.restrict (Icc 0 U ×ˢ Icc 0 V)))
    (ha₁ : ∀ v, AbsolutelyContinuousOnInterval (fun u => f (u, v)) 0 U)
    (hd₁ : ∀ v, ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (fun t => f (t, v)) (f₁ (u, v)) (Icc 0 U) u)
    (ha₂ : ∀ u, AbsolutelyContinuousOnInterval (fun v => f (u, v)) 0 V)
    (hd₂ : ∀ u, ∀ᵐ v ∂volume.restrict (Icc 0 V),
      HasDerivWithinAt (fun t => f (u, t)) (f₂ (u, v)) (Icc 0 V) v) :
    HasL2FirstDerivatives U V f f₁ f₂ := by
  let : IsFiniteMeasure (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hfi : IntegrableOn f (Icc 0 U ×ˢ Icc 0 V) := hf.integrable (by norm_num)
  have h₁i : IntegrableOn f₁ (Icc 0 U ×ˢ Icc 0 V) := h₁.integrable (by norm_num)
  have h₂i : IntegrableOn f₂ (Icc 0 U ×ˢ Icc 0 V) := h₂.integrable (by norm_num)
  refine ⟨hf, h₁, h₂, ?_, ?_⟩
  · ext ψ
    let ψu : 𝓓(openRectangle U V, ℝ) := TestFunction.lineDerivCLM ℝ (1, 0) ψ
    have hi (v : ℝ) : (∫ u in (0 : ℝ)..U, f₁ (u, v) * ψ (u, v)) =
        -(∫ u in (0 : ℝ)..U, f (u, v) * ψu (u, v)) := by
      have hψ : ContDiff ℝ 1 (fun u => ψ (u, v)) :=
        (ψ.contDiff.of_le (by simp)).comp (contDiff_id.prodMk contDiff_const)
      have hψd (u : ℝ) (_hu : u ∈ Icc 0 U) :
          HasDerivWithinAt (fun t => ψ (t, v)) (ψu (u, v)) (Icc 0 U) u := by
        dsimp only [ψu]
        rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le ψ le_top]
        exact (((ψ.contDiff.differentiable (by simp)) (u, v)).hasFDerivAt.comp_hasDerivAt u
          (HasDerivAt.prodMk (hasDerivAt_id u) (hasDerivAt_const u v))).hasDerivWithinAt
      exact (integral_weak_derivative hU (ha₁ v) (hd₁ v) hψ hψd
        (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (ψ.tsupport_subset h).1.1))
        (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl U) (ψ.tsupport_subset h).1.2))).2
    have hs : uIoc (0 : ℝ) U ×ˢ uIoc (0 : ℝ) V ⊆ Icc 0 U ×ˢ Icc 0 V := by
      rw [uIoc_of_le hU, uIoc_of_le hV]
      exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
    have h₁ψ := (h₁i.mul_continuousOn ψ.continuous.continuousOn
      (isCompact_Icc.prod isCompact_Icc)).mono_set hs
    have hfψ := (hfi.mul_continuousOn ψu.continuous.continuousOn
      (isCompact_Icc.prod isCompact_Icc)).mono_set hs
    rw [Distribution.lineDerivCLM_apply, rectangleDistribution_apply hU hV hfi,
      rectangleDistribution_apply hU hV h₁i]
    change -(∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, f (u, v) * ψu (u, v)) = _
    symm
    rw [intervalIntegral_intervalIntegral_swap (F := fun u v => f₁ (u, v) * ψ (u, v)) h₁ψ]
    simp_rw [hi]
    rw [intervalIntegral.integral_neg,
      ← intervalIntegral_intervalIntegral_swap (F := fun u v => f (u, v) * ψu (u, v)) hfψ]
  · ext ψ
    let ψv : 𝓓(openRectangle U V, ℝ) := TestFunction.lineDerivCLM ℝ (0, 1) ψ
    have hi (u : ℝ) : (∫ v in (0 : ℝ)..V, f₂ (u, v) * ψ (u, v)) =
        -(∫ v in (0 : ℝ)..V, f (u, v) * ψv (u, v)) := by
      have hψ : ContDiff ℝ 1 (fun v => ψ (u, v)) :=
        (ψ.contDiff.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id)
      have hψd (v : ℝ) (_hv : v ∈ Icc 0 V) :
          HasDerivWithinAt (fun t => ψ (u, t)) (ψv (u, v)) (Icc 0 V) v := by
        dsimp only [ψv]
        rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le ψ le_top]
        exact (((ψ.contDiff.differentiable (by simp)) (u, v)).hasFDerivAt.comp_hasDerivAt v
          (HasDerivAt.prodMk (hasDerivAt_const v u) (hasDerivAt_id v))).hasDerivWithinAt
      exact (integral_weak_derivative hV (ha₂ u) (hd₂ u) hψ hψd
        (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (ψ.tsupport_subset h).2.1))
        (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl V) (ψ.tsupport_subset h).2.2))).2
    rw [Distribution.lineDerivCLM_apply, rectangleDistribution_apply hU hV hfi,
      rectangleDistribution_apply hU hV h₂i]
    change -(∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, f (u, v) * ψv (u, v)) = _
    simp_rw [hi]
    rw [intervalIntegral.integral_neg]

theorem l2_constant_derivatives {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (c : ℝ) :
    HasL2FirstDerivatives U V (fun _ => c) (fun _ => 0) (fun _ => 0) := by
  let : IsFiniteMeasure (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  refine l2_first_derivatives_of_sections hU hV (memLp_const c) (memLp_const 0) (memLp_const 0)
    ?_ ?_ ?_ ?_
  · exact fun _ => (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  · exact fun _ => Eventually.of_forall fun t => hasDerivWithinAt_const t _ c
  · exact fun _ => (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  · exact fun _ => Eventually.of_forall fun t => hasDerivWithinAt_const t _ c

end CauchyHorizon
