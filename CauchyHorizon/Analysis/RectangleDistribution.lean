import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Distributions induced by integrable functions on a finite rectangle. -/

open MeasureTheory Set
open scoped Distributions

namespace CauchyHorizon

def openRectangle (U V : ℝ) : TopologicalSpace.Opens (ℝ × ℝ) :=
  ⟨Ioo 0 U ×ˢ Ioo 0 V, isOpen_Ioo.prod isOpen_Ioo⟩

noncomputable def rectangleDistribution (U V : ℝ) (f : ℝ × ℝ → ℝ) :
    𝓓'(openRectangle U V, ℝ) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ)
    (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) f

theorem rectangleDistribution_apply {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {f : ℝ × ℝ → ℝ} (hf : IntegrableOn f (Icc 0 U ×ˢ Icc 0 V))
    (ψ : 𝓓(openRectangle U V, ℝ)) :
    rectangleDistribution U V f ψ =
      ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, f (u, v) * ψ (u, v) := by
  have hi : IntegrableOn (fun w => f w * ψ w) (Icc 0 U ×ˢ Icc 0 V) :=
    hf.mul_continuousOn ψ.continuous.continuousOn (isCompact_Icc.prod isCompact_Icc)
  change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ)
    (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) f ψ = _
  rw [TestFunction.integralAgainstBilinCLM_eq_integral
    (hf.locallyIntegrable.locallyIntegrableOn _)]
  change (∫ w in Icc 0 U ×ˢ Icc 0 V, ψ w * f w) = _
  simp_rw [mul_comm (ψ _) (f _)]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi]
  simp_rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hU,
    intervalIntegral.integral_of_le hV]

theorem rectangleDistribution_pairing {U V : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 U ×ˢ Icc 0 V)) (ψ : 𝓓(openRectangle U V, ℝ)) :
    Integrable (fun w => f w * ψ w) ∧
      rectangleDistribution U V f ψ = ∫ w, f w * ψ w := by
  have hs : Function.support (fun w => f w * ψ w) ⊆ Icc 0 U ×ˢ Icc 0 V := by
    intro w hw
    have hψ : ψ w ≠ 0 := fun h => hw (by change f w * ψ w = 0; rw [h, mul_zero])
    exact (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
      (ψ.tsupport_subset (subset_tsupport ψ hψ))
  have hi := hf.mul_continuousOn ψ.continuous.continuousOn (isCompact_Icc.prod isCompact_Icc)
  refine ⟨(integrableOn_iff_integrable_of_support_subset hs).1 hi, ?_⟩
  change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ)
    (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) f ψ = _
  rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
  change (∫ w in Icc 0 U ×ˢ Icc 0 V, ψ w * f w) = _
  simp_rw [mul_comm (ψ _) (f _)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro w hw
  by_contra hn
  exact hw (hs hn)

end CauchyHorizon
