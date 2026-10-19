import CauchyHorizon.Analysis.PrimitiveContinuity

/-! Absolutely continuous derivatives satisfy integration by parts against boundary-vanishing tests. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

theorem integral_weak_derivative {a b : ℝ} (hab : a ≤ b) {f f' g g' : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfd : ∀ᵐ x ∂volume.restrict (Icc a b), HasDerivWithinAt f (f' x) (Icc a b) x)
    (hg : ContDiff ℝ 1 g) (hgd : ∀ x ∈ Icc a b, HasDerivWithinAt g (g' x) (Icc a b) x)
    (hga : g a = 0) (hgb : g b = 0) :
    IntervalIntegrable (fun x => f' x * g x) volume a b ∧
      (∫ x in a..b, f' x * g x) = -(∫ x in a..b, f x * g' x) := by
  have hgAC : AbsolutelyContinuousOnInterval g a b := hg.contDiffOn.absolutelyContinuousOnInterval
  have he : ∀ᵐ x ∂volume.restrict (Icc a b), deriv f x = f' x ∧ deriv g x = g' x := by
    filter_upwards [hfd, ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc a b)).ae_ne a, (volume.restrict (Icc a b)).ae_ne b]
      with x hd hx hxa hxb
    have hn := Icc_mem_nhds (lt_of_le_of_ne hx.1 hxa.symm) (lt_of_le_of_ne hx.2 hxb)
    exact ⟨(hd.hasDerivAt hn).deriv, ((hgd x hx).hasDerivAt hn).deriv⟩
  have hs : uIoc a b ⊆ Icc a b := by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self
  have hfa : (fun x => deriv f x * g x) =ᵐ[volume.restrict (uIoc a b)] fun x => f' x * g x := by
    filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) he] with x hx
    rw [hx.1]
  have hga' : (fun x => f x * deriv g x) =ᵐ[volume.restrict (uIoc a b)] fun x => f x * g' x := by
    filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) he] with x hx
    rw [hx.2]
  refine ⟨(hf.intervalIntegrable_deriv.mul_continuousOn hgAC.continuousOn).congr_ae hfa, ?_⟩
  have hi := hf.integral_mul_deriv_eq_deriv_mul hgAC
  rw [intervalIntegral.integral_congr_ae_restrict hfa,
    intervalIntegral.integral_congr_ae_restrict hga', hga, hgb, mul_zero, mul_zero, sub_self] at hi
  linarith only [hi]

end CauchyHorizon
