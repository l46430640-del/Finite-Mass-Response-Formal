import CauchyHorizon.Analysis.PrimitiveCompatibility
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! The product rule in integral form for two real L2 primitives. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem l2_primitive_product {U : ℝ} (hU : 0 ≤ U)
    (f g : Lp ℝ 2 (volume.restrict (Icc 0 U))) (a b : ℝ) (t : Icc 0 U) :
    (a + horizontalPrimitive hU f t) * (b + horizontalPrimitive hU g t) = a * b +
      ∫ s in (0 : ℝ)..t, f s * (b + ∫ w in 0..s, g w) + (a + ∫ w in 0..s, f w) * g s := by
  let F : ℝ → ℝ := fun s => a + ∫ w in 0..s, f w
  let G : ℝ → ℝ := fun s => b + ∫ w in 0..s, g w
  have hF : AbsolutelyContinuousOnInterval F 0 U := by
    simpa only [AbsolutelyContinuousOnInterval, F, dist_add_left] using
      (l2_intervalIntegrable hU f).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hG : AbsolutelyContinuousOnInterval G 0 U := by
    simpa only [AbsolutelyContinuousOnInterval, G, dist_add_left] using
      (l2_intervalIntegrable hU g).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have he : deriv (F * G) =ᵐ[volume.restrict (Icc 0 U)] fun s => f s * G s + F s * g s := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [(l2_intervalIntegrable hU f).ae_hasDerivAt_integral,
      (l2_intervalIntegrable hU g).ae_hasDerivAt_integral] with s hf hg hs
    have hs' : s ∈ uIcc (0 : ℝ) U := by simpa only [uIcc_of_le hU] using hs
    exact (((hf hs' 0 left_mem_uIcc).const_add a).mul ((hg hs' 0 left_mem_uIcc).const_add b)).deriv
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le t.property.1, uIcc_of_le hU]
    exact fun _ hs => ⟨hs.1, hs.2.trans t.property.2⟩
  have hp := ((hF.mul hG).mono hsub).integral_deriv_eq_sub
  have hs : Ioc (0 : ℝ) t ⊆ Icc (0 : ℝ) U := fun _ hs => ⟨hs.1.le, hs.2.trans t.property.2⟩
  rw [intervalIntegral.integral_of_le t.property.1, integral_congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) he)] at hp
  simp only [Pi.mul_apply] at hp
  have hF0 : F 0 = a := by simp [F]
  have hG0 : G 0 = b := by simp [G]
  rw [hF0, hG0] at hp
  change F t * G t = a * b + ∫ s in (0 : ℝ)..t, f s * G s + F s * g s
  rw [intervalIntegral.integral_of_le t.property.1]
  linarith only [hp]

end CauchyHorizon
