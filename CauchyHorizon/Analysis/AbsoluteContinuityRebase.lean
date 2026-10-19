import CauchyHorizon.Analysis.PrimitiveContinuity

/-! Restricting and translating an absolutely continuous scalar function preserves absolute continuity. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem absolutelyContinuous_rebase {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    {f : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => f (a + t)) 0 (c - a) := by
  have hsub : uIcc a c ⊆ uIcc a b := by
    rw [uIcc_of_le hac, uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc le_rfl hcb
  have hi : IntervalIntegrable (fun t => deriv f (a + t)) volume 0 (c - a) := by
    simpa only [sub_self] using (hf.mono hsub).intervalIntegrable_deriv.comp_add_left a
  have hp (s : ℝ) (hs : s ∈ Icc 0 (c - a)) :
      (∫ t in (0 : ℝ)..s, deriv f (a + t)) = f (a + s) - f a := by
    rw [intervalIntegral.integral_comp_add_left, add_zero]
    apply (hf.mono ?_).integral_deriv_eq_sub
    rw [uIcc_of_le (le_add_of_nonneg_right hs.1), uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc le_rfl (by linarith [hs.2])
  apply absolutelyContinuous_of_dist_le
    (hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc) (K := 1) zero_le_one
  intro s hs t ht
  rw [uIcc_of_le (sub_nonneg.2 hac)] at hs ht
  rw [hp s hs, hp t ht, one_mul, dist_sub_right]

end CauchyHorizon
