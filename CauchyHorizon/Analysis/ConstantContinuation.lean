import CauchyHorizon.Analysis.PrimitiveContinuity

/-! A continuous endpoint and an integrable derivative permit constant continuation. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

theorem constant_continuation_absolutelyContinuous {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    {f g : ℝ → ℝ} (hc : ContinuousOn f (Icc a 0))
    (hd : ∀ x ∈ Ioo a 0, HasDerivAt f (g x) x)
    (hg : IntervalIntegrable g volume a 0) :
    AbsolutelyContinuousOnInterval (fun x => f (min x 0)) a b := by
  classical
  let F := fun x => f (min x 0)
  let G := (Ico a 0).indicator g
  have hi : Integrable G := by
    apply (integrable_indicator_iff measurableSet_Ico).2
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le ha).1 hg).mono_set Ico_subset_Icc_self
  have hcont : ContinuousOn F (Icc a b) := hc.comp (by fun_prop)
    (fun x hx => ⟨le_min hx.1 ha, min_le_right _ _⟩)
  have hder (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivWithinAt F (G x) (Ioi x) x := by
    by_cases hx0 : x < 0
    · have he : G x = g x := indicator_of_mem (show x ∈ Ico a 0 from ⟨hx.1.le, hx0⟩) g
      rw [he]
      apply ((hd x ⟨hx.1, hx0⟩).congr_of_eventuallyEq ?_).hasDerivWithinAt
      filter_upwards [eventually_lt_nhds hx0] with y hy
      exact congrArg f (min_eq_left hy.le)
    · have hx0 := le_of_not_gt hx0
      have he : G x = 0 := indicator_of_notMem (show x ∉ Ico a 0 from fun h => (not_lt_of_ge hx0) h.2) g
      rw [he]
      apply (hasDerivWithinAt_const x (Ioi x) (f 0)).congr (f₁ := F) _ (congrArg f (min_eq_right hx0))
      intro y hy
      exact congrArg f (min_eq_right (hx0.trans hy.le))
  have hprim (s : ℝ) (hs : s ∈ Icc a b) : (∫ x in a..s, G x) = F s - F a :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.1
      (hcont.mono (Icc_subset_Icc le_rfl hs.2))
      (fun x hx => hder x ⟨hx.1, hx.2.trans_le hs.2⟩) hi.intervalIntegrable
  apply absolutelyContinuous_of_dist_le
    (hi.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
      (a := a) (b := b) left_mem_uIcc) (K := 1) zero_le_one
  intro s hs t ht
  rw [uIcc_of_le (ha.trans hb)] at hs ht
  rw [hprim s hs, hprim t ht, one_mul, dist_sub_right]

end CauchyHorizon
