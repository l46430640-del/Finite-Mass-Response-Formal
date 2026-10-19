import CauchyHorizon.Analysis.PrimitiveContinuity

/-! An absolutely continuous flux with a continuous density has pointwise positive-time derivatives. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem absolutelyContinuous_hasDerivWithinAt_of_continuous {U : ℝ} (hU : 0 ≤ U)
    {F G : ℝ → ℝ} (hF : AbsolutelyContinuousOnInterval F 0 U)
    (hG : ContinuousOn G (Ioi 0))
    (hd : ∀ᵐ t ∂volume.restrict (Icc 0 U), HasDerivWithinAt F (G t) (Icc 0 U) t)
    {u : ℝ} (hu : u ∈ Ioc 0 U) : HasDerivWithinAt F (G u) (Icc 0 U) u := by
  have he : deriv F =ᵐ[volume.restrict (Icc 0 U)] G := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc 0 U)).ae_ne 0, (volume.restrict (Icc 0 U)).ae_ne U] with t ht hm h0 htop
    exact (ht.hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne hm.1 h0.symm)
      (lt_of_le_of_ne hm.2 htop))).deriv
  have hsub (t : ℝ) (ht : t ∈ Icc 0 U) : uIcc (0 : ℝ) t ⊆ uIcc 0 U := by
    rw [uIcc_of_le ht.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl ht.2
  have hi : IntervalIntegrable G volume 0 U := hF.intervalIntegrable_deriv.congr_ae
    (ae_mono (Measure.restrict_mono (by rw [uIoc_of_le hU]; exact Ioc_subset_Icc_self) le_rfl) he)
  have hp (t : ℝ) (ht : t ∈ Icc 0 U) : (∫ s in (0 : ℝ)..t, G s) = F t - F 0 := by
    have hh := (hF.mono (hsub t ht)).integral_deriv_eq_sub
    rw [intervalIntegral.integral_of_le ht.1,
      integral_congr_ae (ae_mono (Measure.restrict_mono
        (show Ioc (0 : ℝ) t ⊆ Icc 0 U from fun _ hs => ⟨hs.1.le, hs.2.trans ht.2⟩) le_rfl) he),
      ← intervalIntegral.integral_of_le ht.1] at hh
    exact hh
  have hh := intervalIntegral.integral_hasDerivAt_right (hi.mono_set (hsub u ⟨hu.1.le, hu.2⟩))
    (hG.stronglyMeasurableAtFilter isOpen_Ioi u hu.1)
    (hG.continuousAt (isOpen_Ioi.mem_nhds hu.1))
  apply (hh.const_add (F 0)).hasDerivWithinAt.congr_of_mem (s := Icc 0 U) ?_ ⟨hu.1.le, hu.2⟩
  intro t ht
  linarith only [hp t ht]

end CauchyHorizon
