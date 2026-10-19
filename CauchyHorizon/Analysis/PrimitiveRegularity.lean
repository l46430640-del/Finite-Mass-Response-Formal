import CauchyHorizon.Analysis.PrimitiveCompatibility

/-! A continuous representative gives the derivative of an L2 primitive at positive points. -/

open Set MeasureTheory

namespace CauchyHorizon

theorem horizontalPrimitive_hasDerivWithinAt_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : ℝ} (hU : 0 ≤ U) (f : Lp E 2 (volume.restrict (Icc 0 U)))
    {F : ℝ → E} (hF : ContinuousOn F (Ioi 0))
    (he : f =ᵐ[volume.restrict (Icc 0 U)] F) {u : ℝ} (hu : u ∈ Ioc 0 U) :
    HasDerivWithinAt (intervalExtension hU (horizontalPrimitive hU f)) (F u) (Icc 0 U) u := by
  have hi : IntervalIntegrable F volume 0 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      (((Lp.memLp f).integrable (by norm_num)).congr he)
  have hiu := hi.mono_set (show uIcc (0 : ℝ) u ⊆ uIcc 0 U by
    rw [uIcc_of_le hu.1.le, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl hu.2)
  have hd := intervalIntegral.integral_hasDerivAt_right hiu
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hF u hu.1)
    (hF.continuousAt (isOpen_Ioi.mem_nhds hu.1))
  apply hd.hasDerivWithinAt.congr_of_mem (s := Icc 0 U) ?_ ⟨hu.1.le, hu.2⟩
  intro t ht
  simp only [intervalExtension_apply, projIcc_of_mem hU ht]
  change (∫ w in (0 : ℝ)..t, f w) = ∫ w in (0 : ℝ)..t, F w
  simp only [intervalIntegral.integral_of_le ht.1]
  exact integral_congr_ae (ae_mono (Measure.restrict_mono
    (show Ioc (0 : ℝ) t ⊆ Icc 0 U from fun w hw => ⟨hw.1.le, hw.2.trans ht.2⟩) le_rfl) he)

end CauchyHorizon
