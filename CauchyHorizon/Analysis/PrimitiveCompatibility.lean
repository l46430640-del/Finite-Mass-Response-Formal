import CauchyHorizon.Analysis.IntervalOperators
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! Linear compatibility and derivatives of the two characteristic primitives. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {a b : ℝ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] in
theorem horizontalPrimitive_add (hab : a ≤ b) (f g : Lp E 2 (volume.restrict (Icc a b))) :
    horizontalPrimitive hab (f + g) = horizontalPrimitive hab f + horizontalPrimitive hab g := by
  ext t
  have hsub : Ioc a (t : ℝ) ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans t.property.2⟩
  have he := ae_mono (Measure.restrict_mono hsub le_rfl) (Lp.coeFn_add f g)
  change (∫ x in a..(t : ℝ), (f + g) x) = (∫ x in a..(t : ℝ), f x) + ∫ x in a..(t : ℝ), g x
  simp only [intervalIntegral.integral_of_le t.property.1]
  rw [integral_congr_ae he]
  have hf : IntegrableOn (fun x => f x) (Icc a b) := (Lp.memLp f).integrable (by norm_num)
  have hg : IntegrableOn (fun x => g x) (Icc a b) := (Lp.memLp g).integrable (by norm_num)
  exact integral_add (hf.mono_set hsub) (hg.mono_set hsub)

theorem horizontalPrimitive_compLp (hab : a ≤ b) (T : E →L[ℝ] F)
    (f : Lp E 2 (volume.restrict (Icc a b))) :
    horizontalPrimitive hab (T.compLpL 2 (volume.restrict (Icc a b)) f) =
      ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) T (horizontalPrimitive hab f) := by
  ext t
  have hsub : Ioc a (t : ℝ) ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans t.property.2⟩
  have he := ae_mono (Measure.restrict_mono hsub le_rfl) (T.coeFn_compLpL f)
  change (∫ x in a..(t : ℝ), T.compLpL 2 (volume.restrict (Icc a b)) f x) =
    T (∫ x in a..(t : ℝ), f x)
  simp only [intervalIntegral.integral_of_le t.property.1]
  rw [integral_congr_ae he]
  have hf : IntegrableOn (fun x => f x) (Icc a b) := (Lp.memLp f).integrable (by norm_num)
  exact T.integral_comp_comm (hf.mono_set hsub)

omit [CompleteSpace E] in
theorem horizontalPrimitive_intervalToLp (hab : a ≤ b) (f : C(Icc a b, E)) :
    horizontalPrimitive hab (intervalToLp hab 2 f) = continuousPrimitive hab f := by
  apply ContinuousMap.ext
  intro t
  have hsub : Ioc a (t : ℝ) ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans t.property.2⟩
  have he := ae_mono (Measure.restrict_mono hsub le_rfl) (intervalToLp_ae hab 2 f)
  change (∫ x in a..(t : ℝ), intervalToLp hab 2 f x) =
    ∫ x in a..(t : ℝ), intervalExtension hab f x
  simp only [intervalIntegral.integral_of_le t.property.1]
  exact integral_congr_ae he

theorem continuousPrimitive_comp (hab : a ≤ b) (T : E →L[ℝ] F) (f : C(Icc a b, E)) :
    continuousPrimitive hab (ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) T f) =
      ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) T (continuousPrimitive hab f) := by
  apply ContinuousMap.ext
  intro t
  change (∫ x in a..(t : ℝ), T (intervalExtension hab f x)) =
    T (∫ x in a..(t : ℝ), intervalExtension hab f x)
  exact T.intervalIntegral_comp_comm ((intervalExtension hab f).continuous.intervalIntegrable _ _)

theorem continuousPrimitive_hasDerivWithinAt (hab : a ≤ b) (f : C(Icc a b, E))
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (intervalExtension hab (continuousPrimitive hab f)) (f ⟨t, ht⟩) (Icc a b) t := by
  have hc := (intervalExtension hab f).continuous
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [intervalExtension_apply, projIcc_of_mem hab ht] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ ht
  intro x hx
  simp only [intervalExtension_apply, projIcc_of_mem hab hx]
  rfl

theorem horizontalPrimitive_ae_hasDerivWithinAt (hab : a ≤ b)
    (f : Lp E 2 (volume.restrict (Icc a b))) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivWithinAt (intervalExtension hab (horizontalPrimitive hab f)) (f t) (Icc a b) t := by
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards [(l2_intervalIntegrable hab f).ae_hasDerivAt_integral] with t ht hmem
  have hmem' : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hmem
  apply (ht hmem' a left_mem_uIcc).hasDerivWithinAt.congr_of_mem _ hmem
  intro x hx
  simp only [intervalExtension_apply, projIcc_of_mem hab hx]
  rfl

end CauchyHorizon
