import CauchyHorizon.Analysis.PrimitiveCompatibility

/-! Restriction to a translated subinterval preserves the characteristic primitives. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {A a U : ℝ}

def intervalTranslate (ha : 0 ≤ a) (haU : a + U ≤ A) : C(Icc 0 U, Icc 0 A) where
  toFun t := ⟨a + t, add_nonneg ha t.property.1, (add_le_add_right t.property.2 a).trans haU⟩
  continuous_toFun := by fun_prop

@[simp] theorem intervalTranslate_zero (A : ℝ) :
    intervalTranslate (a := 0) (U := A) le_rfl (by simp) = ContinuousMap.id (Icc 0 A) := by
  apply ContinuousMap.ext
  intro t
  exact Subtype.ext (zero_add _)

theorem intervalTranslate_measure (a U : ℝ) :
    MeasurePreserving (fun t : ℝ => a + t) (volume.restrict (Icc 0 U))
      (volume.restrict (Icc a (a + U))) := by
  have hp : (fun t : ℝ => a + t) ⁻¹' Icc a (a + U) = Icc 0 U := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
  simpa only [hp] using (measurePreserving_add_left volume a).restrict_preimage
    (s := Icc a (a + U)) measurableSet_Icc

theorem intervalTranslate_ae (ha : 0 ≤ a) (haU : a + U ≤ A) {P : ℝ → Prop}
    (hP : ∀ᵐ t ∂volume.restrict (Icc 0 A), P t) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), P (a + t) := by
  have hs : Icc a (a + U) ⊆ Icc 0 A := fun _ ht => ⟨ha.trans ht.1, ht.2.trans haU⟩
  exact (intervalTranslate_measure a U).quasiMeasurePreserving.ae
    (ae_mono (Measure.restrict_mono hs le_rfl) hP)

variable {E : Type*} [NormedAddCommGroup E]

theorem intervalTranslate_memLp (ha : 0 ≤ a) (haU : a + U ≤ A)
    (f : Lp E 2 (volume.restrict (Icc 0 A))) :
    MemLp (fun t => f (a + t)) 2 (volume.restrict (Icc 0 U)) := by
  have hs : Icc a (a + U) ⊆ Icc 0 A := fun _ ht => ⟨ha.trans ht.1, ht.2.trans haU⟩
  exact ((Lp.memLp f).mono_measure (Measure.restrict_mono hs le_rfl)).comp_measurePreserving
    (intervalTranslate_measure a U)

noncomputable def intervalTranslateLp (ha : 0 ≤ a) (haU : a + U ≤ A)
    (f : Lp E 2 (volume.restrict (Icc 0 A))) : Lp E 2 (volume.restrict (Icc 0 U)) :=
  (intervalTranslate_memLp ha haU f).toLp (fun t => f (a + t))

theorem intervalTranslateLp_ae (ha : 0 ≤ a) (haU : a + U ≤ A)
    (f : Lp E 2 (volume.restrict (Icc 0 A))) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), intervalTranslateLp ha haU f t = f (a + t) :=
  (intervalTranslate_memLp ha haU f).coeFn_toLp

@[simp] theorem intervalTranslateLp_zero (f : Lp E 2 (volume.restrict (Icc 0 A))) :
    intervalTranslateLp (a := 0) (U := A) le_rfl (by simp) f = f := by
  apply Lp.ext
  filter_upwards [intervalTranslateLp_ae (a := 0) (U := A) le_rfl (by simp) f] with t ht
  simpa only [zero_add] using ht

theorem intervalTranslateLp_norm_le (ha : 0 ≤ a) (haU : a + U ≤ A)
    (f : Lp E 2 (volume.restrict (Icc 0 A))) : ‖intervalTranslateLp ha haU f‖ ≤ ‖f‖ := by
  have hs : Icc a (a + U) ⊆ Icc 0 A := fun _ ht => ⟨ha.trans ht.1, ht.2.trans haU⟩
  have hf := (Lp.memLp f).mono_measure (Measure.restrict_mono hs le_rfl)
  rw [intervalTranslateLp, Lp.norm_toLp, Lp.norm_def]
  rw [show (fun t => f (a + t)) = (fun t => f t) ∘ (fun t => a + t) from rfl,
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (intervalTranslate_measure a U)]
  exact ENNReal.toReal_mono (Lp.memLp f).2.ne (eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl))

variable [NormedSpace ℝ E]

theorem horizontalPrimitive_translate (hA : 0 ≤ A) (hU : 0 ≤ U)
    (ha : 0 ≤ a) (haU : a + U ≤ A) (f : Lp E 2 (volume.restrict (Icc 0 A))) (t : Icc 0 U) :
    horizontalPrimitive hU (intervalTranslateLp ha haU f) t =
      horizontalPrimitive hA f (intervalTranslate ha haU t) -
        horizontalPrimitive hA f (intervalTranslate ha haU ⟨0, le_rfl, hU⟩) := by
  have hs : Ioc 0 (t : ℝ) ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans t.property.2⟩
  have he : (fun s : ℝ => intervalTranslateLp ha haU f s) =ᵐ[volume.restrict (Ioc 0 (t : ℝ))]
      fun s => f (a + s) :=
    ae_mono (Measure.restrict_mono hs le_rfl) (intervalTranslateLp_ae ha haU f)
  have hi := l2_intervalIntegrable hA f
  change (∫ s in (0 : ℝ)..t, intervalTranslateLp ha haU f s) =
    (∫ s in (0 : ℝ)..(a + t), f s) - ∫ s in (0 : ℝ)..(a + 0), f s
  rw [intervalIntegral.integral_congr_ae_restrict (μ := volume)
    (f := fun s => intervalTranslateLp ha haU f s) (g := fun s => f (a + s))
    (by rw [uIoc_of_le t.property.1]; exact he)]
  rw [intervalIntegral.integral_comp_add_left, add_zero]
  symm
  apply intervalIntegral.integral_interval_sub_left
  · exact hi.mono_set (by
      rw [uIcc_of_le hA, uIcc_of_le (add_nonneg ha t.property.1)]
      exact Icc_subset_Icc le_rfl ((add_le_add_right t.property.2 a).trans haU))
  · exact hi.mono_set (by
      rw [uIcc_of_le hA, uIcc_of_le ha]
      exact Icc_subset_Icc le_rfl (by linarith))

theorem continuousPrimitive_translate (hA : 0 ≤ A) (hU : 0 ≤ U)
    (ha : 0 ≤ a) (haU : a + U ≤ A) (f : C(Icc 0 A, E)) (t : Icc 0 U) :
    continuousPrimitive hU (f.comp (intervalTranslate ha haU)) t =
      continuousPrimitive hA f (intervalTranslate ha haU t) -
        continuousPrimitive hA f (intervalTranslate ha haU ⟨0, le_rfl, hU⟩) := by
  change (∫ s in (0 : ℝ)..t, intervalExtension hU (f.comp (intervalTranslate ha haU)) s) =
    (∫ s in (0 : ℝ)..(a + t), intervalExtension hA f s) -
      ∫ s in (0 : ℝ)..(a + 0), intervalExtension hA f s
  have he : (∫ s in (0 : ℝ)..t, intervalExtension hU (f.comp (intervalTranslate ha haU)) s) =
      ∫ s in (0 : ℝ)..t, intervalExtension hA f (a + s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    have hsu : s ∈ Icc 0 U := ⟨hs.1, hs.2.trans t.property.2⟩
    have hsa : a + s ∈ Icc 0 A := ⟨add_nonneg ha hs.1, (add_le_add_right hsu.2 a).trans haU⟩
    simp only [intervalExtension_apply, projIcc_of_mem hU hsu, projIcc_of_mem hA hsa]
    rfl
  rw [he, intervalIntegral.integral_comp_add_left, add_zero]
  exact (intervalIntegral.integral_interval_sub_left
    ((intervalExtension hA f).continuous.intervalIntegrable _ _)
    ((intervalExtension hA f).continuous.intervalIntegrable _ _)).symm

end CauchyHorizon
