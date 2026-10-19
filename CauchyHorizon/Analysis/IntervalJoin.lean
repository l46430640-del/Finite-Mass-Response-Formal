import CauchyHorizon.Analysis.IntervalSplice

/-! Concatenating L2 data changes the interval measure and requires no endpoint values. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem intervalUntranslate_measure (U W : ℝ) :
    MeasurePreserving (fun t : ℝ => t - U) (volume.restrict (Icc U (U + W)))
      (volume.restrict (Icc 0 W)) := by
  have hp : (fun t : ℝ => -U + t) ⁻¹' Icc 0 W = Icc U (U + W) := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
  have hm := (measurePreserving_add_left volume (-U)).restrict_preimage (s := Icc 0 W) measurableSet_Icc
  rw [hp] at hm
  simpa only [neg_add_eq_sub] using hm

theorem intervalJoin_ae {U W : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W) {P : ℝ → Prop}
    (hl : ∀ᵐ t ∂volume.restrict (Icc 0 U), P t)
    (hr : ∀ᵐ t ∂volume.restrict (Icc 0 W), P (U + t)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 (U + W)), P t := by
  have hh := (intervalUntranslate_measure U W).quasiMeasurePreserving.ae hr
  simp only [add_sub_cancel] at hh
  rw [← Icc_union_Icc_eq_Icc hU (by linarith : U ≤ U + W), ae_restrict_union_iff]
  exact ⟨hl, hh⟩

variable {U W : ℝ} {E : Type*} [NormedAddCommGroup E]

theorem intervalJoin_memLp (hW : 0 ≤ W)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp E 2 (volume.restrict (Icc 0 W))) :
    MemLp ((Iic U).piecewise (fun t => f t) (fun t => g (t - U))) 2
      (volume.restrict (Icc 0 (U + W))) := by
  classical
  apply MemLp.piecewise measurableSet_Iic
  · have hs : Iic U ∩ Icc 0 (U + W) = Icc 0 U := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · intro ht
        exact ⟨ht.2.1, ht.1⟩
      · intro ht
        exact ⟨ht.2, ht.1, by linarith [ht.2]⟩
    rw [Measure.restrict_restrict measurableSet_Iic, hs]
    exact Lp.memLp f
  · have hg := (Lp.memLp g).comp_measurePreserving (intervalUntranslate_measure U W)
    rw [Measure.restrict_restrict measurableSet_Iic.compl]
    exact hg.mono_measure (Measure.restrict_mono (by
      intro t ht
      simp only [mem_inter_iff, mem_compl_iff, mem_Iic, mem_Icc] at ht
      exact ⟨(not_le.mp ht.1).le, ht.2.2⟩) le_rfl)

noncomputable def intervalJoinLp (hW : 0 ≤ W)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp E 2 (volume.restrict (Icc 0 W))) :
    Lp E 2 (volume.restrict (Icc 0 (U + W))) :=
  (intervalJoin_memLp hW f g).toLp ((Iic U).piecewise (fun t => f t) (fun t => g (t - U)))

theorem intervalJoinLp_left (hW : 0 ≤ W)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp E 2 (volume.restrict (Icc 0 W))) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), intervalJoinLp hW f g t = f t := by
  have he := (intervalJoin_memLp hW f g).coeFn_toLp
  have hs : Icc 0 U ⊆ Icc 0 (U + W) := Icc_subset_Icc le_rfl (by linarith)
  filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) he, ae_restrict_mem measurableSet_Icc] with t ht hm
  change intervalJoinLp hW f g t = _ at ht
  simpa only [piecewise, mem_Iic, if_pos hm.2] using ht

theorem intervalJoinLp_right (hU : 0 ≤ U) (hW : 0 ≤ W)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp E 2 (volume.restrict (Icc 0 W))) :
    ∀ᵐ t ∂volume.restrict (Icc 0 W), intervalJoinLp hW f g (U + t) = g t := by
  have he := intervalTranslate_ae hU (le_refl (U + W)) (intervalJoin_memLp hW f g).coeFn_toLp
  filter_upwards [he, ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc (0 : ℝ) W)).ae_ne 0] with t ht hm hn
  have ht0 : 0 < t := lt_of_le_of_ne hm.1 (Ne.symm hn)
  change intervalJoinLp hW f g (U + t) = _ at ht
  simpa only [piecewise, mem_Iic, if_neg (show ¬ U + t ≤ U by linarith),
    add_sub_cancel_left] using ht

theorem intervalJoinLp_restrict_left (hW : 0 ≤ W)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp E 2 (volume.restrict (Icc 0 W))) :
    intervalTranslateLp (a := 0) (U := U) le_rfl (by linarith) (intervalJoinLp hW f g) = f := by
  apply Lp.ext
  filter_upwards [intervalTranslateLp_ae (a := 0) (U := U) le_rfl (by linarith) (intervalJoinLp hW f g),
    intervalJoinLp_left hW f g] with t ht hf
  simpa only [zero_add, hf] using ht

theorem intervalJoinLp_restrict_right (hU : 0 ≤ U) (hW : 0 ≤ W)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp E 2 (volume.restrict (Icc 0 W))) :
    intervalTranslateLp hU (le_refl (U + W)) (intervalJoinLp hW f g) = g := by
  apply Lp.ext
  filter_upwards [intervalTranslateLp_ae hU (le_refl (U + W)) (intervalJoinLp hW f g),
    intervalJoinLp_right hU hW f g] with t ht hg
  exact ht.trans hg

theorem intervalJoinLp_add (hU : 0 ≤ U) (hW : 0 ≤ W)
    (f f' : Lp E 2 (volume.restrict (Icc 0 U))) (g g' : Lp E 2 (volume.restrict (Icc 0 W))) :
    intervalJoinLp hW (f + f') (g + g') = intervalJoinLp hW f g + intervalJoinLp hW f' g' := by
  apply Lp.ext
  apply intervalJoin_ae hU hW
  · have hs : Icc 0 U ⊆ Icc 0 (U + W) := Icc_subset_Icc le_rfl (by linarith)
    filter_upwards [intervalJoinLp_left hW (f + f') (g + g'), intervalJoinLp_left hW f g,
      intervalJoinLp_left hW f' g', Lp.coeFn_add f f', ae_mono (Measure.restrict_mono hs le_rfl)
        (Lp.coeFn_add (intervalJoinLp hW f g) (intervalJoinLp hW f' g'))] with t hj hf hg ha hb
    rw [hj, ha, hb]
    simp only [Pi.add_apply, hf, hg]
  · filter_upwards [intervalJoinLp_right hU hW (f + f') (g + g'), intervalJoinLp_right hU hW f g,
      intervalJoinLp_right hU hW f' g', Lp.coeFn_add g g', intervalTranslate_ae hU (le_refl (U + W))
        (Lp.coeFn_add (intervalJoinLp hW f g) (intervalJoinLp hW f' g'))] with t hj hf hg ha hb
    rw [hj, ha, hb]
    simp only [Pi.add_apply, hf, hg]

variable [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem intervalSplice_comp (hU : 0 ≤ U) (hW : 0 ≤ W) (T : E →L[ℝ] F)
    (f : C(Icc 0 U, E)) (g : C(Icc 0 W, E)) :
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 (U + W)) T (intervalSplice hU hW f g) =
      intervalSplice hU hW (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) T f)
        (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 W) T g) := by
  apply ContinuousMap.ext
  intro t
  change T (f (projIcc 0 U hU t) + (g (projIcc 0 W hW (t - U)) - g ⟨0, le_rfl, hW⟩)) =
    T (f (projIcc 0 U hU t)) + (T (g (projIcc 0 W hW (t - U))) - T (g ⟨0, le_rfl, hW⟩))
  rw [map_add, map_sub]

theorem intervalJoinLp_comp (hU : 0 ≤ U) (hW : 0 ≤ W) (T : E →L[ℝ] F)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp E 2 (volume.restrict (Icc 0 W))) :
    T.compLpL 2 (volume.restrict (Icc 0 (U + W))) (intervalJoinLp hW f g) =
      intervalJoinLp hW (T.compLpL 2 (volume.restrict (Icc 0 U)) f)
        (T.compLpL 2 (volume.restrict (Icc 0 W)) g) := by
  apply Lp.ext
  apply intervalJoin_ae hU hW
  · have hs : Icc 0 U ⊆ Icc 0 (U + W) := Icc_subset_Icc le_rfl (by linarith)
    filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) (T.coeFn_compLpL (intervalJoinLp hW f g)),
      intervalJoinLp_left hW f g, T.coeFn_compLpL f,
      intervalJoinLp_left hW (T.compLpL 2 _ f) (T.compLpL 2 _ g)] with t ht hj hf hg
    rw [ht, hj, hg, hf]
  · filter_upwards [intervalTranslate_ae hU (le_refl (U + W)) (T.coeFn_compLpL (intervalJoinLp hW f g)),
      intervalJoinLp_right hU hW f g, T.coeFn_compLpL g,
      intervalJoinLp_right hU hW (T.compLpL 2 _ f) (T.compLpL 2 _ g)] with t ht hj hf hg
    rw [ht, hj, hg, hf]

theorem horizontalPrimitive_join (hU : 0 ≤ U) (hW : 0 ≤ W)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp E 2 (volume.restrict (Icc 0 W))) :
    horizontalPrimitive (add_nonneg hU hW) (intervalJoinLp hW f g) =
      intervalSplice hU hW (horizontalPrimitive hU f) (horizontalPrimitive hW g) := by
  let F := intervalJoinLp hW f g
  have hl (t : Icc 0 U) : horizontalPrimitive (add_nonneg hU hW) F
      (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U + W by linarith) t) = horizontalPrimitive hU f t := by
    have hh := horizontalPrimitive_translate (add_nonneg hU hW) hU (a := 0) le_rfl (by linarith) F t
    rw [intervalJoinLp_restrict_left] at hh
    have hz : horizontalPrimitive (add_nonneg hU hW) F
        (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U + W by linarith) ⟨0, le_rfl, hU⟩) = 0 := by
      change (∫ s in (0 : ℝ)..(0 + 0), F s) = 0
      simp
    rw [hz, sub_zero] at hh
    exact hh.symm
  apply continuousMap_ext_adjacent hU hW
  · intro t
    rw [intervalSplice_left]
    exact hl t
  · intro t
    have hh := horizontalPrimitive_translate (add_nonneg hU hW) hW hU (le_refl (U + W)) F t
    rw [intervalJoinLp_restrict_right] at hh
    have hb : intervalTranslate hU (le_refl (U + W)) (⟨0, le_rfl, hW⟩ : Icc 0 W) =
        intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U + W by linarith) ⟨U, hU, le_rfl⟩ :=
      Subtype.ext (by simp [intervalTranslate])
    rw [hb, hl] at hh
    rw [intervalSplice_right]
    have hz : horizontalPrimitive hW g ⟨0, le_rfl, hW⟩ = 0 := by
      change (∫ s in (0 : ℝ)..0, g s) = 0
      simp
    rw [hz, sub_zero]
    exact (eq_sub_iff_add_eq.mp hh).symm.trans (add_comm _ _)

end CauchyHorizon
