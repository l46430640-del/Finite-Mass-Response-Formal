import CauchyHorizon.Analysis.IntervalTranslate

/-! Adjacent continuous sections and their L2-valued characteristic primitives. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {V W : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def intervalSpliceLeft (hV : 0 ≤ V) :
    C(Icc 0 V, E) →L[ℝ] C(Icc 0 (V + W), E) :=
  ContinuousMap.compCLM ℝ E ⟨fun t => projIcc 0 V hV t, by fun_prop⟩

noncomputable def intervalSpliceRight (V : ℝ) (hW : 0 ≤ W) :
    C(Icc 0 W, E) →L[ℝ] C(Icc 0 (V + W), E) :=
  ContinuousMap.compCLM ℝ E ⟨fun t : Icc 0 (V + W) => projIcc 0 W hW ((t : ℝ) - V), by fun_prop⟩ -
    (ContinuousLinearMap.const ℝ (Icc 0 (V + W)) : E →L[ℝ] C(Icc 0 (V + W), E)).comp
      (ContinuousMap.evalCLM ℝ (⟨0, le_rfl, hW⟩ : Icc 0 W))

noncomputable def intervalSplice (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f : C(Icc 0 V, E)) (g : C(Icc 0 W, E)) : C(Icc 0 (V + W), E) :=
  intervalSpliceLeft hV f + intervalSpliceRight V hW g

theorem intervalSplice_left (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f : C(Icc 0 V, E)) (g : C(Icc 0 W, E)) (t : Icc 0 V) :
    intervalSplice hV hW f g (intervalTranslate (a := 0) le_rfl (by linarith) t) = f t := by
  change f (projIcc 0 V hV (0 + t)) + (g (projIcc 0 W hW (0 + t - V)) - g ⟨0, le_rfl, hW⟩) = f t
  rw [zero_add, projIcc_val, projIcc_of_le_left hW (sub_nonpos.2 t.property.2), sub_self, add_zero]

theorem intervalSplice_right (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f : C(Icc 0 V, E)) (g : C(Icc 0 W, E)) (t : Icc 0 W) :
    intervalSplice hV hW f g (intervalTranslate hV le_rfl t) =
      f ⟨V, hV, le_rfl⟩ + g t - g ⟨0, le_rfl, hW⟩ := by
  change f (projIcc 0 V hV (V + t)) + (g (projIcc 0 W hW (V + t - V)) - g ⟨0, le_rfl, hW⟩) = _
  rw [projIcc_of_right_le hV (by linarith [t.property.1]), add_sub_cancel_left, projIcc_val]
  abel

theorem intervalSplice_right_of_match (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f : C(Icc 0 V, E)) (g : C(Icc 0 W, E))
    (hm : f ⟨V, hV, le_rfl⟩ = g ⟨0, le_rfl, hW⟩) (t : Icc 0 W) :
    intervalSplice hV hW f g (intervalTranslate hV le_rfl t) = g t := by
  rw [intervalSplice_right, hm]
  abel

omit [NormedSpace ℝ E] in
theorem continuousMap_ext_adjacent (hV : 0 ≤ V) (hW : 0 ≤ W)
    {f g : C(Icc 0 (V + W), E)}
    (hl : ∀ t : Icc 0 V, f (intervalTranslate (a := 0) le_rfl (by linarith) t) =
      g (intervalTranslate (a := 0) le_rfl (by linarith) t))
    (hr : ∀ t : Icc 0 W, f (intervalTranslate hV le_rfl t) = g (intervalTranslate hV le_rfl t)) : f = g := by
  apply ContinuousMap.ext
  intro t
  by_cases ht : (t : ℝ) ≤ V
  · let s : Icc 0 V := ⟨t, t.property.1, ht⟩
    have he : intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V + W by linarith) s = t :=
      Subtype.ext (by simp [intervalTranslate, s])
    simpa only [he] using hl s
  · let s : Icc 0 W := ⟨t - V, by linarith, by linarith [t.property.2]⟩
    have he : intervalTranslate hV (le_refl (V + W)) s = t := Subtype.ext (by dsimp [intervalTranslate, s]; ring)
    simpa only [he] using hr s

theorem intervalSplice_add (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f f' : C(Icc 0 V, E)) (g g' : C(Icc 0 W, E)) :
    intervalSplice hV hW (f + f') (g + g') = intervalSplice hV hW f g + intervalSplice hV hW f' g' := by
  unfold intervalSplice
  rw [map_add, map_add]
  abel

theorem intervalSplice_const (hV : 0 ≤ V) (hW : 0 ≤ W) (c d : E) :
    intervalSplice hV hW (ContinuousMap.const _ c) (ContinuousMap.const _ d) = ContinuousMap.const _ c := by
  ext t
  change c + (d - d) = c
  abel

theorem continuousPrimitive_splice (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f : C(Icc 0 V, E)) (g : C(Icc 0 W, E))
    (hm : f ⟨V, hV, le_rfl⟩ = g ⟨0, le_rfl, hW⟩) :
    continuousPrimitive (add_nonneg hV hW) (intervalSplice hV hW f g) =
      intervalSplice hV hW (continuousPrimitive hV f) (continuousPrimitive hW g) := by
  let F := intervalSplice hV hW f g
  have hl : F.comp (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V + W by linarith)) = f :=
    ContinuousMap.ext (intervalSplice_left hV hW f g)
  have hr : F.comp (intervalTranslate hV (le_refl (V + W))) = g :=
    ContinuousMap.ext (intervalSplice_right_of_match hV hW f g hm)
  have hp (t : Icc 0 V) : continuousPrimitive (add_nonneg hV hW) F
      (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V + W by linarith) t) = continuousPrimitive hV f t := by
    have he := continuousPrimitive_translate (add_nonneg hV hW) hV (a := 0) le_rfl (by linarith) F t
    rw [hl] at he
    have hz : continuousPrimitive (add_nonneg hV hW) F
        (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V + W by linarith) ⟨0, le_rfl, hV⟩) = 0 := by
      change (∫ s in (0 : ℝ)..(0 + 0), intervalExtension (add_nonneg hV hW) F s) = 0
      simp
    rw [hz, sub_zero] at he
    exact he.symm
  apply continuousMap_ext_adjacent hV hW
  · intro t
    rw [intervalSplice_left]
    exact hp t
  · intro t
    have he := continuousPrimitive_translate (add_nonneg hV hW) hW hV (le_refl (V + W)) F t
    rw [hr] at he
    have hb : intervalTranslate hV (le_refl (V + W)) (⟨0, le_rfl, hW⟩ : Icc 0 W) =
        intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V + W by linarith) ⟨V, hV, le_rfl⟩ :=
      Subtype.ext (by simp [intervalTranslate])
    rw [hb, hp] at he
    rw [intervalSplice_right]
    have hz : continuousPrimitive hW g ⟨0, le_rfl, hW⟩ = 0 := by
      change (∫ s in (0 : ℝ)..0, intervalExtension hW g s) = 0
      simp
    rw [hz, sub_zero]
    exact (eq_sub_iff_add_eq.mp he).symm.trans (add_comm _ _)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

noncomputable def intervalSpliceLp (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f : Lp C(Icc 0 V, E) 2 μ) (g : Lp C(Icc 0 W, E) 2 μ) : Lp C(Icc 0 (V + W), E) 2 μ :=
  (intervalSpliceLeft hV).compLpL 2 μ f + (intervalSpliceRight V hW).compLpL 2 μ g

theorem intervalSpliceLp_ae (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f : Lp C(Icc 0 V, E) 2 μ) (g : Lp C(Icc 0 W, E) 2 μ) :
    ∀ᵐ u ∂μ, intervalSpliceLp hV hW f g u = intervalSplice hV hW (f u) (g u) := by
  filter_upwards [Lp.coeFn_add ((intervalSpliceLeft hV).compLpL 2 μ f) ((intervalSpliceRight V hW).compLpL 2 μ g),
    (intervalSpliceLeft (W := W) hV).coeFn_compLpL f, (intervalSpliceRight V hW).coeFn_compLpL g] with u hu hf hg
  change intervalSpliceLp hV hW f g u = _ at hu
  rw [hu, Pi.add_apply, hf, hg]
  rfl

theorem horizontalPrimitive_splice [CompleteSpace E] {U : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f : Lp C(Icc 0 V, E) 2 (volume.restrict (Icc 0 U)))
    (g : Lp C(Icc 0 W, E) 2 (volume.restrict (Icc 0 U))) (u : Icc 0 U) :
    horizontalPrimitive hU (intervalSpliceLp hV hW f g) u =
      intervalSplice hV hW (horizontalPrimitive hU f u) (horizontalPrimitive hU g u) := by
  rw [intervalSpliceLp, horizontalPrimitive_add, horizontalPrimitive_compLp, horizontalPrimitive_compLp]
  rfl

theorem verticalPrimitive_splice (hV : 0 ≤ V) (hW : 0 ≤ W)
    (f : Lp C(Icc 0 V, E) 2 μ) (g : Lp C(Icc 0 W, E) 2 μ)
    (hm : ∀ᵐ u ∂μ, f u ⟨V, hV, le_rfl⟩ = g u ⟨0, le_rfl, hW⟩) :
    verticalPrimitive (add_nonneg hV hW) (intervalSpliceLp hV hW f g) =
      intervalSpliceLp hV hW (verticalPrimitive hV f) (verticalPrimitive hW g) := by
  apply Lp.ext
  filter_upwards [verticalPrimitive_ae (add_nonneg hV hW) (intervalSpliceLp hV hW f g),
    intervalSpliceLp_ae hV hW f g, intervalSpliceLp_ae hV hW (verticalPrimitive hV f) (verticalPrimitive hW g),
    verticalPrimitive_ae hV f, verticalPrimitive_ae hW g, hm] with u hu hs hp hf hg hm
  rw [hu, hs, hp, hf, hg]
  exact continuousPrimitive_splice hV hW _ _ hm

end CauchyHorizon
