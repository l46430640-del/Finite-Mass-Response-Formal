import CauchyHorizon.Reduced.TransversePrimitive
import CauchyHorizon.Characteristic.TransverseScalarBoundary
import Mathlib.MeasureTheory.Measure.OpenPos

/-! An integrable mixed source gives the actual transverse log-lapse trace on positive-u intervals. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

def IsTransverseConformalTrace {U ε : ℝ} (hU : 0 ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (D : ℝ → C(Icc ε U, ℝ)) (Dh : C(Icc ε U, ℝ)) : Prop :=
  (∀ (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U),
    HasDerivWithinAt (fun x => intervalExtension hU (X T).1 x ⟨t, ht, htT⟩ 2)
      (D t u) (Icc 0 U) u) ∧
  Tendsto D atTop (𝓝 Dh) ∧
  Tendsto (fun w => D (χ w)) (𝓝[<] (0 : ℝ)) (𝓝 Dh) ∧
  ∃ T C : ℝ, 0 ≤ T ∧ 0 < C ∧ ∀ t, T ≤ t → ‖D t‖ ≤ C

set_option maxHeartbeats 1600000 in
theorem exists_transverse_conformal_boundary {U ε e Λ T₀ : ℝ}
    (hε : 0 < ε) (hεU : ε < U) (hT₀ : 0 ≤ T₀)
    (zIn : C(Icc 0 U, WaveVector))
    (vOut : (T : Ici (0 : ℝ)) → C(Icc 0 (T : ℝ), WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ T, IsWaveIntegral (hε.trans hεU).le T.property e Λ zIn (vOut T) uIn (X T))
    {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive (hε.trans hεU).le uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    {G : ℝ → ℝ} (hGc : Continuous G) (hGi : IntegrableOn G (Ici 0))
    (hGpos : ∀ t, 0 ≤ G t)
    (hbound : ∀ t (ht : 0 ≤ t), T₀ ≤ t →
      ∀ᵐ s ∂volume.restrict (Icc 0 U), s ∈ Icc ε U →
        |waveSource e Λ ((X ⟨t, ht⟩).1 (projIcc 0 U (hε.trans hεU).le s) ⟨t, ht, le_rfl⟩)
          ((X ⟨t, ht⟩).2.2 s ⟨t, ht, le_rfl⟩)
          ((X ⟨t, ht⟩).2.1 (projIcc 0 U (hε.trans hεU).le s) ⟨t, ht, le_rfl⟩) 2| ≤ G t)
    {χ : ℝ → ℝ} (hχ : Tendsto χ (𝓝[<] (0 : ℝ)) atTop) :
    ∃ D : ℝ → C(Icc ε U, ℝ), ∃ Dh : C(Icc ε U, ℝ),
      IsTransverseConformalTrace (hε.trans hεU).le X χ D Dh ∧
      ∀ t, T₀ ≤ t → ‖D t - Dh‖ ≤ ∫ s in Ioi t, G s := by
  have hU := hε.trans hεU
  choose d S hdc hSc hdae hSae hprim hder using
    fun T => (hX T).exists_continuous_transverse_primitive hzin hinu hF hif
  have hfield (A T : Ici (0 : ℝ)) (hAT : A ≤ T) (u : Icc 0 U) (v : Icc 0 (A : ℝ)) :
      (X A).1 u v = (X T).1 u ⟨v, v.property.1, v.property.2.trans hAT⟩ := by
    have he := congrArg (fun x : WaveState U (A : ℝ) => x.1 u v) (hcompat A T hAT)
    change (X T).1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hAT⟩ = (X A).1 u v at he
    simpa only [zero_add] using he.symm
  have hvel (A T : Ici (0 : ℝ)) (hAT : A ≤ T) (u : Icc 0 U) (v : Icc 0 (A : ℝ)) :
      (X A).2.1 u v = (X T).2.1 u ⟨v, v.property.1, v.property.2.trans hAT⟩ := by
    have he := congrArg (fun x : WaveState U (A : ℝ) => x.2.1 u v) (hcompat A T hAT)
    change (X T).2.1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hAT⟩ = (X A).2.1 u v at he
    simpa only [zero_add] using he.symm
  -- Uniqueness of actual horizontal derivatives fixes representatives at every positive u.
  have hcmp {A T : Ici (0 : ℝ)} (hAT : A ≤ T)
      {Y : WaveRectangle U A} {Z : WaveRectangle U T}
      {dA : ℝ → C(Icc 0 (A : ℝ), WaveVector)} {dT : ℝ → C(Icc 0 (T : ℝ), WaveVector)}
      (hA : ∀ u ∈ Ioc 0 U, HasDerivWithinAt (intervalExtension hU.le Y) (dA u) (Icc 0 U) u)
      (hT : ∀ u ∈ Ioc 0 U, HasDerivWithinAt (intervalExtension hU.le Z) (dT u) (Icc 0 U) u)
      (hYZ : ∀ u v, Y u v = Z u ⟨v, v.property.1, v.property.2.trans hAT⟩)
      (u : ℝ) (hu : u ∈ Ioc 0 U) (v : Icc 0 (A : ℝ)) :
      dA u v = dT u ⟨v, v.property.1, v.property.2.trans hAT⟩ := by
    let w : Icc 0 (T : ℝ) := ⟨v, v.property.1, v.property.2.trans hAT⟩
    have hdA := (ContinuousMap.evalCLM ℝ v).hasFDerivAt.comp_hasDerivWithinAt u (hA u hu)
    have hdT := (ContinuousMap.evalCLM ℝ w).hasFDerivAt.comp_hasDerivWithinAt u (hT u hu)
    have he : HasDerivWithinAt (fun s => intervalExtension hU.le Y s v) (dT u w) (Icc 0 U) u :=
      hdT.congr_of_mem (fun s _ => hYZ (projIcc 0 U hU.le s) v) ⟨hu.1.le, hu.2⟩
    exact (hdA.derivWithin (uniqueDiffOn_Icc hU u ⟨hu.1.le, hu.2⟩)).symm.trans
      (he.derivWithin (uniqueDiffOn_Icc hU u ⟨hu.1.le, hu.2⟩))
  have hdcompat (A T : Ici (0 : ℝ)) (hAT : A ≤ T) u (hu : u ∈ Ioc 0 U) v :=
    hcmp hAT (fun u hu => (hder A u hu).1) (fun u hu => (hder T u hu).1) (hfield A T hAT) u hu v
  have hScompat (A T : Ici (0 : ℝ)) (hAT : A ≤ T) u (hu : u ∈ Ioc 0 U) v :=
    hcmp hAT (fun u hu => (hder A u hu).2) (fun u hu => (hder T u hu).2) (hvel A T hAT) u hu v
  let row (T : Ici (0 : ℝ)) (v : Icc 0 (T : ℝ)) : C(Icc ε U, ℝ) :=
    ⟨fun u => d T u v 2, by
      have hc := (hdc T).comp_continuous continuous_subtype_val (fun u : Icc ε U => hε.trans_le u.property.1)
      exact (continuous_apply (2 : Fin 3)).comp ((continuous_eval_const v).comp hc)⟩
  let D := fun t => row ⟨max 0 t, show (0 : ℝ) ≤ max 0 t from le_max_left _ _⟩
    ⟨max 0 t, le_max_left _ _, le_rfl⟩
  have hfinite (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U) :
      D t u = d T u ⟨t, ht, htT⟩ 2 := by
    change d ⟨max 0 t, show (0 : ℝ) ≤ max 0 t from le_max_left _ _⟩ u
      ⟨max 0 t, le_max_left _ _, le_rfl⟩ 2 = _
    have he := congrArg (fun z : WaveVector => z 2)
      (hdcompat ⟨max 0 t, show (0 : ℝ) ≤ max 0 t from le_max_left _ _⟩ T (max_le T.property htT) u
        ⟨hε.trans_le u.property.1, u.property.2⟩ ⟨max 0 t, le_max_left _ _, le_rfl⟩)
    simpa only [max_eq_right ht] using he
  have hSb (t : ℝ) (ht : 0 ≤ t) (ht₀ : T₀ ≤ t) (u : Icc ε U) :
      |S ⟨t, ht⟩ u ⟨t, ht, le_rfl⟩ 2| ≤ G t := by
    let f := fun s : ℝ => |S ⟨t, ht⟩ s ⟨t, ht, le_rfl⟩ 2|
    have hc : ContinuousOn f (Icc ε U) := by
      have hh := (hSc ⟨t, ht⟩).mono (fun (s : ℝ) (hs : s ∈ Icc ε U) => hε.trans_le hs.1)
      exact ((continuous_apply (2 : Fin 3)).comp_continuousOn
        ((continuous_eval_const ⟨t, ht, le_rfl⟩).comp_continuousOn hh)).abs
    have hae : (fun s => min (f s) (G t)) =ᵐ[volume.restrict (Icc ε U)] f := by
      have hh : ∀ᵐ s ∂volume.restrict (Icc 0 U), s ∈ Icc ε U → f s ≤ G t := by
        filter_upwards [hSae ⟨t, ht⟩, rectangleSource_ae hU.le e Λ (X ⟨t, ht⟩) (hX ⟨t, ht⟩).choose,
          hbound t ht ht₀] with s hs hsrc hb
        intro hm
        dsimp only [f]
        rw [← hs, hsrc ⟨t, ht, le_rfl⟩]
        exact hb hm
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hε.le le_rfl) hh,
        ae_restrict_mem measurableSet_Icc] with s hs hm
      exact min_eq_left (hs hm)
    exact min_eq_left_iff.1
      (Measure.eqOn_Icc_of_ae_eq volume hεU.ne hae (hc.inf continuousOn_const) hc u.property)
  let Q (T : Ici (0 : ℝ)) (u : Icc ε U) (t : ℝ) := intervalExtension T.property (S T u) t 2
  have hQc (T : Ici (0 : ℝ)) (u : Icc ε U) : Continuous (Q T u) := by fun_prop
  have hQb (T : Ici (0 : ℝ)) (u : Icc ε U) {t : ℝ} (ht : T₀ ≤ t) (htT : t ≤ T) :
      ‖Q T u t‖ ≤ G t := by
    have ht0 := hT₀.trans ht
    have he := congrArg (fun z : WaveVector => z 2)
      (hScompat ⟨t, ht0⟩ T htT u ⟨hε.trans_le u.property.1, u.property.2⟩ ⟨t, ht0, le_rfl⟩)
    change ‖S T u (projIcc 0 (T : ℝ) T.property t) 2‖ ≤ G t
    rw [projIcc_of_mem T.property (show t ∈ Icc 0 (T : ℝ) from ⟨ht0, htT⟩), Real.norm_eq_abs, ← he]
    exact hSb t ht0 ht u
  have hinc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : Icc ε U) :
      D b u - D a u = ∫ t in a..b, Q ⟨b, ha.trans hab⟩ u t := by
    let T : Ici (0 : ℝ) := ⟨b, ha.trans hab⟩
    have hp (v : Icc 0 (T : ℝ)) : d T u v 2 = F u 2 + ∫ t in (0 : ℝ)..v, Q T u t := by
      rw [hprim T u]
      change F u 2 + (∫ t in (0 : ℝ)..v, intervalExtension T.property (S T u) t) 2 = _
      congr 1
      exact ((ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).intervalIntegral_comp_comm
        ((intervalExtension T.property (S T u)).continuous.intervalIntegrable 0 v)).symm
    rw [hfinite T b T.property le_rfl u, hfinite T a ha hab u, hp, hp]
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hQc T u).intervalIntegrable 0 a) ((hQc T u).intervalIntegrable a b)
    linarith only [hi]
  have htail (a : ℝ) (ha : T₀ ≤ a) (b : ℝ) (hab : a ≤ b) :
      dist (D a) (D b) ≤ ∫ t in Ioi a, G t := by
    have ha0 := hT₀.trans ha
    rw [dist_comm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (integral_nonneg hGpos)).2
    intro u
    rw [ContinuousMap.sub_apply, hinc ha0 hab u]
    calc
      _ ≤ ∫ t in a..b, G t := intervalIntegral.norm_integral_le_of_norm_le hab
        (Eventually.of_forall (fun t ht => hQb ⟨b, ha0.trans hab⟩ u (ha.trans ht.1.le) ht.2))
        (hGc.intervalIntegrable a b)
      _ ≤ ∫ t in Ioi a, G t := by
        rw [intervalIntegral.integral_of_le hab]
        exact setIntegral_mono_set (hGi.mono_set (fun _ ht => ha0.trans ht.le))
          (Eventually.of_forall hGpos) (Eventually.of_forall (fun _ ht => ht.1))
  obtain ⟨Dh, hDh, htailDh⟩ := exists_limit_of_tail_bound
    (tendsto_integral_Ioi_zero (f := G) (μ := volume) tendsto_id) htail
  refine ⟨D, Dh, ⟨?_, hDh, hDh.comp hχ, ?_⟩, ?_⟩
  · intro T t ht htT u
    let P : C(Icc 0 (T : ℝ), WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ ⟨t, ht, htT⟩)
    rw [hfinite T t ht htT u]
    exact P.hasFDerivAt.comp_hasDerivWithinAt (u : ℝ) (hder T u ⟨hε.trans_le u.property.1, u.property.2⟩).1
  · obtain ⟨T, hT⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hDh 1 (by norm_num))
    refine ⟨max 0 T, ‖Dh‖ + 1, le_max_left _ _, by positivity, fun t ht => ?_⟩
    have hb := (hT t ((le_max_right _ _).trans ht)).le
    rw [dist_eq_norm] at hb
    exact (norm_le_norm_sub_add (D t) Dh).trans (by linarith only [hb])
  · intro t ht
    simpa only [dist_eq_norm, id_eq] using htailDh t ht

end CauchyHorizon
