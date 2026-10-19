import CauchyHorizon.Reduced.IntegralRegularity
import CauchyHorizon.Analysis.IntervalTranslate

/-! Actual integral solutions on translated subrectangles, with their induced data. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {A B a b U V : ℝ}

noncomputable def rectangleTranslate (ha : 0 ≤ a) (haU : a + U ≤ A)
    (hb : 0 ≤ b) (hbV : b + V ≤ B) (z : WaveRectangle A B) : WaveRectangle U V :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
    (ContinuousMap.compCLM ℝ WaveVector (intervalTranslate hb hbV))
    (z.comp (intervalTranslate ha haU))

noncomputable def transverseTranslate (ha : 0 ≤ a) (haU : a + U ≤ A)
    (hb : 0 ≤ b) (hbV : b + V ≤ B) (d : WaveTransverse A B) : WaveTransverse U V :=
  (ContinuousMap.compCLM ℝ WaveVector (intervalTranslate hb hbV)).compLpL 2
    (volume.restrict (Icc 0 U)) (intervalTranslateLp ha haU d)

noncomputable def waveTranslate (ha : 0 ≤ a) (haU : a + U ≤ A)
    (hb : 0 ≤ b) (hbV : b + V ≤ B) (x : WaveState A B) : WaveState U V :=
  (rectangleTranslate ha haU hb hbV x.1, rectangleTranslate ha haU hb hbV x.2.1,
    transverseTranslate ha haU hb hbV x.2.2)

theorem transverseTranslate_ae (ha : 0 ≤ a) (haU : a + U ≤ A)
    (hb : 0 ≤ b) (hbV : b + V ≤ B) (d : WaveTransverse A B) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U),
      transverseTranslate ha haU hb hbV d u = (d (a + u)).comp (intervalTranslate hb hbV) := by
  filter_upwards [(ContinuousMap.compCLM ℝ WaveVector (intervalTranslate hb hbV)).coeFn_compLpL
    (intervalTranslateLp ha haU d), intervalTranslateLp_ae ha haU d] with u hu hd
  change transverseTranslate ha haU hb hbV d u = _ at hu
  rw [hu, hd]
  rfl

theorem rectangleTranslate_norm_le (ha : 0 ≤ a) (haU : a + U ≤ A)
    (hb : 0 ≤ b) (hbV : b + V ≤ B) (z : WaveRectangle A B) :
    ‖rectangleTranslate ha haU hb hbV z‖ ≤ ‖z‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg z)).2
  intro u
  apply (ContinuousMap.norm_le _ (norm_nonneg z)).2
  intro v
  exact ((z (intervalTranslate ha haU u)).norm_coe_le_norm (intervalTranslate hb hbV v)).trans
    (z.norm_coe_le_norm _)

theorem transverseTranslate_norm_le (ha : 0 ≤ a) (haU : a + U ≤ A)
    (hb : 0 ≤ b) (hbV : b + V ≤ B) (d : WaveTransverse A B) :
    ‖transverseTranslate ha haU hb hbV d‖ ≤ ‖d‖ := by
  let T := ContinuousMap.compCLM ℝ WaveVector (intervalTranslate hb hbV)
  have hT : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one (fun f => by
    simpa only [one_mul] using (ContinuousMap.norm_le (T f) (norm_nonneg f)).2
      (fun v => f.norm_coe_le_norm (intervalTranslate hb hbV v)))
  exact (T.norm_compLp_le (intervalTranslateLp ha haU d)).trans
    ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans (by
      simpa only [one_mul] using intervalTranslateLp_norm_le ha haU d))

theorem waveTranslate_norm_le (ha : 0 ≤ a) (haU : a + U ≤ A)
    (hb : 0 ≤ b) (hbV : b + V ≤ B) (x : WaveState A B) :
    ‖waveTranslate ha haU hb hbV x‖ ≤ ‖x‖ := by
  apply norm_prod_le_iff.2
  refine ⟨(rectangleTranslate_norm_le ha haU hb hbV x.1).trans (norm_fst_le x), norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact (rectangleTranslate_norm_le ha haU hb hbV x.2.1).trans ((norm_fst_le x.2).trans (norm_snd_le x))
  · exact (transverseTranslate_norm_le ha haU hb hbV x.2.2).trans ((norm_snd_le x.2).trans (norm_snd_le x))

theorem wave_trace_norm_le (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V) :
    let v₀ : Icc 0 V := ⟨0, le_rfl, hV⟩
    ‖ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (ContinuousMap.evalCLM ℝ v₀) x.1‖ ≤ ‖x‖ ∧
      ‖x.2.1 ⟨0, le_rfl, hU⟩‖ ≤ ‖x‖ ∧
      ‖(ContinuousMap.evalCLM ℝ v₀).compLpL 2 (volume.restrict (Icc 0 U)) x.2.2‖ ≤ ‖x‖ := by
  let v₀ : Icc 0 V := ⟨0, le_rfl, hV⟩
  let T : C(Icc 0 V, WaveVector) →L[ℝ] WaveVector := ContinuousMap.evalCLM ℝ v₀
  have hT : ‖T‖ ≤ 1 := T.opNorm_le_bound zero_le_one (fun f => by
    change ‖f v₀‖ ≤ 1 * ‖f‖
    rw [one_mul]
    exact f.norm_coe_le_norm v₀)
  refine ⟨?_, (x.2.1.norm_coe_le_norm _).trans ((norm_fst_le x.2).trans (norm_snd_le x)), ?_⟩
  · apply (ContinuousMap.norm_le _ (norm_nonneg x)).2
    intro u
    exact ((x.1 u).norm_coe_le_norm v₀).trans ((x.1.norm_coe_le_norm u).trans (norm_fst_le x))
  · exact (T.norm_compLp_le x.2.2).trans ((mul_le_mul_of_nonneg_right hT (norm_nonneg _)).trans
      (by simpa only [one_mul] using (norm_snd_le x.2).trans (norm_snd_le x)))

theorem rectangleSource_translate (hA : 0 ≤ A) (hU : 0 ≤ U)
    (ha : 0 ≤ a) (haU : a + U ≤ A) (hb : 0 ≤ b) (hbV : b + V ≤ B)
    (e Λ : ℝ) (x : WaveState A B) (hr : ∀ u v, x.1 u v 0 ≠ 0) :
    rectangleSource hU e Λ (waveTranslate ha haU hb hbV x)
      (fun u v => hr (intervalTranslate ha haU u) (intervalTranslate hb hbV v)) =
      transverseTranslate ha haU hb hbV (rectangleSource hA e Λ x hr) := by
  apply Lp.ext
  filter_upwards [rectangleSource_ae hU e Λ (waveTranslate ha haU hb hbV x)
      (fun u v => hr (intervalTranslate ha haU u) (intervalTranslate hb hbV v)),
    transverseTranslate_ae ha haU hb hbV (rectangleSource hA e Λ x hr),
    transverseTranslate_ae ha haU hb hbV x.2.2,
    intervalTranslate_ae ha haU (rectangleSource_ae hA e Λ x hr),
    ae_restrict_mem measurableSet_Icc] with u hu hF hd hx hum
  apply ContinuousMap.ext
  intro v
  rw [hu v, hF]
  change waveSource e Λ (x.1 (intervalTranslate ha haU (projIcc 0 U hU u)) (intervalTranslate hb hbV v))
    (transverseTranslate ha haU hb hbV x.2.2 u v)
    (x.2.1 (intervalTranslate ha haU (projIcc 0 U hU u)) (intervalTranslate hb hbV v)) =
      rectangleSource hA e Λ x hr (a + u) (intervalTranslate hb hbV v)
  rw [hd, hx (intervalTranslate hb hbV v), projIcc_of_mem hU hum,
    projIcc_of_mem hA (show a + u ∈ Icc 0 A from
      ⟨add_nonneg ha hum.1, (add_le_add_right hum.2 a).trans haU⟩)]
  rfl

theorem IsWaveIntegral.translate {hA : 0 ≤ A} {hB : 0 ≤ B} {e Λ : ℝ}
    {zIn : C(Icc 0 A, WaveVector)} {vOut : C(Icc 0 B, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 A))} {x : WaveState A B}
    (hx : IsWaveIntegral hA hB e Λ zIn vOut uIn x)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : 0 ≤ a) (haU : a + U ≤ A)
    (hb : 0 ≤ b) (hbV : b + V ≤ B) :
    let y := waveTranslate ha haU hb hbV x
    let v₀ : Icc 0 V := ⟨0, le_rfl, hV⟩
    IsWaveIntegral hU hV e Λ
      (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (ContinuousMap.evalCLM ℝ v₀) y.1)
      (y.2.1 ⟨0, le_rfl, hU⟩)
      ((ContinuousMap.evalCLM ℝ v₀).compLpL 2 (volume.restrict (Icc 0 U)) y.2.2) y := by
  let y := waveTranslate ha haU hb hbV x
  let u₀ : Icc 0 U := ⟨0, le_rfl, hU⟩
  let v₀ : Icc 0 V := ⟨0, le_rfl, hV⟩
  let F := rectangleSource hA e Λ x hx.choose
  have hz : incomingField zIn + longitudinalIntegral hB x.2.1 = x.1 := congrArg Prod.fst hx.choose_spec
  have hw : ContinuousMap.const _ vOut + horizontalPrimitive hA F = x.2.1 :=
    congrArg (fun z : WaveState A B => z.2.1) hx.choose_spec
  have hd : incomingTransverse uIn + verticalPrimitive hB F = x.2.2 :=
    congrArg (fun z : WaveState A B => z.2.2) hx.choose_spec
  have hr : ∀ u v, y.1 u v 0 ≠ 0 := fun u v => hx.choose (intervalTranslate ha haU u) (intervalTranslate hb hbV v)
  have hF : rectangleSource hU e Λ y hr = transverseTranslate ha haU hb hbV F :=
    rectangleSource_translate hA hU ha haU hb hbV e Λ x hx.choose
  refine ⟨hr, ?_⟩
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change y.1 u v₀ + continuousPrimitive hV (y.2.1 u) v = y.1 u v
    have he := continuousPrimitive_translate hB hV hb hbV (x.2.1 (intervalTranslate ha haU u)) v
    change continuousPrimitive hV (y.2.1 u) v = _ at he
    rw [he]
    have ht := congrArg (fun z : WaveRectangle A B => z (intervalTranslate ha haU u) (intervalTranslate hb hbV v)) hz
    have hb' := congrArg (fun z : WaveRectangle A B => z (intervalTranslate ha haU u) (intervalTranslate hb hbV v₀)) hz
    change zIn (intervalTranslate ha haU u) + continuousPrimitive hB (x.2.1 (intervalTranslate ha haU u))
      (intervalTranslate hb hbV v) = y.1 u v at ht
    change zIn (intervalTranslate ha haU u) + continuousPrimitive hB (x.2.1 (intervalTranslate ha haU u))
      (intervalTranslate hb hbV v₀) = y.1 u v₀ at hb'
    rw [← ht, ← hb']
    abel
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change y.2.1 u₀ v + horizontalPrimitive hU (rectangleSource hU e Λ y hr) u v = y.2.1 u v
    rw [hF, transverseTranslate, horizontalPrimitive_compLp]
    change y.2.1 u₀ v + horizontalPrimitive hU (intervalTranslateLp ha haU F) u
      (intervalTranslate hb hbV v) = y.2.1 u v
    rw [horizontalPrimitive_translate hA hU ha haU F u]
    have ht := congrArg (fun z : WaveRectangle A B => z (intervalTranslate ha haU u) (intervalTranslate hb hbV v)) hw
    have ha' := congrArg (fun z : WaveRectangle A B => z (intervalTranslate ha haU u₀) (intervalTranslate hb hbV v)) hw
    change vOut (intervalTranslate hb hbV v) + horizontalPrimitive hA F (intervalTranslate ha haU u)
      (intervalTranslate hb hbV v) = y.2.1 u v at ht
    change vOut (intervalTranslate hb hbV v) + horizontalPrimitive hA F (intervalTranslate ha haU u₀)
      (intervalTranslate hb hbV v) = y.2.1 u₀ v at ha'
    rw [← ht, ← ha']
    simp only [ContinuousMap.sub_apply]
    abel
  · have hd' : ∀ᵐ u ∂volume.restrict (Icc 0 A),
        x.2.2 u = ContinuousMap.const _ (uIn u) + continuousPrimitive hB (F u) := by
      filter_upwards [Lp.coeFn_add (incomingTransverse (V := B) uIn) (verticalPrimitive hB F),
        (ContinuousLinearMap.const ℝ (Icc 0 B)).coeFn_compLpL uIn, verticalPrimitive_ae hB F] with u hu hi hv
      rw [← hd]
      change (incomingTransverse (V := B) uIn + verticalPrimitive hB F : WaveTransverse A B) u = _
      rw [hu, Pi.add_apply, hv]
      exact congrArg (fun z => z + continuousPrimitive hB (F u)) hi
    let ui := (ContinuousMap.evalCLM ℝ v₀).compLpL 2 (volume.restrict (Icc 0 U)) y.2.2
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (incomingTransverse (V := V) ui)
        (verticalPrimitive hV (rectangleSource hU e Λ y hr)),
      (ContinuousLinearMap.const ℝ (Icc 0 V)).coeFn_compLpL ui,
      (ContinuousMap.evalCLM ℝ v₀).coeFn_compLpL y.2.2,
      verticalPrimitive_ae hV (rectangleSource hU e Λ y hr),
      transverseTranslate_ae ha haU hb hbV F, transverseTranslate_ae ha haU hb hbV x.2.2,
      intervalTranslate_ae ha haU hd'] with u hu hi hui hv hFu hyu hdu
    apply ContinuousMap.ext
    intro v
    change incomingTransverse (V := V) ui u = ContinuousMap.const _ (ui u) at hi
    change (incomingTransverse (V := V) ui + verticalPrimitive hV (rectangleSource hU e Λ y hr) : WaveTransverse U V) u v = y.2.2 u v
    rw [hu, Pi.add_apply, hi, hv, hF, hFu]
    change ui u + continuousPrimitive hV ((F (a + u)).comp (intervalTranslate hb hbV)) v = y.2.2 u v
    change ui u = y.2.2 u v₀ at hui
    rw [hui]
    change transverseTranslate ha haU hb hbV x.2.2 u v₀ + _ = transverseTranslate ha haU hb hbV x.2.2 u v
    rw [hyu, continuousPrimitive_translate hB hV hb hbV (F (a + u)) v, hdu]
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply]
    abel

theorem IsWaveIntegral.translated_incoming_primitive {hA : 0 ≤ A} {hB : 0 ≤ B} {e Λ : ℝ}
    {zIn : C(Icc 0 A, WaveVector)} {vOut : C(Icc 0 B, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 A))} {x : WaveState A B}
    (hx : IsWaveIntegral hA hB e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hA uIn)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : 0 ≤ a) (haU : a + U ≤ A)
    (hb : 0 ≤ b) (hbV : b + V ≤ B) :
    let y := waveTranslate ha haU hb hbV x
    let u₀ : Icc 0 U := ⟨0, le_rfl, hU⟩
    let v₀ : Icc 0 V := ⟨0, le_rfl, hV⟩
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (ContinuousMap.evalCLM ℝ v₀) y.1 =
      ContinuousMap.const _ (y.1 u₀ v₀) + horizontalPrimitive hU
        ((ContinuousMap.evalCLM ℝ v₀).compLpL 2 (volume.restrict (Icc 0 U)) y.2.2) := by
  let u₀ : Icc 0 U := ⟨0, le_rfl, hU⟩
  let v₀ : Icc 0 V := ⟨0, le_rfl, hV⟩
  apply ContinuousMap.ext
  intro u
  rw [horizontalPrimitive_compLp]
  change x.1 (intervalTranslate ha haU u) (intervalTranslate hb hbV v₀) =
    x.1 (intervalTranslate ha haU u₀) (intervalTranslate hb hbV v₀) +
      horizontalPrimitive hU (transverseTranslate ha haU hb hbV x.2.2) u v₀
  rw [transverseTranslate, horizontalPrimitive_compLp]
  change _ = _ + horizontalPrimitive hU (intervalTranslateLp ha haU x.2.2) u (intervalTranslate hb hbV v₀)
  rw [horizontalPrimitive_translate hA hU ha haU x.2.2 u]
  have he := hx.horizontal_identity hzin
  have ht := congrArg (fun z : WaveRectangle A B => z (intervalTranslate ha haU u) (intervalTranslate hb hbV v₀)) he
  have hbase := congrArg (fun z : WaveRectangle A B => z (intervalTranslate ha haU u₀) (intervalTranslate hb hbV v₀)) he
  change x.1 (intervalTranslate ha haU u) (intervalTranslate hb hbV v₀) =
    (c + continuousPrimitive hB vOut (intervalTranslate hb hbV v₀)) +
      horizontalPrimitive hA x.2.2 (intervalTranslate ha haU u) (intervalTranslate hb hbV v₀) at ht
  change x.1 (intervalTranslate ha haU u₀) (intervalTranslate hb hbV v₀) =
    (c + continuousPrimitive hB vOut (intervalTranslate hb hbV v₀)) +
      horizontalPrimitive hA x.2.2 (intervalTranslate ha haU u₀) (intervalTranslate hb hbV v₀) at hbase
  rw [ht, hbase]
  simp only [ContinuousMap.sub_apply]
  abel

end CauchyHorizon
