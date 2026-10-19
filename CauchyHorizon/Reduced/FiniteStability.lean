import CauchyHorizon.Reduced.RectangleTopology
import CauchyHorizon.Characteristic.PrefixData
import CauchyHorizon.Analysis.FiniteSubdivision

/-! Continuous dependence on a fixed finite rectangle by two finite subdivisions. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

theorem exists_local_wave_tendsto (e Λ ρ M : ℝ) (hρ : 0 < ρ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {ι : Type*} {l : Filter ι} {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ d → V ≤ d →
      ∀ {z : ι → C(Icc 0 U, WaveVector)} {z' : C(Icc 0 U, WaveVector)}
        {v : ι → C(Icc 0 V, WaveVector)} {v' : C(Icc 0 V, WaveVector)}
        {u : ι → Lp WaveVector 2 (volume.restrict (Icc 0 U))}
        {u' : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : ι → WaveState U V} {y : WaveState U V},
        (∀ i, IsWaveIntegral hU hV e Λ (z i) (v i) (u i) (x i)) →
        IsWaveIntegral hU hV e Λ z' v' u' y →
        (∀ i s t, ρ ≤ (x i).1 s t 0) → (∀ s t, ρ ≤ y.1 s t 0) →
        (∀ i, ‖x i‖ ≤ M) → ‖y‖ ≤ M →
        Tendsto z l (𝓝 z') → Tendsto v l (𝓝 v') → Tendsto u l (𝓝 u') → Tendsto x l (𝓝 y) := by
  obtain ⟨d, hd, hd1, hstab⟩ := exists_local_wave_stability e Λ ρ M hρ
  refine ⟨d, hd, hd1, ?_⟩
  intro ι l U V hU hV hUd hVd z z' v v' u u' x y hx hy hxr hyr hxn hyn hz hv hu
  apply (tendsto_iff_norm_sub_tendsto_zero (f := x) (b := y)).2
  have hlim : Tendsto (fun i => 2 * (‖z i - z'‖ + ‖v i - v'‖ + ‖u i - u'‖)) l (𝓝 0) := by
    simpa only [add_zero, mul_zero] using
      (((tendsto_iff_norm_sub_tendsto_zero.1 hz).add (tendsto_iff_norm_sub_tendsto_zero.1 hv)).add
        (tendsto_iff_norm_sub_tendsto_zero.1 hu)).const_mul 2
  exact squeeze_zero (fun i => norm_nonneg _) (fun i =>
    hstab hU hV hUd hVd (z i) z' (v i) v' (u i) u' (x i) y
      (hx i) hy (hxr i) hyr (hxn i) hyn) hlim

theorem exists_thin_wave_tendsto (e Λ ρ M : ℝ) (hρ : 0 < ρ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {ι : Type*} {l : Filter ι} {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ d →
      ∀ {z : ι → C(Icc 0 U, WaveVector)} {z' : C(Icc 0 U, WaveVector)}
        {v : ι → C(Icc 0 V, WaveVector)} {v' : C(Icc 0 V, WaveVector)}
        {u : ι → Lp WaveVector 2 (volume.restrict (Icc 0 U))}
        {u' : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : ι → WaveState U V} {y : WaveState U V},
        (∀ i, IsWaveIntegral hU hV e Λ (z i) (v i) (u i) (x i)) →
        IsWaveIntegral hU hV e Λ z' v' u' y →
        (∀ i s t, ρ ≤ (x i).1 s t 0) → (∀ s t, ρ ≤ y.1 s t 0) →
        (∀ i, ‖x i‖ ≤ M) → ‖y‖ ≤ M →
        Tendsto z l (𝓝 z') → Tendsto v l (𝓝 v') → Tendsto u l (𝓝 u') → Tendsto x l (𝓝 y) := by
  obtain ⟨d, hd, hd1, hlocal⟩ := exists_local_wave_tendsto e Λ ρ M hρ
  refine ⟨d, hd, hd1, ?_⟩
  intro ι l U V hU hV hUd z z' v v' u u' x y hx hy hxr hyr hxn hyn hz hv hu
  let P (b : ℝ) : Prop := ∀ hb : 0 ≤ b, ∀ hbV : b ≤ V,
    Tendsto (fun i => waveTranslate (a := 0) (U := U) (b := 0) (V := b)
      le_rfl (by simp) le_rfl (by linarith) (x i)) l
      (𝓝 (waveTranslate (a := 0) (U := U) (b := 0) (V := b) le_rfl (by simp) le_rfl (by linarith) y))
  have hbase : P 0 := by
    intro h0 h0V
    apply hlocal hU h0 hUd hd.le (fun i => (hx i).prefix hU h0 le_rfl h0V) (hy.prefix hU h0 le_rfl h0V)
      (fun i s t => hxr i _ _) (fun s t => hyr _ _)
      (fun i => (waveTranslate_norm_le _ _ _ _ (x i)).trans (hxn i))
      ((waveTranslate_norm_le _ _ _ _ y).trans hyn)
    · simpa only [intervalTranslate_zero, ContinuousMap.comp_id] using hz
    · exact (ContinuousMap.compCLM ℝ WaveVector (intervalTranslate (a := 0) le_rfl (by linarith))).continuous.tendsto _ |>.comp hv
    · simpa only [intervalTranslateLp_zero] using hu
  have hstep (b H : ℝ) (hb : 0 ≤ b) (hH : 0 ≤ H) (hbH : b + H ≤ V) (hHd : H ≤ d) (ih : P b) : P (b + H) := by
    intro _hbH _hbHV
    let xp (i : ι) := waveTranslate (a := 0) (U := U) le_rfl (show 0 + U ≤ U by simp) hb hbH (x i)
    let yp := waveTranslate (a := 0) (U := U) le_rfl (show 0 + U ≤ U by simp) hb hbH y
    let q (s : WaveState U V) := waveTranslate (a := 0) (U := U) (V := 0)
      le_rfl (show 0 + U ≤ U by simp) hb (show b + 0 ≤ V by linarith) s
    let E := ContinuousMap.evalCLM ℝ (⟨0, le_rfl, le_rfl⟩ : Icc (0 : ℝ) 0) (M := WaveVector)
    have hq : Tendsto (fun i => q (x i)) l (𝓝 (q y)) := by
      have hh := (continuous_waveTranslate (a := 0) (U := U) (b := b) (V := 0)
        le_rfl (show 0 + U ≤ U by simp) hb (show b + 0 ≤ b by simp)).tendsto _ |>.comp (ih hb (by linarith))
      simpa only [q, Function.comp_def, waveTranslate_comp, zero_add] using hh
    have hsol {z0 : C(Icc 0 U, WaveVector)} {v0 : C(Icc 0 V, WaveVector)}
        {u0 : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {s : WaveState U V}
        (hs : IsWaveIntegral hU hV e Λ z0 v0 u0 s) :
        IsWaveIntegral hU hH e Λ
          (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) E (q s).1)
          (v0.comp (intervalTranslate hb hbH))
          (E.compLpL 2 (volume.restrict (Icc 0 U)) (q s).2.2)
          (waveTranslate (a := 0) (U := U) le_rfl (show 0 + U ≤ U by simp) hb hbH s) := by
      have hp := hs.translate hU hH (a := 0) le_rfl (by simp) hb hbH
      have hq0 := hs.translate hU (le_refl (0 : ℝ)) (a := 0) le_rfl (by simp) hb (show b + 0 ≤ V by linarith)
      have hp' := hp.of_vertical_prefix (le_refl (0 : ℝ)) hH hq0 (by
        simp only [waveTranslate_comp, add_zero])
      have hout := waveIteration_outgoing_derivative hU hV e Λ z0 v0 u0 s hs.choose
      rw [hs.choose_spec] at hout
      have he : (waveTranslate (a := 0) (U := U) le_rfl (show 0 + U ≤ U by simp) hb hbH s).2.1
          ⟨0, le_rfl, hU⟩ = v0.comp (intervalTranslate hb hbH) := by
        apply ContinuousMap.ext
        intro t
        change s.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) ⟨0, le_rfl, hU⟩) _ = _
        rw [intervalTranslate_zero, ContinuousMap.id_apply, hout]
        rfl
      rw [he] at hp'
      exact hp'
    have hp : Tendsto xp l (𝓝 yp) :=
      hlocal hU hH hUd hHd (fun i => hsol (hx i)) (hsol hy)
        (fun i s t => hxr i _ _) (fun s t => hyr _ _)
        (fun i => (waveTranslate_norm_le _ _ _ _ (x i)).trans (hxn i))
        ((waveTranslate_norm_le _ _ _ _ y).trans hyn)
        ((ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) E).continuous.tendsto _ |>.comp hq.fst_nhds)
        ((ContinuousMap.compCLM ℝ WaveVector (intervalTranslate hb hbH)).continuous.tendsto _ |>.comp hv)
        ((E.compLpL 2 (volume.restrict (Icc 0 U))).continuous.tendsto _ |>.comp hq.snd_nhds.snd_nhds)
    apply waveTranslate_tendsto_vertical hb hH
    · simpa only [waveTranslate_comp, zero_add] using ih hb (show b ≤ V by linarith)
    · simpa only [xp, yp, waveTranslate_comp, zero_add] using hp
  have hh := interval_subdivision_induction hV hd hbase hstep hV le_rfl
  simpa only [waveTranslate_zero] using hh

theorem IsWaveIntegral.tendsto_of_bounds {ι : Type*} {l : Filter ι} {U V e Λ ρ M : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {z : ι → C(Icc 0 U, WaveVector)} {z' : C(Icc 0 U, WaveVector)}
    {v : ι → C(Icc 0 V, WaveVector)} {v' : C(Icc 0 V, WaveVector)}
    {u : ι → Lp WaveVector 2 (volume.restrict (Icc 0 U))}
    {u' : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : ι → WaveState U V} {y : WaveState U V}
    (hx : ∀ i, IsWaveIntegral hU hV e Λ (z i) (v i) (u i) (x i))
    (hy : IsWaveIntegral hU hV e Λ z' v' u' y) (hρ : 0 < ρ)
    (hxr : ∀ i s t, ρ ≤ (x i).1 s t 0) (hyr : ∀ s t, ρ ≤ y.1 s t 0)
    (hxn : ∀ i, ‖x i‖ ≤ M) (hyn : ‖y‖ ≤ M)
    (hz : Tendsto z l (𝓝 z')) (hv : Tendsto v l (𝓝 v')) (hu : Tendsto u l (𝓝 u')) :
    Tendsto x l (𝓝 y) := by
  obtain ⟨d, hd, _hd1, hthin⟩ := exists_thin_wave_tendsto e Λ ρ M hρ
  let P (a : ℝ) : Prop := ∀ ha : 0 ≤ a, ∀ haU : a ≤ U,
    Tendsto (fun i => waveTranslate (a := 0) (U := a) (b := 0) (V := V)
      le_rfl (by linarith) le_rfl (by simp) (x i)) l
      (𝓝 (waveTranslate (a := 0) (U := a) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) y))
  have hbase : P 0 := by
    intro h0 h0U
    apply hthin h0 hV hd.le (fun i => (hx i).prefix h0 hV h0U le_rfl) (hy.prefix h0 hV h0U le_rfl)
      (fun i s t => hxr i _ _) (fun s t => hyr _ _)
      (fun i => (waveTranslate_norm_le _ _ _ _ (x i)).trans (hxn i))
      ((waveTranslate_norm_le _ _ _ _ y).trans hyn)
    · exact (ContinuousMap.compCLM ℝ WaveVector (intervalTranslate (a := 0) le_rfl (by linarith))).continuous.tendsto _ |>.comp hz
    · simpa only [intervalTranslate_zero, ContinuousMap.comp_id] using hv
    · exact (continuous_intervalTranslateLp (a := 0) (U := 0) le_rfl (by linarith)).tendsto _ |>.comp hu
  have hstep (a W : ℝ) (ha : 0 ≤ a) (hW : 0 ≤ W) (haW : a + W ≤ U) (hWd : W ≤ d) (ih : P a) : P (a + W) := by
    intro _haW _haWU
    let xp (i : ι) := waveTranslate ha haW (b := 0) (V := V) le_rfl (show 0 + V ≤ V by simp) (x i)
    let yp := waveTranslate ha haW (b := 0) (V := V) le_rfl (show 0 + V ≤ V by simp) y
    have hvp : Tendsto (fun i => (x i).2.1 ⟨a, ha, by linarith⟩) l
        (𝓝 (y.2.1 ⟨a, ha, by linarith⟩)) := by
      have hh := (ContinuousMap.evalCLM ℝ (⟨a, ha, le_rfl⟩ : Icc 0 a)
        (M := C(Icc 0 V, WaveVector))).continuous.tendsto _ |>.comp (ih ha (by linarith)).snd_nhds.fst_nhds
      have haend : intervalTranslate (a := 0) le_rfl (show 0 + a ≤ U by linarith) ⟨a, ha, le_rfl⟩ =
          (⟨a, ha, by linarith⟩ : Icc 0 U) := Subtype.ext (zero_add _)
      change Tendsto (fun i => ((x i).2.1
        (intervalTranslate (a := 0) le_rfl (show 0 + a ≤ U by linarith) ⟨a, ha, le_rfl⟩)).comp
          (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by simp))) l
        (𝓝 ((y.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + a ≤ U by linarith) ⟨a, ha, le_rfl⟩)).comp
          (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by simp)))) at hh
      simpa only [haend, intervalTranslate_zero, ContinuousMap.comp_id] using hh
    have hp : Tendsto xp l (𝓝 yp) := by
      apply hthin hW hV hWd (fun i => (hx i).incoming_translate hW hV ha haW le_rfl)
        (hy.incoming_translate hW hV ha haW le_rfl)
        (fun i s t => hxr i _ _) (fun s t => hyr _ _)
        (fun i => (waveTranslate_norm_le _ _ _ _ (x i)).trans (hxn i))
        ((waveTranslate_norm_le _ _ _ _ y).trans hyn)
      · exact (ContinuousMap.compCLM ℝ WaveVector (intervalTranslate ha haW)).continuous.tendsto _ |>.comp hz
      · simpa only [intervalTranslate_zero, ContinuousMap.comp_id] using hvp
      · exact (continuous_intervalTranslateLp ha haW).tendsto _ |>.comp hu
    apply waveTranslate_tendsto_horizontal ha hW
    · simpa only [waveTranslate_comp, zero_add] using ih ha (show a ≤ U by linarith)
    · simpa only [xp, yp, waveTranslate_comp, zero_add] using hp
  have hh := interval_subdivision_induction hU hd hbase hstep hU le_rfl
  simpa only [waveTranslate_zero] using hh

end CauchyHorizon
