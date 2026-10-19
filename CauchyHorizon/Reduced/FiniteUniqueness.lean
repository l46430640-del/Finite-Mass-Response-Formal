import CauchyHorizon.Reduced.LocalUniqueness
import CauchyHorizon.Reduced.RestrictionComposition
import CauchyHorizon.Characteristic.PrefixData
import CauchyHorizon.Analysis.FiniteSubdivision

/-! Local uniqueness propagates by finite subdivision, first in v and then in u. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_thin_wave_uniqueness (e Λ ρ M : ℝ) (hρ : 0 < ρ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ d →
      ∀ (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
        (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x y : WaveState U V),
        IsWaveIntegral hU hV e Λ zIn vOut uIn x → IsWaveIntegral hU hV e Λ zIn vOut uIn y →
        (∀ u v, ρ ≤ x.1 u v 0) → (∀ u v, ρ ≤ y.1 u v 0) → ‖x‖ ≤ M → ‖y‖ ≤ M → x = y := by
  obtain ⟨d, hd, hd1, huniq⟩ := exists_local_wave_uniqueness e Λ ρ M hρ
  refine ⟨d, hd, hd1, ?_⟩
  intro U V hU hV hUd zIn vOut uIn x y hx hy hxr hyr hxn hyn
  let P (b : ℝ) : Prop := ∀ hb : 0 ≤ b, ∀ hbV : b ≤ V,
    waveTranslate (a := 0) (U := U) (b := 0) (V := b) le_rfl (by simp) le_rfl (by linarith) x =
      waveTranslate (a := 0) (U := U) (b := 0) (V := b) le_rfl (by simp) le_rfl (by linarith) y
  have hbase : P 0 := by
    intro h0 h0V
    exact huniq hU h0 hUd hd.le _ _ _ _ _ (hx.prefix hU h0 le_rfl h0V) (hy.prefix hU h0 le_rfl h0V)
      (fun u v => hxr _ _) (fun u v => hyr _ _)
      ((waveTranslate_norm_le _ _ _ _ x).trans hxn) ((waveTranslate_norm_le _ _ _ _ y).trans hyn)
  have hstep (b H : ℝ) (hb : 0 ≤ b) (hH : 0 ≤ H) (hbH : b + H ≤ V) (hHd : H ≤ d) (ih : P b) : P (b + H) := by
    intro _hbH _hbHV
    let xp := waveTranslate (a := 0) (U := U) le_rfl (show 0 + U ≤ U by simp) hb hbH x
    let yp := waveTranslate (a := 0) (U := U) le_rfl (show 0 + U ≤ U by simp) hb hbH y
    have hxp := hx.translate hU hH (a := 0) le_rfl (by simp) hb hbH
    have hyp := hy.translate hU hH (a := 0) le_rfl (by simp) hb hbH
    have hbot : waveTranslate (a := 0) (U := U) (b := 0) (V := 0) le_rfl (by simp) le_rfl (by linarith) xp =
        waveTranslate (a := 0) (U := U) (b := 0) (V := 0) le_rfl (by simp) le_rfl (by linarith) yp := by
      have he := congrArg (waveTranslate (a := 0) (U := U) (b := b) (V := 0)
        le_rfl (show 0 + U ≤ U by simp) hb (show b + 0 ≤ b by simp)) (ih hb (by linarith))
      simpa only [xp, yp, waveTranslate_comp, zero_add, add_zero] using he
    have h0 := hxp.prefix hU (le_refl (0 : ℝ)) le_rfl hH
    simp only [intervalTranslate_zero, ContinuousMap.comp_id, intervalTranslateLp_zero] at h0
    have hyp' := hyp.of_vertical_prefix (le_refl (0 : ℝ)) hH h0 hbot.symm
    have hvx := waveIteration_outgoing_derivative hU hV e Λ zIn vOut uIn x hx.choose
    have hvy := waveIteration_outgoing_derivative hU hV e Λ zIn vOut uIn y hy.choose
    rw [hx.choose_spec] at hvx
    rw [hy.choose_spec] at hvy
    have hvp : xp.2.1 ⟨0, le_rfl, hU⟩ = yp.2.1 ⟨0, le_rfl, hU⟩ := by
      apply ContinuousMap.ext
      intro v
      change x.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) ⟨0, le_rfl, hU⟩) _ =
        y.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) ⟨0, le_rfl, hU⟩) _
      rw [intervalTranslate_zero, ContinuousMap.id_apply, hvx, hvy]
    change IsWaveIntegral hU hH e Λ _ (yp.2.1 ⟨0, le_rfl, hU⟩) _ yp at hyp'
    rw [← hvp] at hyp'
    have heq : xp = yp := huniq hU hH hUd hHd _ _ _ xp yp hxp hyp'
      (fun u v => hxr _ _) (fun u v => hyr _ _)
      ((waveTranslate_norm_le _ _ _ _ x).trans hxn) ((waveTranslate_norm_le _ _ _ _ y).trans hyn)
    apply waveTranslate_ext_vertical hb hH
    · simpa only [waveTranslate_comp, zero_add] using ih hb (show b ≤ V by linarith)
    · simpa only [xp, yp, waveTranslate_comp, zero_add] using heq
  have he := interval_subdivision_induction hV hd hbase hstep hV le_rfl
  simpa only [waveTranslate_zero] using he

theorem IsWaveIntegral.eq_of_bounds {U V e Λ ρ M : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x y : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hy : IsWaveIntegral hU hV e Λ zIn vOut uIn y)
    (hρ : 0 < ρ) (hxr : ∀ u v, ρ ≤ x.1 u v 0) (hyr : ∀ u v, ρ ≤ y.1 u v 0)
    (hxn : ‖x‖ ≤ M) (hyn : ‖y‖ ≤ M) : x = y := by
  obtain ⟨d, hd, _hd1, huniq⟩ := exists_thin_wave_uniqueness e Λ ρ M hρ
  let P (a : ℝ) : Prop := ∀ ha : 0 ≤ a, ∀ haU : a ≤ U,
    waveTranslate (a := 0) (U := a) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) x =
      waveTranslate (a := 0) (U := a) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) y
  have hbase : P 0 := by
    intro h0 h0U
    exact huniq h0 hV hd.le _ _ _ _ _ (hx.prefix h0 hV h0U le_rfl) (hy.prefix h0 hV h0U le_rfl)
      (fun u v => hxr _ _) (fun u v => hyr _ _)
      ((waveTranslate_norm_le _ _ _ _ x).trans hxn) ((waveTranslate_norm_le _ _ _ _ y).trans hyn)
  have hstep (a W : ℝ) (ha : 0 ≤ a) (hW : 0 ≤ W) (haW : a + W ≤ U) (hWd : W ≤ d) (ih : P a) : P (a + W) := by
    intro _haW _haWU
    let xp := waveTranslate ha haW (b := 0) (V := V) le_rfl (show 0 + V ≤ V by simp) x
    let yp := waveTranslate ha haW (b := 0) (V := V) le_rfl (show 0 + V ≤ V by simp) y
    have hxp := hx.incoming_translate hW hV ha haW le_rfl
    have hyp := hy.incoming_translate hW hV ha haW le_rfl
    have hvp : x.2.1 ⟨a, ha, by linarith⟩ = y.2.1 ⟨a, ha, by linarith⟩ := by
      have he := congrArg (fun s : WaveState a V => s.2.1 ⟨a, ha, le_rfl⟩) (ih ha (by linarith))
      change (x.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + a ≤ U by linarith) ⟨a, ha, le_rfl⟩)).comp
        (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by simp)) =
        (y.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + a ≤ U by linarith) ⟨a, ha, le_rfl⟩)).comp
        (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by simp)) at he
      have haend : intervalTranslate (a := 0) le_rfl (show 0 + a ≤ U by linarith) ⟨a, ha, le_rfl⟩ =
          (⟨a, ha, by linarith⟩ : Icc 0 U) := Subtype.ext (zero_add _)
      simpa only [intervalTranslate_zero, ContinuousMap.comp_id, haend] using he
    rw [← hvp] at hyp
    have heq : xp = yp := huniq hW hV hWd _ _ _ xp yp hxp hyp
      (fun u v => hxr _ _) (fun u v => hyr _ _)
      ((waveTranslate_norm_le _ _ _ _ x).trans hxn) ((waveTranslate_norm_le _ _ _ _ y).trans hyn)
    apply waveTranslate_ext_horizontal ha hW
    · simpa only [waveTranslate_comp, zero_add] using ih ha (show a ≤ U by linarith)
    · simpa only [xp, yp, waveTranslate_comp, zero_add] using heq
  have he := interval_subdivision_induction hU hd hbase hstep hU le_rfl
  simpa only [waveTranslate_zero] using he

theorem IsWaveIntegral.unique_of_positive_radius {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x y : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hy : IsWaveIntegral hU hV e Λ zIn vOut uIn y)
    (hxr : ∀ u v, 0 < x.1 u v 0) (hyr : ∀ u v, 0 < y.1 u v 0) : x = y := by
  have hc : Continuous (fun q : Icc 0 U × Icc 0 V => min (x.1 q.1 q.2 0) (y.1 q.1 q.2 0)) := by fun_prop
  obtain ⟨q, _hq, hmin⟩ := isCompact_univ.exists_isMinOn
    ⟨(⟨0, le_rfl, hU⟩, ⟨0, le_rfl, hV⟩), mem_univ _⟩ hc.continuousOn
  have hρ : 0 < min (x.1 q.1 q.2 0) (y.1 q.1 q.2 0) := lt_min (hxr _ _) (hyr _ _)
  exact hx.eq_of_bounds hy (M := max ‖x‖ ‖y‖) hρ
    (fun u v => (hmin (mem_univ (u, v))).trans (min_le_left _ _))
    (fun u v => (hmin (mem_univ (u, v))).trans (min_le_right _ _)) (le_max_left _ _) (le_max_right _ _)

end CauchyHorizon
