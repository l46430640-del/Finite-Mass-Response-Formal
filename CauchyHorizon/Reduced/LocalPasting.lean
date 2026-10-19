import CauchyHorizon.Reduced.VerticalPasting
import CauchyHorizon.Reduced.RectangleRestriction
import CauchyHorizon.Reduced.LocalUniqueness

/-! Local uniqueness supplies the derivative matching needed for characteristic pasting. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_vertical_pasting_width (e Λ ρ M : ℝ) (hρ : 0 < ρ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {U V W : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W), U ≤ d →
      ∀ (zx zy : C(Icc 0 U, WaveVector)) (vx : C(Icc 0 V, WaveVector)) (vy : C(Icc 0 W, WaveVector))
        (ux uy : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x : WaveState U V) (y : WaveState U W),
        IsWaveIntegral hU hV e Λ zx vx ux x → IsWaveIntegral hU hW e Λ zy vy uy y →
        (∀ u v, ρ ≤ x.1 u v 0) → (∀ u v, ρ ≤ y.1 u v 0) → ‖x‖ ≤ M → ‖y‖ ≤ M →
        (∀ u, x.1 u ⟨V, hV, le_rfl⟩ = y.1 u ⟨0, le_rfl, hW⟩) →
        (∀ᵐ u ∂volume.restrict (Icc 0 U), x.2.2 u ⟨V, hV, le_rfl⟩ = y.2.2 u ⟨0, le_rfl, hW⟩) →
        vx ⟨V, hV, le_rfl⟩ = vy ⟨0, le_rfl, hW⟩ →
      IsWaveIntegral hU (add_nonneg hV hW) e Λ zx (intervalSplice hV hW vx vy) ux (waveSplice hV hW x y) := by
  obtain ⟨d, hd, hd1, huniq⟩ := exists_local_wave_uniqueness e Λ ρ M hρ
  refine ⟨d, hd, hd1, ?_⟩
  intro U V W hU hV hW hUd zx zy vx vy ux uy x y hx hy hxr hyr hxn hyn hz hdu hcorner
  let o : Icc (0 : ℝ) 0 := ⟨0, le_rfl, le_rfl⟩
  let p := waveTranslate (a := 0) (U := U) (V := 0) le_rfl (show 0 + U ≤ U by linarith)
    hV (show V + 0 ≤ V by linarith) x
  let q := waveTranslate (a := 0) (U := U) (b := 0) (V := 0) le_rfl (show 0 + U ≤ U by linarith)
    le_rfl (show (0 : ℝ) + 0 ≤ W by linarith) y
  let E := ContinuousMap.evalCLM ℝ o (M := WaveVector)
  have hp := hx.translate hU (le_refl (0 : ℝ)) (a := 0) le_rfl (by linarith) hV (by linarith)
  have hq := hy.translate hU (le_refl (0 : ℝ)) (a := 0) le_rfl (by linarith) (b := 0) le_rfl (by linarith)
  have hleft (u : Icc 0 U) : intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by linarith) u = u :=
    Subtype.ext (zero_add _)
  have hend : intervalTranslate hV (show V + 0 ≤ V by linarith) o = ⟨V, hV, le_rfl⟩ :=
    Subtype.ext (add_zero _)
  have hstart : intervalTranslate (a := 0) le_rfl (show (0 : ℝ) + 0 ≤ W by linarith) o = ⟨0, le_rfl, hW⟩ :=
    Subtype.ext (zero_add _)
  have ho (v : Icc (0 : ℝ) 0) : v = o := Subtype.ext (le_antisymm v.property.2 v.property.1)
  have hz0 : ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) E p.1 =
      ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) E q.1 := by
    apply ContinuousMap.ext
    intro u
    change x.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by linarith) u)
      (intervalTranslate hV (show V + 0 ≤ V by linarith) o) =
        y.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by linarith) u)
          (intervalTranslate (a := 0) le_rfl (show (0 : ℝ) + 0 ≤ W by linarith) o)
    rw [hleft, hend, hstart]
    exact hz u
  have hv0 : p.2.1 ⟨0, le_rfl, hU⟩ = q.2.1 ⟨0, le_rfl, hU⟩ := by
    apply ContinuousMap.ext
    intro v
    rw [ho v]
    change x.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by linarith) ⟨0, le_rfl, hU⟩)
      (intervalTranslate hV (show V + 0 ≤ V by linarith) o) =
        y.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by linarith) ⟨0, le_rfl, hU⟩)
          (intervalTranslate (a := 0) le_rfl (show (0 : ℝ) + 0 ≤ W by linarith) o)
    rw [hleft, hend, hstart]
    have hxout := waveIteration_outgoing_derivative hU hV e Λ zx vx ux x hx.choose
    have hyout := waveIteration_outgoing_derivative hU hW e Λ zy vy uy y hy.choose
    rw [hx.choose_spec] at hxout
    rw [hy.choose_spec] at hyout
    rw [hxout, hyout]
    exact hcorner
  have hu0 : E.compLpL 2 (volume.restrict (Icc 0 U)) p.2.2 =
      E.compLpL 2 (volume.restrict (Icc 0 U)) q.2.2 := by
    apply Lp.ext
    filter_upwards [E.coeFn_compLpL p.2.2, E.coeFn_compLpL q.2.2,
      transverseTranslate_ae (a := 0) (U := U) (V := 0) le_rfl (by linarith) hV (by linarith) x.2.2,
      transverseTranslate_ae (a := 0) (U := U) (b := 0) (V := 0) le_rfl (by linarith) le_rfl (by linarith) y.2.2,
      hdu] with u he hf hpx hqy hm
    rw [he, hf]
    change transverseTranslate (a := 0) (U := U) (V := 0) le_rfl (by linarith) hV (by linarith) x.2.2 u o =
      transverseTranslate (a := 0) (U := U) (b := 0) (V := 0) le_rfl (by linarith) le_rfl (by linarith) y.2.2 u o
    rw [hpx, hqy]
    change x.2.2 (0 + u) (intervalTranslate hV (show V + 0 ≤ V by linarith) o) =
      y.2.2 (0 + u) (intervalTranslate (a := 0) le_rfl (show (0 : ℝ) + 0 ≤ W by linarith) o)
    rw [zero_add, hend, hstart]
    exact hm
  have hq' : IsWaveIntegral hU (le_refl (0 : ℝ)) e Λ
      (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) E p.1) (p.2.1 ⟨0, le_rfl, hU⟩)
      (E.compLpL 2 (volume.restrict (Icc 0 U)) p.2.2) q := by
    rw [hz0, hv0, hu0]
    exact hq
  have hpeq : p = q := huniq hU (le_refl (0 : ℝ)) hUd hd.le _ _ _ p q hp hq'
    (fun u v => hxr _ _) (fun u v => hyr _ _)
    ((waveTranslate_norm_le _ _ _ _ x).trans hxn) ((waveTranslate_norm_le _ _ _ _ y).trans hyn)
  have hw (u : Icc 0 U) : x.2.1 u ⟨V, hV, le_rfl⟩ = y.2.1 u ⟨0, le_rfl, hW⟩ := by
    have he := congrArg (fun s : WaveState U 0 => s.2.1 u o) hpeq
    change x.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by linarith) u)
      (intervalTranslate hV (show V + 0 ≤ V by linarith) o) =
        y.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by linarith) u)
          (intervalTranslate (a := 0) le_rfl (show (0 : ℝ) + 0 ≤ W by linarith) o) at he
    simpa only [hleft, hend, hstart] using he
  exact hx.splice hy hz hw hdu

theorem waveSplice_restrict_left {U V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (x : WaveState U V) (y : WaveState U W) :
    waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith)
      le_rfl (by linarith) (waveSplice hV hW x y) = x := by
  have hleft (u : Icc 0 U) : intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by linarith) u = u :=
    Subtype.ext (zero_add _)
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change intervalSplice hV hW (x.1 (intervalTranslate (a := 0) le_rfl (by linarith) u))
      (y.1 (intervalTranslate (a := 0) le_rfl (by linarith) u)) (intervalTranslate (a := 0) le_rfl (by linarith) v) = _
    rw [intervalSplice_left, hleft]
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change intervalSplice hV hW (x.2.1 (intervalTranslate (a := 0) le_rfl (by linarith) u))
      (y.2.1 (intervalTranslate (a := 0) le_rfl (by linarith) u)) (intervalTranslate (a := 0) le_rfl (by linarith) v) = _
    rw [intervalSplice_left, hleft]
  · apply Lp.ext
    filter_upwards [transverseTranslate_ae (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith)
        le_rfl (by linarith) (intervalSpliceLp hV hW x.2.2 y.2.2), intervalSpliceLp_ae hV hW x.2.2 y.2.2]
      with u hu hs
    apply ContinuousMap.ext
    intro v
    change transverseTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith)
      le_rfl (by linarith) (intervalSpliceLp hV hW x.2.2 y.2.2) u v = x.2.2 u v
    rw [hu]
    change intervalSpliceLp hV hW x.2.2 y.2.2 (0 + u) (intervalTranslate (a := 0) le_rfl (by linarith) v) = _
    rw [zero_add, hs, intervalSplice_left]

theorem waveSplice_restrict_right {U V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (x : WaveState U V) (y : WaveState U W)
    (hz : ∀ u, x.1 u ⟨V, hV, le_rfl⟩ = y.1 u ⟨0, le_rfl, hW⟩)
    (hw : ∀ u, x.2.1 u ⟨V, hV, le_rfl⟩ = y.2.1 u ⟨0, le_rfl, hW⟩)
    (hd : ∀ᵐ u ∂volume.restrict (Icc 0 U), x.2.2 u ⟨V, hV, le_rfl⟩ = y.2.2 u ⟨0, le_rfl, hW⟩) :
    waveTranslate (a := 0) (U := U) (b := V) (V := W) le_rfl (by linarith)
      hV le_rfl (waveSplice hV hW x y) = y := by
  have hleft (u : Icc 0 U) : intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by linarith) u = u :=
    Subtype.ext (zero_add _)
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change intervalSplice hV hW (x.1 (intervalTranslate (a := 0) le_rfl (by linarith) u))
      (y.1 (intervalTranslate (a := 0) le_rfl (by linarith) u)) (intervalTranslate hV le_rfl v) = _
    rw [intervalSplice_right_of_match hV hW _ _ (hz _), hleft]
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change intervalSplice hV hW (x.2.1 (intervalTranslate (a := 0) le_rfl (by linarith) u))
      (y.2.1 (intervalTranslate (a := 0) le_rfl (by linarith) u)) (intervalTranslate hV le_rfl v) = _
    rw [intervalSplice_right_of_match hV hW _ _ (hw _), hleft]
  · apply Lp.ext
    filter_upwards [transverseTranslate_ae (a := 0) (U := U) (V := W) le_rfl (by linarith)
        hV le_rfl (intervalSpliceLp hV hW x.2.2 y.2.2), intervalSpliceLp_ae hV hW x.2.2 y.2.2, hd]
      with u hu hs hm
    apply ContinuousMap.ext
    intro v
    change transverseTranslate (a := 0) (U := U) (V := W) le_rfl (by linarith)
      hV le_rfl (intervalSpliceLp hV hW x.2.2 y.2.2) u v = y.2.2 u v
    rw [hu]
    change intervalSpliceLp hV hW x.2.2 y.2.2 (0 + u) (intervalTranslate hV le_rfl v) = _
    rw [zero_add, hs, intervalSplice_right_of_match hV hW _ _ hm]

end CauchyHorizon
