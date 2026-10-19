import CauchyHorizon.Characteristic.PrefixData
import CauchyHorizon.Reduced.CornerExtension
import CauchyHorizon.Reduced.RestrictionComposition

/-! One step of a row preserves the whole lower rectangle and its incoming data. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_prefix_wave_extension (e Λ ρ M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {A W V H : ℝ} (hA : 0 ≤ A) (hW : 0 ≤ W) (hV : 0 ≤ V) (hH : 0 ≤ H), W ≤ d → H ≤ d →
      ∀ (zx : C(Icc 0 A, WaveVector)) (vx : C(Icc 0 (V + H), WaveVector))
        (ux : Lp WaveVector 2 (volume.restrict (Icc 0 A))) (x : WaveState A (V + H))
        (zy : C(Icc 0 (A + W), WaveVector)) (vy : C(Icc 0 V, WaveVector))
        (uy : Lp WaveVector 2 (volume.restrict (Icc 0 (A + W)))) (y : WaveState (A + W) V),
        IsWaveIntegral hA (add_nonneg hV hH) e Λ zx vx ux x →
        IsWaveIntegral (add_nonneg hA hW) hV e Λ zy vy uy y →
        ‖x‖ ≤ M → ‖y‖ ≤ M → (∀ u v, ρ / 2 ≤ x.1 u v 0) → (∀ u v, ρ ≤ y.1 u v 0) →
        waveTranslate (a := 0) (U := A) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) x =
          waveTranslate (a := 0) (U := A) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) y →
      ∃ s : WaveState (A + W) (V + H),
        IsWaveIntegral (add_nonneg hA hW) (add_nonneg hV hH) e Λ zy vx uy s ∧
        waveTranslate (a := 0) (U := A + W) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) s = y ∧
        waveTranslate (a := 0) (U := A) (b := 0) (V := V + H) le_rfl (by linarith) le_rfl (by simp) s = x ∧
        ∀ u v, ρ / 2 ≤ s.1 u v 0 := by
  obtain ⟨d, hd, hd1, hext⟩ := exists_corner_wave_extension e Λ ρ M hρ hM
  refine ⟨d, hd, hd1, ?_⟩
  intro A W V H hA hW hV hH hWd hHd zx vx ux x zy vy uy y hx hy hxn hyn hxr hyr hb
  let yr := waveTranslate (a := A) (U := W) (b := 0) (V := V) hA le_rfl le_rfl (show 0 + V ≤ V by simp) y
  have hyrsol := hy.translate hW hV hA (le_refl (A + W)) (b := 0) le_rfl (by simp)
  let al := intervalTranslate (a := 0) (U := A) le_rfl (show 0 + A ≤ A + W by linarith)
  let ar := intervalTranslate (a := A) (U := W) hA (le_refl (A + W))
  let bv := intervalTranslate (a := 0) (U := V) le_rfl (show 0 + V ≤ V + H by linarith)
  have haend : al ⟨A, hA, le_rfl⟩ = ar ⟨0, le_rfl, hW⟩ := Subtype.ext (by simp [al, ar, intervalTranslate])
  have hw : (x.2.1 ⟨A, hA, le_rfl⟩).comp bv = y.2.1 (al ⟨A, hA, le_rfl⟩) := by
    apply ContinuousMap.ext
    intro v
    have he := congrArg (fun t : WaveState A V => t.2.1 ⟨A, hA, le_rfl⟩ v) hb
    change x.2.1 (intervalTranslate (a := 0) (U := A) le_rfl (show 0 + A ≤ A by simp) ⟨A, hA, le_rfl⟩) (bv v) =
      y.2.1 (al ⟨A, hA, le_rfl⟩) (intervalTranslate (a := 0) (U := V) le_rfl (show 0 + V ≤ V by simp) v) at he
    simpa only [intervalTranslate_zero, ContinuousMap.id_apply, ContinuousMap.comp_apply] using he
  have hv : yr.2.1 ⟨0, le_rfl, hW⟩ = (x.2.1 ⟨A, hA, le_rfl⟩).comp bv := by
    change (y.2.1 (ar ⟨0, le_rfl, hW⟩)).comp
      (intervalTranslate (a := 0) (U := V) le_rfl (show 0 + V ≤ V by simp)) = _
    rw [intervalTranslate_zero, ContinuousMap.comp_id, ← haend]
    exact hw.symm
  have hcorner : zx ⟨A, hA, le_rfl⟩ = yr.1 ⟨0, le_rfl, hW⟩ ⟨0, le_rfl, hV⟩ := by
    have hz := waveIteration_incoming_value hA (add_nonneg hV hH) e Λ zx vx ux x hx.choose ⟨A, hA, le_rfl⟩
    rw [hx.choose_spec] at hz
    have he := congrArg (fun t : WaveState A V => t.1 ⟨A, hA, le_rfl⟩ ⟨0, le_rfl, hV⟩) hb
    change x.1 (intervalTranslate (a := 0) (U := A) le_rfl (show 0 + A ≤ A by simp) ⟨A, hA, le_rfl⟩)
      (bv ⟨0, le_rfl, hV⟩) = y.1 (al ⟨A, hA, le_rfl⟩)
      (intervalTranslate (a := 0) (U := V) le_rfl (show 0 + V ≤ V by simp) ⟨0, le_rfl, hV⟩) at he
    have hb0 : bv ⟨0, le_rfl, hV⟩ = ⟨0, le_rfl, add_nonneg hV hH⟩ := Subtype.ext (zero_add _)
    simp only [intervalTranslate_zero, ContinuousMap.id_apply, hb0, haend] at he
    change _ = y.1 (ar ⟨0, le_rfl, hW⟩)
      (intervalTranslate (a := 0) (U := V) le_rfl (show 0 + V ≤ V by simp) ⟨0, le_rfl, hV⟩)
    rw [intervalTranslate_zero, ContinuousMap.id_apply]
    exact hz.symm.trans he
  obtain ⟨z, _hz, hzb, _hzr, hs, hsl, hsr, hrad⟩ := hext hA hW hV hH hWd hHd zx vx ux x
    _ _ _ yr hx hyrsol hxn ((waveTranslate_norm_le _ _ _ _ y).trans hyn) hxr (fun u v => hyr _ _) hv hcorner
  let s := waveJoin hA hW x z
  have hbottom : waveTranslate (a := 0) (U := A + W) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) s = y := by
    apply waveTranslate_ext_horizontal hA hW
    · calc
        waveTranslate (a := 0) (U := A) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp)
            (waveTranslate (a := 0) (U := A + W) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) s) =
          waveTranslate (a := 0) (U := A) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith)
            (waveTranslate (a := 0) (U := A) (b := 0) (V := V + H) le_rfl (by linarith) le_rfl (by simp) s) := by
              simp only [waveTranslate_comp, zero_add]
        _ = _ := by rw [hsl, hb]
    · calc
        waveTranslate (a := A) (U := W) (b := 0) (V := V) hA le_rfl le_rfl (by simp)
            (waveTranslate (a := 0) (U := A + W) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) s) =
          waveTranslate (a := 0) (U := W) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith)
            (waveTranslate (a := A) (U := W) (b := 0) (V := V + H) hA le_rfl le_rfl (by simp) s) := by
              simp only [waveTranslate_comp, zero_add, add_zero]
        _ = _ := by rw [hsr, hzb]
  exact ⟨s, hs.of_vertical_prefix hV (by linarith) hy hbottom, hbottom, hsl, hrad⟩

end CauchyHorizon
