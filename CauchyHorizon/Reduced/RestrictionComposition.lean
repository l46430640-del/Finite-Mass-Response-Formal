import CauchyHorizon.Reduced.RectangleRestriction
import CauchyHorizon.Analysis.IntervalJoin

/-! Composition and adjacent-rectangle extensionality for actual mixed states. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

@[simp] theorem waveTranslate_zero {U V : ℝ} (x : WaveState U V) :
    waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp) le_rfl (by simp) x = x := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change x.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u)
      (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by simp) v) = x.1 u v
    simp only [intervalTranslate_zero, ContinuousMap.id_apply]
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change x.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u)
      (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by simp) v) = x.2.1 u v
    simp only [intervalTranslate_zero, ContinuousMap.id_apply]
  · apply Lp.ext
    filter_upwards [transverseTranslate_ae (a := 0) (U := U) (b := 0) (V := V)
      le_rfl (by simp) le_rfl (by simp) x.2.2] with u hu
    change transverseTranslate (a := 0) (U := U) (b := 0) (V := V)
      le_rfl (by simp) le_rfl (by simp) x.2.2 u = x.2.2 u
    simpa only [zero_add, intervalTranslate_zero, ContinuousMap.comp_id] using hu

theorem waveTranslate_comp {A B U V W H a b c d : ℝ}
    (ha : 0 ≤ a) (haU : a + U ≤ A) (hb : 0 ≤ b) (hbV : b + V ≤ B)
    (hc : 0 ≤ c) (hcW : c + W ≤ U) (hd : 0 ≤ d) (hdH : d + H ≤ V) (x : WaveState A B) :
    waveTranslate hc hcW hd hdH (waveTranslate ha haU hb hbV x) =
      waveTranslate (add_nonneg ha hc) (show (a + c) + W ≤ A by linarith)
        (add_nonneg hb hd) (show (b + d) + H ≤ B by linarith) x := by
  have hu (u : Icc 0 W) : intervalTranslate ha haU (intervalTranslate hc hcW u) =
      intervalTranslate (add_nonneg ha hc) (show (a + c) + W ≤ A by linarith) u :=
    Subtype.ext (add_assoc _ _ _).symm
  have hv (v : Icc 0 H) : intervalTranslate hb hbV (intervalTranslate hd hdH v) =
      intervalTranslate (add_nonneg hb hd) (show (b + d) + H ≤ B by linarith) v :=
    Subtype.ext (add_assoc _ _ _).symm
  apply Prod.ext
  · exact ContinuousMap.ext (fun u => ContinuousMap.ext (fun v => by change x.1 _ _ = x.1 _ _; rw [hu, hv]))
  apply Prod.ext
  · exact ContinuousMap.ext (fun u => ContinuousMap.ext (fun v => by change x.2.1 _ _ = x.2.1 _ _; rw [hu, hv]))
  · apply Lp.ext
    filter_upwards [transverseTranslate_ae hc hcW hd hdH (transverseTranslate ha haU hb hbV x.2.2),
      intervalTranslate_ae hc hcW (transverseTranslate_ae ha haU hb hbV x.2.2),
      transverseTranslate_ae (add_nonneg ha hc) (show (a + c) + W ≤ A by linarith)
        (add_nonneg hb hd) (show (b + d) + H ≤ B by linarith) x.2.2] with u ho hi ht
    change transverseTranslate hc hcW hd hdH (transverseTranslate ha haU hb hbV x.2.2) u =
      transverseTranslate (add_nonneg ha hc) (show (a + c) + W ≤ A by linarith)
        (add_nonneg hb hd) (show (b + d) + H ≤ B by linarith) x.2.2 u
    rw [ho, hi, ht]
    apply ContinuousMap.ext
    intro v
    change x.2.2 (a + (c + u)) _ = x.2.2 ((a + c) + u) _
    rw [← add_assoc, hv]

theorem waveTranslate_ext_horizontal {A W V : ℝ} (hA : 0 ≤ A) (hW : 0 ≤ W)
    {x y : WaveState (A + W) V}
    (hl : waveTranslate (a := 0) (U := A) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) x =
      waveTranslate (a := 0) (U := A) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) y)
    (hr : waveTranslate (a := A) (U := W) (b := 0) (V := V) hA le_rfl le_rfl (by simp) x =
      waveTranslate (a := A) (U := W) (b := 0) (V := V) hA le_rfl le_rfl (by simp) y) : x = y := by
  have hzl := congrArg Prod.fst hl
  have hzr := congrArg Prod.fst hr
  have hwl := congrArg (fun s : WaveState A V => s.2.1) hl
  have hwr := congrArg (fun s : WaveState W V => s.2.1) hr
  simp only [waveTranslate, rectangleTranslate, intervalTranslate_zero,
    ContinuousLinearMap.compLeftContinuous_apply] at hzl hzr hwl hwr
  apply Prod.ext
  · exact continuousMap_ext_adjacent hA hW (fun u => congrArg (fun f => f u) hzl)
      (fun u => congrArg (fun f => f u) hzr)
  apply Prod.ext
  · exact continuousMap_ext_adjacent hA hW (fun u => congrArg (fun f => f u) hwl)
      (fun u => congrArg (fun f => f u) hwr)
  · have hdl := congrArg (fun s : WaveState A V => s.2.2) hl
    have hdr := congrArg (fun s : WaveState W V => s.2.2) hr
    apply Lp.ext
    apply intervalJoin_ae hA hW
    · filter_upwards [transverseTranslate_ae (a := 0) (U := A) (b := 0) (V := V)
        le_rfl (by linarith) le_rfl (by simp) x.2.2,
        transverseTranslate_ae (a := 0) (U := A) (b := 0) (V := V)
        le_rfl (by linarith) le_rfl (by simp) y.2.2] with u hx hy
      have he := congrArg (fun f : WaveTransverse A V => f u) hdl
      change transverseTranslate _ _ _ _ x.2.2 u = transverseTranslate _ _ _ _ y.2.2 u at he
      simpa only [hx, hy, zero_add, intervalTranslate_zero, ContinuousMap.comp_id] using he
    · filter_upwards [transverseTranslate_ae (a := A) (U := W) (b := 0) (V := V)
        hA le_rfl le_rfl (by simp) x.2.2,
        transverseTranslate_ae (a := A) (U := W) (b := 0) (V := V)
        hA le_rfl le_rfl (by simp) y.2.2] with u hx hy
      have he := congrArg (fun f : WaveTransverse W V => f u) hdr
      change transverseTranslate _ _ _ _ x.2.2 u = transverseTranslate _ _ _ _ y.2.2 u at he
      simpa only [hx, hy, intervalTranslate_zero, ContinuousMap.comp_id] using he

theorem waveTranslate_ext_vertical {U V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    {x y : WaveState U (V + W)}
    (hl : waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) x =
      waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) y)
    (hr : waveTranslate (a := 0) (U := U) (b := V) (V := W) le_rfl (by simp) hV le_rfl x =
      waveTranslate (a := 0) (U := U) (b := V) (V := W) le_rfl (by simp) hV le_rfl y) : x = y := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply continuousMap_ext_adjacent hV hW
    · intro v
      have he := congrArg (fun s : WaveState U V => s.1 u v) hl
      change x.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u) _ =
        y.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u) _ at he
      simpa only [intervalTranslate_zero, ContinuousMap.id_apply] using he
    · intro v
      have he := congrArg (fun s : WaveState U W => s.1 u v) hr
      change x.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u) _ =
        y.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u) _ at he
      simpa only [intervalTranslate_zero, ContinuousMap.id_apply] using he
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply continuousMap_ext_adjacent hV hW
    · intro v
      have he := congrArg (fun s : WaveState U V => s.2.1 u v) hl
      change x.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u) _ =
        y.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u) _ at he
      simpa only [intervalTranslate_zero, ContinuousMap.id_apply] using he
    · intro v
      have he := congrArg (fun s : WaveState U W => s.2.1 u v) hr
      change x.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u) _ =
        y.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) u) _ at he
      simpa only [intervalTranslate_zero, ContinuousMap.id_apply] using he
  · have hdl := congrArg (fun s : WaveState U V => s.2.2) hl
    have hdr := congrArg (fun s : WaveState U W => s.2.2) hr
    apply Lp.ext
    filter_upwards [transverseTranslate_ae (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) x.2.2,
      transverseTranslate_ae (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) y.2.2,
      transverseTranslate_ae (a := 0) (U := U) (b := V) (V := W) le_rfl (by simp) hV le_rfl x.2.2,
      transverseTranslate_ae (a := 0) (U := U) (b := V) (V := W) le_rfl (by simp) hV le_rfl y.2.2] with u hxl hyl hxr hyr
    apply continuousMap_ext_adjacent hV hW
    · intro v
      have he := congrArg (fun f : WaveTransverse U V => f u v) hdl
      change transverseTranslate _ _ _ _ x.2.2 u v = transverseTranslate _ _ _ _ y.2.2 u v at he
      simpa only [hxl, hyl, zero_add, ContinuousMap.comp_apply] using he
    · intro v
      have he := congrArg (fun f : WaveTransverse U W => f u v) hdr
      change transverseTranslate _ _ _ _ x.2.2 u v = transverseTranslate _ _ _ _ y.2.2 u v at he
      simpa only [hxr, hyr, zero_add, ContinuousMap.comp_apply] using he

end CauchyHorizon
