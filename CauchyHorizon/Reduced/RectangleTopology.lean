import CauchyHorizon.Analysis.IntervalTopology
import CauchyHorizon.Reduced.LocalPasting
import CauchyHorizon.Reduced.HorizontalPasting
import CauchyHorizon.Reduced.RestrictionComposition

/-! Adjacent restrictions determine convergence in the mixed characteristic state norm. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

theorem continuous_waveTranslate {A B a b U V : ℝ}
    (ha : 0 ≤ a) (haU : a + U ≤ A) (hb : 0 ≤ b) (hbV : b + V ≤ B) :
    Continuous (waveTranslate ha haU hb hbV) := by
  have hr : Continuous (rectangleTranslate ha haU hb hbV) :=
    (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
      (ContinuousMap.compCLM ℝ WaveVector (intervalTranslate hb hbV))).continuous.comp
        (ContinuousMap.compCLM ℝ C(Icc 0 B, WaveVector) (intervalTranslate ha haU)).continuous
  have ht : Continuous (transverseTranslate ha haU hb hbV) :=
    ((ContinuousMap.compCLM ℝ WaveVector (intervalTranslate hb hbV)).compLpL 2
      (volume.restrict (Icc 0 U))).continuous.comp (continuous_intervalTranslateLp ha haU)
  exact (hr.comp continuous_fst).prodMk
    ((hr.comp (continuous_fst.comp continuous_snd)).prodMk (ht.comp (continuous_snd.comp continuous_snd)))

theorem continuous_waveSplice {U V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W) :
    Continuous (fun p : WaveState U V × WaveState U W => waveSplice hV hW p.1 p.2) := by
  unfold waveSplice rectangleSplice intervalSpliceLp
  fun_prop

theorem continuous_waveJoin {U W V : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W) :
    Continuous (fun p : WaveState U V × WaveState W V => waveJoin hU hW p.1 p.2) := by
  unfold waveJoin intervalSplice
  apply Continuous.prodMk
  · fun_prop
  apply Continuous.prodMk
  · fun_prop
  exact (continuous_intervalJoinLp hU hW).comp
    ((continuous_fst.snd.snd).prodMk (continuous_snd.snd.snd))

theorem waveSplice_reassemble {U V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (x : WaveState U (V + W)) :
    waveSplice hV hW
      (waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) x)
      (waveTranslate (a := 0) (U := U) (V := W) le_rfl (by simp) hV le_rfl x) = x := by
  apply waveTranslate_ext_vertical hV hW
  · rw [waveSplice_restrict_left]
  apply waveSplice_restrict_right
  · intro u
    change x.1 _ _ = x.1 _ _
    exact congrArg (x.1 _) (Subtype.ext (by simp [intervalTranslate]))
  · intro u
    change x.2.1 _ _ = x.2.1 _ _
    exact congrArg (x.2.1 _) (Subtype.ext (by simp [intervalTranslate]))
  · filter_upwards [transverseTranslate_ae (a := 0) (U := U) (b := 0) (V := V)
        le_rfl (by simp) le_rfl (by linarith) x.2.2,
      transverseTranslate_ae (a := 0) (U := U) (V := W) le_rfl (by simp) hV le_rfl x.2.2] with u hl hr
    change transverseTranslate _ _ _ _ x.2.2 u _ = transverseTranslate _ _ _ _ x.2.2 u _
    rw [hl, hr]
    change x.2.2 (0 + u) _ = x.2.2 (0 + u) _
    congr 1
    exact Subtype.ext (by simp [intervalTranslate])

theorem waveJoin_reassemble {U W V : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W)
    (x : WaveState (U + W) V) :
    waveJoin hU hW
      (waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) x)
      (waveTranslate (U := W) (b := 0) (V := V) hU le_rfl le_rfl (by simp) x) = x := by
  apply waveTranslate_ext_horizontal hU hW
  · rw [waveJoin_restrict_left]
  apply waveJoin_restrict_right
  · apply ContinuousMap.ext
    intro v
    change x.1 _ _ = x.1 _ _
    exact congrArg (fun u => x.1 u _) (Subtype.ext (by simp [intervalTranslate]))
  · apply ContinuousMap.ext
    intro v
    change x.2.1 _ _ = x.2.1 _ _
    exact congrArg (fun u => x.2.1 u _) (Subtype.ext (by simp [intervalTranslate]))

theorem waveTranslate_tendsto_vertical {ι : Type*} {l : Filter ι} {U V W : ℝ}
    (hV : 0 ≤ V) (hW : 0 ≤ W) {x : ι → WaveState U (V + W)} {y : WaveState U (V + W)}
    (hl : Tendsto (fun i => waveTranslate (a := 0) (U := U) (b := 0) (V := V)
      le_rfl (by simp) le_rfl (by linarith) (x i)) l
      (𝓝 (waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) y)))
    (hr : Tendsto (fun i => waveTranslate (a := 0) (U := U) (V := W)
      le_rfl (by simp) hV le_rfl (x i)) l
      (𝓝 (waveTranslate (a := 0) (U := U) (V := W) le_rfl (by simp) hV le_rfl y))) :
    Tendsto x l (𝓝 y) := by
  have hh := (continuous_waveSplice hV hW).tendsto _ |>.comp (hl.prodMk_nhds hr)
  simpa only [Function.comp_def, waveSplice_reassemble] using hh

theorem waveTranslate_tendsto_horizontal {ι : Type*} {l : Filter ι} {U W V : ℝ}
    (hU : 0 ≤ U) (hW : 0 ≤ W) {x : ι → WaveState (U + W) V} {y : WaveState (U + W) V}
    (hl : Tendsto (fun i => waveTranslate (a := 0) (U := U) (b := 0) (V := V)
      le_rfl (by linarith) le_rfl (by simp) (x i)) l
      (𝓝 (waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) y)))
    (hr : Tendsto (fun i => waveTranslate (U := W) (b := 0) (V := V)
      hU le_rfl le_rfl (by simp) (x i)) l
      (𝓝 (waveTranslate (U := W) (b := 0) (V := V) hU le_rfl le_rfl (by simp) y))) :
    Tendsto x l (𝓝 y) := by
  have hh := (continuous_waveJoin hU hW).tendsto _ |>.comp (hl.prodMk_nhds hr)
  simpa only [Function.comp_def, waveJoin_reassemble] using hh

end CauchyHorizon
