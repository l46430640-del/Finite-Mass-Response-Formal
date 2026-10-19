import CauchyHorizon.Analysis.IntervalJoin
import CauchyHorizon.Reduced.RectangleRestriction

/-! Horizontal characteristic pasting keeps transverse derivatives as L2 classes. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U W V : ℝ}

noncomputable def waveJoin (hU : 0 ≤ U) (hW : 0 ≤ W)
    (x : WaveState U V) (y : WaveState W V) : WaveState (U + W) V :=
  (intervalSplice hU hW x.1 y.1, intervalSplice hU hW x.2.1 y.2.1, intervalJoinLp hW x.2.2 y.2.2)

theorem waveJoin_radius (hU : 0 ≤ U) (hW : 0 ≤ W)
    (x : WaveState U V) (y : WaveState W V)
    (hx : ∀ u v, x.1 u v 0 ≠ 0) (hy : ∀ u v, y.1 u v 0 ≠ 0)
    (hz : x.1 ⟨U, hU, le_rfl⟩ = y.1 ⟨0, le_rfl, hW⟩) :
    ∀ u v, (waveJoin hU hW x y).1 u v 0 ≠ 0 := by
  intro u v
  change intervalSplice hU hW x.1 y.1 u v 0 ≠ 0
  by_cases hu : (u : ℝ) ≤ U
  · let t : Icc 0 U := ⟨u, u.property.1, hu⟩
    have he : intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U + W by linarith) t = u :=
      Subtype.ext (by simp [intervalTranslate, t])
    rw [← he, intervalSplice_left]
    exact hx t v
  · let t : Icc 0 W := ⟨u - U, by linarith, by linarith [u.property.2]⟩
    have he : intervalTranslate hU (le_refl (U + W)) t = u := Subtype.ext (by dsimp [intervalTranslate, t]; ring)
    rw [← he, intervalSplice_right_of_match hU hW _ _ hz]
    exact hy t v

theorem rectangleSource_join (hU : 0 ≤ U) (hW : 0 ≤ W) (e Λ : ℝ)
    (x : WaveState U V) (y : WaveState W V)
    (rx : ∀ u v, x.1 u v 0 ≠ 0) (ry : ∀ u v, y.1 u v 0 ≠ 0)
    (hz : x.1 ⟨U, hU, le_rfl⟩ = y.1 ⟨0, le_rfl, hW⟩)
    (hw : x.2.1 ⟨U, hU, le_rfl⟩ = y.2.1 ⟨0, le_rfl, hW⟩) :
    rectangleSource (add_nonneg hU hW) e Λ (waveJoin hU hW x y) (waveJoin_radius hU hW x y rx ry hz) =
      intervalJoinLp hW (rectangleSource hU e Λ x rx) (rectangleSource hW e Λ y ry) := by
  let hS := rectangleSource_ae (add_nonneg hU hW) e Λ (waveJoin hU hW x y) (waveJoin_radius hU hW x y rx ry hz)
  apply Lp.ext
  apply intervalJoin_ae hU hW
  · have hs : Icc 0 U ⊆ Icc 0 (U + W) := Icc_subset_Icc le_rfl (by linarith)
    filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) hS,
      rectangleSource_ae hU e Λ x rx, intervalJoinLp_left hW x.2.2 y.2.2,
      intervalJoinLp_left hW (rectangleSource hU e Λ x rx) (rectangleSource hW e Λ y ry),
      ae_restrict_mem measurableSet_Icc] with u hS hx hd hF hu
    have he : projIcc 0 (U + W) (add_nonneg hU hW) u =
        intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U + W by linarith) (projIcc 0 U hU u) := by
      apply Subtype.ext
      simp only [projIcc_of_mem hU hu, projIcc_of_mem (add_nonneg hU hW) (hs hu), intervalTranslate, zero_add]
      rfl
    apply ContinuousMap.ext
    intro v
    rw [hF, hS v, hx v]
    change waveSource e Λ (intervalSplice hU hW x.1 y.1 _ v)
      (intervalJoinLp hW x.2.2 y.2.2 u v) (intervalSplice hU hW x.2.1 y.2.1 _ v) = _
    rw [he, intervalSplice_left, intervalSplice_left, hd]
  · filter_upwards [intervalTranslate_ae hU (le_refl (U + W)) hS,
      rectangleSource_ae hW e Λ y ry, intervalJoinLp_right hU hW x.2.2 y.2.2,
      intervalJoinLp_right hU hW (rectangleSource hU e Λ x rx) (rectangleSource hW e Λ y ry),
      ae_restrict_mem measurableSet_Icc] with u hS hy hd hF hu
    have he : projIcc 0 (U + W) (add_nonneg hU hW) (U + u) =
        intervalTranslate hU (le_refl (U + W)) (projIcc 0 W hW u) := by
      apply Subtype.ext
      have ht : U + u ∈ Icc 0 (U + W) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      simp only [projIcc_of_mem hW hu, projIcc_of_mem (add_nonneg hU hW) ht, intervalTranslate]
      rfl
    apply ContinuousMap.ext
    intro v
    rw [hF, hS v, hy v]
    change waveSource e Λ (intervalSplice hU hW x.1 y.1 _ v)
      (intervalJoinLp hW x.2.2 y.2.2 (U + u) v) (intervalSplice hU hW x.2.1 y.2.1 _ v) = _
    rw [he, intervalSplice_right_of_match hU hW _ _ hz, intervalSplice_right_of_match hU hW _ _ hw, hd]

theorem IsWaveIntegral.join {hU : 0 ≤ U} {hW : 0 ≤ W} {hV : 0 ≤ V} {e Λ : ℝ}
    {zx : C(Icc 0 U, WaveVector)} {zy : C(Icc 0 W, WaveVector)} {vx vy : C(Icc 0 V, WaveVector)}
    {ux : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {uy : Lp WaveVector 2 (volume.restrict (Icc 0 W))}
    {x : WaveState U V} {y : WaveState W V}
    (hx : IsWaveIntegral hU hV e Λ zx vx ux x) (hy : IsWaveIntegral hW hV e Λ zy vy uy y)
    (hz : x.1 ⟨U, hU, le_rfl⟩ = y.1 ⟨0, le_rfl, hW⟩)
    (hw : x.2.1 ⟨U, hU, le_rfl⟩ = y.2.1 ⟨0, le_rfl, hW⟩) :
    IsWaveIntegral (add_nonneg hU hW) hV e Λ (intervalSplice hU hW zx zy) vx
      (intervalJoinLp hW ux uy) (waveJoin hU hW x y) := by
  let F := rectangleSource hU e Λ x hx.choose
  let G := rectangleSource hW e Λ y hy.choose
  let z := waveJoin hU hW x y
  have hr : ∀ u v, z.1 u v 0 ≠ 0 := waveJoin_radius hU hW x y hx.choose hy.choose hz
  have hsource := rectangleSource_join hU hW e Λ x y hx.choose hy.choose hz hw
  change rectangleSource (add_nonneg hU hW) e Λ z hr = intervalJoinLp hW F G at hsource
  have hxf : incomingField zx + longitudinalIntegral hV x.2.1 = x.1 := congrArg Prod.fst hx.choose_spec
  have hyf : incomingField zy + longitudinalIntegral hV y.2.1 = y.1 := congrArg Prod.fst hy.choose_spec
  have hxw : ContinuousMap.const _ vx + horizontalPrimitive hU F = x.2.1 :=
    congrArg (fun s : WaveState U V => s.2.1) hx.choose_spec
  have hyw : ContinuousMap.const _ vy + horizontalPrimitive hW G = y.2.1 :=
    congrArg (fun s : WaveState W V => s.2.1) hy.choose_spec
  have hxd : incomingTransverse ux + verticalPrimitive hV F = x.2.2 :=
    congrArg (fun s : WaveState U V => s.2.2) hx.choose_spec
  have hyd : incomingTransverse uy + verticalPrimitive hV G = y.2.2 :=
    congrArg (fun s : WaveState W V => s.2.2) hy.choose_spec
  refine ⟨hr, ?_⟩
  apply Prod.ext
  · change ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 (U + W))
        (ContinuousLinearMap.const ℝ (Icc 0 V)) (intervalSplice hU hW zx zy) +
      ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 (U + W)) (continuousPrimitiveL hV)
        (intervalSplice hU hW x.2.1 y.2.1) = intervalSplice hU hW x.1 y.1
    rw [intervalSplice_comp, intervalSplice_comp, ← intervalSplice_add]
    change intervalSplice hU hW (incomingField zx + longitudinalIntegral hV x.2.1)
      (incomingField zy + longitudinalIntegral hV y.2.1) = _
    rw [hxf, hyf]
  apply Prod.ext
  · change ContinuousMap.const _ vx + horizontalPrimitive (add_nonneg hU hW)
      (rectangleSource (add_nonneg hU hW) e Λ z hr) = intervalSplice hU hW x.2.1 y.2.1
    rw [hsource, horizontalPrimitive_join, ← hxw, ← hyw, intervalSplice_add, intervalSplice_const]
  · change incomingTransverse (intervalJoinLp hW ux uy) + verticalPrimitive hV
      (rectangleSource (add_nonneg hU hW) e Λ z hr) = intervalJoinLp hW x.2.2 y.2.2
    rw [hsource, ← hxd, ← hyd, intervalJoinLp_add hU hW]
    change (ContinuousLinearMap.const ℝ (Icc 0 V)).compLpL 2 _ (intervalJoinLp hW ux uy) +
      (continuousPrimitiveL hV).compLpL 2 _ (intervalJoinLp hW F G) = _
    rw [intervalJoinLp_comp hU hW, intervalJoinLp_comp hU hW]
    rfl

theorem IsWaveIntegral.horizontal_match {hU : 0 ≤ U} {hW : 0 ≤ W} {hV : 0 ≤ V} {e Λ : ℝ}
    {zx : C(Icc 0 U, WaveVector)} {zy : C(Icc 0 W, WaveVector)} {vx vy : C(Icc 0 V, WaveVector)}
    {ux : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {uy : Lp WaveVector 2 (volume.restrict (Icc 0 W))}
    {x : WaveState U V} {y : WaveState W V}
    (hx : IsWaveIntegral hU hV e Λ zx vx ux x) (hy : IsWaveIntegral hW hV e Λ zy vy uy y)
    (hv : vy = x.2.1 ⟨U, hU, le_rfl⟩) (hc : zx ⟨U, hU, le_rfl⟩ = zy ⟨0, le_rfl, hW⟩) :
    x.1 ⟨U, hU, le_rfl⟩ = y.1 ⟨0, le_rfl, hW⟩ ∧
      x.2.1 ⟨U, hU, le_rfl⟩ = y.2.1 ⟨0, le_rfl, hW⟩ := by
  have hyout := waveIteration_outgoing_derivative hW hV e Λ zy vy uy y hy.choose
  rw [hy.choose_spec] at hyout
  have hw : x.2.1 ⟨U, hU, le_rfl⟩ = y.2.1 ⟨0, le_rfl, hW⟩ := hv.symm.trans hyout.symm
  have hxf : ContinuousMap.const _ (zx ⟨U, hU, le_rfl⟩) + continuousPrimitive hV (x.2.1 ⟨U, hU, le_rfl⟩) =
      x.1 ⟨U, hU, le_rfl⟩ := congrArg (fun s : WaveState U V => s.1 ⟨U, hU, le_rfl⟩) hx.choose_spec
  have hyf : ContinuousMap.const _ (zy ⟨0, le_rfl, hW⟩) + continuousPrimitive hV (y.2.1 ⟨0, le_rfl, hW⟩) =
      y.1 ⟨0, le_rfl, hW⟩ := congrArg (fun s : WaveState W V => s.1 ⟨0, le_rfl, hW⟩) hy.choose_spec
  refine ⟨?_, hw⟩
  rw [← hxf, ← hyf, hc, hw]

theorem IsWaveIntegral.join_of_data {hU : 0 ≤ U} {hW : 0 ≤ W} {hV : 0 ≤ V} {e Λ : ℝ}
    {zx : C(Icc 0 U, WaveVector)} {zy : C(Icc 0 W, WaveVector)} {vx vy : C(Icc 0 V, WaveVector)}
    {ux : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {uy : Lp WaveVector 2 (volume.restrict (Icc 0 W))}
    {x : WaveState U V} {y : WaveState W V}
    (hx : IsWaveIntegral hU hV e Λ zx vx ux x) (hy : IsWaveIntegral hW hV e Λ zy vy uy y)
    (hv : vy = x.2.1 ⟨U, hU, le_rfl⟩) (hc : zx ⟨U, hU, le_rfl⟩ = zy ⟨0, le_rfl, hW⟩) :
    IsWaveIntegral (add_nonneg hU hW) hV e Λ (intervalSplice hU hW zx zy) vx
      (intervalJoinLp hW ux uy) (waveJoin hU hW x y) :=
  hx.join hy (hx.horizontal_match hy hv hc).1 (hx.horizontal_match hy hv hc).2

theorem joined_incoming_primitive (hU : 0 ≤ U) (hW : 0 ≤ W)
    {zx : C(Icc 0 U, WaveVector)} {zy : C(Icc 0 W, WaveVector)} {cx cy : WaveVector}
    {ux : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {uy : Lp WaveVector 2 (volume.restrict (Icc 0 W))}
    (hx : zx = ContinuousMap.const _ cx + horizontalPrimitive hU ux)
    (hy : zy = ContinuousMap.const _ cy + horizontalPrimitive hW uy) :
    intervalSplice hU hW zx zy = ContinuousMap.const _ cx +
      horizontalPrimitive (add_nonneg hU hW) (intervalJoinLp hW ux uy) := by
  rw [hx, hy, intervalSplice_add, intervalSplice_const, horizontalPrimitive_join]

theorem waveJoin_restrict_left (hU : 0 ≤ U) (hW : 0 ≤ W)
    (x : WaveState U V) (y : WaveState W V) :
    waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith)
      le_rfl (by linarith) (waveJoin hU hW x y) = x := by
  have hv (v : Icc 0 V) : intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by linarith) v = v :=
    Subtype.ext (zero_add _)
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change intervalSplice hU hW x.1 y.1 (intervalTranslate (a := 0) le_rfl (by linarith) u)
      (intervalTranslate (a := 0) le_rfl (by linarith) v) = _
    rw [intervalSplice_left, hv]
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change intervalSplice hU hW x.2.1 y.2.1 (intervalTranslate (a := 0) le_rfl (by linarith) u)
      (intervalTranslate (a := 0) le_rfl (by linarith) v) = _
    rw [intervalSplice_left, hv]
  · apply Lp.ext
    filter_upwards [transverseTranslate_ae (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith)
      le_rfl (by linarith) (intervalJoinLp hW x.2.2 y.2.2), intervalJoinLp_left hW x.2.2 y.2.2] with u hu hj
    apply ContinuousMap.ext
    intro v
    change transverseTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith)
      le_rfl (by linarith) (intervalJoinLp hW x.2.2 y.2.2) u v = x.2.2 u v
    rw [hu]
    change intervalJoinLp hW x.2.2 y.2.2 (0 + u) (intervalTranslate (a := 0) le_rfl (by linarith) v) = _
    rw [zero_add, hj, hv]

theorem waveJoin_restrict_right (hU : 0 ≤ U) (hW : 0 ≤ W)
    (x : WaveState U V) (y : WaveState W V)
    (hz : x.1 ⟨U, hU, le_rfl⟩ = y.1 ⟨0, le_rfl, hW⟩)
    (hw : x.2.1 ⟨U, hU, le_rfl⟩ = y.2.1 ⟨0, le_rfl, hW⟩) :
    waveTranslate (a := U) (U := W) (b := 0) (V := V) hU le_rfl
      le_rfl (by linarith) (waveJoin hU hW x y) = y := by
  have hv (v : Icc 0 V) : intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by linarith) v = v :=
    Subtype.ext (zero_add _)
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change intervalSplice hU hW x.1 y.1 (intervalTranslate hU le_rfl u)
      (intervalTranslate (a := 0) le_rfl (by linarith) v) = _
    rw [intervalSplice_right_of_match hU hW _ _ hz, hv]
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    apply ContinuousMap.ext
    intro v
    change intervalSplice hU hW x.2.1 y.2.1 (intervalTranslate hU le_rfl u)
      (intervalTranslate (a := 0) le_rfl (by linarith) v) = _
    rw [intervalSplice_right_of_match hU hW _ _ hw, hv]
  · apply Lp.ext
    filter_upwards [transverseTranslate_ae (a := U) (U := W) (b := 0) (V := V) hU le_rfl
      le_rfl (by linarith) (intervalJoinLp hW x.2.2 y.2.2), intervalJoinLp_right hU hW x.2.2 y.2.2] with u hu hj
    apply ContinuousMap.ext
    intro v
    change transverseTranslate (a := U) (U := W) (b := 0) (V := V) hU le_rfl
      le_rfl (by linarith) (intervalJoinLp hW x.2.2 y.2.2) u v = y.2.2 u v
    rw [hu]
    change intervalJoinLp hW x.2.2 y.2.2 (U + u) (intervalTranslate (a := 0) le_rfl (by linarith) v) = _
    rw [hj, hv]

theorem exists_horizontal_wave_extension (e Λ ρ R M : ℝ)
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {U W V : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W) (hV : 0 ≤ V), W ≤ d → V ≤ d →
      ∀ (zx : C(Icc 0 U, WaveVector)) (vx : C(Icc 0 V, WaveVector))
        (ux : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x : WaveState U V),
        IsWaveIntegral hU hV e Λ zx vx ux x → ‖x‖ ≤ R →
      ∀ (zy : C(Icc 0 W, WaveVector)) (uy : Lp WaveVector 2 (volume.restrict (Icc 0 W))),
        (∀ u, ρ ≤ zy u 0) → ‖zy‖ ≤ R → ‖uy‖ ≤ M → zx ⟨U, hU, le_rfl⟩ = zy ⟨0, le_rfl, hW⟩ →
      ∃ y : WaveState W V,
        IsWaveIntegral hW hV e Λ zy (x.2.1 ⟨U, hU, le_rfl⟩) uy y ∧
        IsWaveIntegral (add_nonneg hU hW) hV e Λ (intervalSplice hU hW zx zy) vx
          (intervalJoinLp hW ux uy) (waveJoin hU hW x y) ∧
        waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith)
          le_rfl (by linarith) (waveJoin hU hW x y) = x ∧
        ∀ u v, ρ / 2 ≤ y.1 u v 0 := by
  obtain ⟨δ, _hδ, hδρ, d, hd, hd1, hsolve⟩ := exists_local_wave_integral e Λ (ρ / 2) R M (half_pos hρ) hR hM
  refine ⟨d, hd, hd1, ?_⟩
  intro U W V hU hW hV hWd hVd zx vx ux x hx hxn zy uy hzr hzn hun hc
  have hv : ‖x.2.1 ⟨U, hU, le_rfl⟩‖ ≤ R :=
    (x.2.1.norm_coe_le_norm _).trans (((norm_fst_le x.2).trans (norm_snd_le x)).trans hxn)
  obtain ⟨y, ⟨hyball, hy⟩, _hyuniq⟩ := hsolve hW hV hWd hVd zy (x.2.1 ⟨U, hU, le_rfl⟩) uy
    (fun u => (half_le_self hρ.le).trans (hzr u)) hzn hv hun
  refine ⟨y, hy, hx.join_of_data hy rfl hc, waveJoin_restrict_left hU hW x y, ?_⟩
  intro u v
  have hlo := (waveSeed_ball_range zy (x.2.1 ⟨U, hU, le_rfl⟩) uy hzr hzn hv hyball u v).1.1 0
  change ρ - δ ≤ y.1 u v 0 at hlo
  linarith

end CauchyHorizon
