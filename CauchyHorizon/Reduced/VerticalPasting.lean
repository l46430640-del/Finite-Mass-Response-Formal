import CauchyHorizon.Reduced.IntegralRegularity
import CauchyHorizon.Analysis.IntervalSplice

/-! Pasting actual characteristic solutions across a common longitudinal edge. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V W : ℝ}

noncomputable def rectangleSplice (hV : 0 ≤ V) (hW : 0 ≤ W)
    (x : WaveRectangle U V) (y : WaveRectangle U W) : WaveRectangle U (V + W) :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (intervalSpliceLeft hV) x +
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (intervalSpliceRight V hW) y

noncomputable def waveSplice (hV : 0 ≤ V) (hW : 0 ≤ W)
    (x : WaveState U V) (y : WaveState U W) : WaveState U (V + W) :=
  (rectangleSplice hV hW x.1 y.1, rectangleSplice hV hW x.2.1 y.2.1,
    intervalSpliceLp hV hW x.2.2 y.2.2)

theorem waveSplice_radius (hV : 0 ≤ V) (hW : 0 ≤ W)
    (x : WaveState U V) (y : WaveState U W)
    (hx : ∀ u v, x.1 u v 0 ≠ 0) (hy : ∀ u v, y.1 u v 0 ≠ 0)
    (hz : ∀ u, x.1 u ⟨V, hV, le_rfl⟩ = y.1 u ⟨0, le_rfl, hW⟩) :
    ∀ u v, (waveSplice hV hW x y).1 u v 0 ≠ 0 := by
  intro u v
  change intervalSplice hV hW (x.1 u) (y.1 u) v 0 ≠ 0
  by_cases hv : (v : ℝ) ≤ V
  · let t : Icc 0 V := ⟨v, v.property.1, hv⟩
    have he : intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V + W by linarith) t = v :=
      Subtype.ext (by simp [intervalTranslate, t])
    rw [← he, intervalSplice_left]
    exact hx u t
  · let t : Icc 0 W := ⟨v - V, by linarith, by linarith [v.property.2]⟩
    have he : intervalTranslate hV (le_refl (V + W)) t = v := Subtype.ext (by dsimp [intervalTranslate, t]; ring)
    rw [← he, intervalSplice_right_of_match hV hW _ _ (hz u)]
    exact hy u t

theorem rectangleSource_splice (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (e Λ : ℝ)
    (x : WaveState U V) (y : WaveState U W)
    (rx : ∀ u v, x.1 u v 0 ≠ 0) (ry : ∀ u v, y.1 u v 0 ≠ 0)
    (hz : ∀ u, x.1 u ⟨V, hV, le_rfl⟩ = y.1 u ⟨0, le_rfl, hW⟩)
    (hw : ∀ u, x.2.1 u ⟨V, hV, le_rfl⟩ = y.2.1 u ⟨0, le_rfl, hW⟩)
    (hd : ∀ᵐ u ∂volume.restrict (Icc 0 U), x.2.2 u ⟨V, hV, le_rfl⟩ = y.2.2 u ⟨0, le_rfl, hW⟩) :
    (∀ᵐ u ∂volume.restrict (Icc 0 U),
      rectangleSource hU e Λ x rx u ⟨V, hV, le_rfl⟩ = rectangleSource hU e Λ y ry u ⟨0, le_rfl, hW⟩) ∧
    rectangleSource hU e Λ (waveSplice hV hW x y) (waveSplice_radius hV hW x y rx ry hz) =
      intervalSpliceLp hV hW (rectangleSource hU e Λ x rx) (rectangleSource hU e Λ y ry) := by
  have hm : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      rectangleSource hU e Λ x rx u ⟨V, hV, le_rfl⟩ = rectangleSource hU e Λ y ry u ⟨0, le_rfl, hW⟩ := by
    filter_upwards [rectangleSource_ae hU e Λ x rx, rectangleSource_ae hU e Λ y ry, hd] with u hx hy hd
    rw [hx, hy, hz, hw, hd]
  refine ⟨hm, ?_⟩
  apply Lp.ext
  filter_upwards [rectangleSource_ae hU e Λ (waveSplice hV hW x y) (waveSplice_radius hV hW x y rx ry hz),
    rectangleSource_ae hU e Λ x rx, rectangleSource_ae hU e Λ y ry,
    intervalSpliceLp_ae hV hW x.2.2 y.2.2,
    intervalSpliceLp_ae hV hW (rectangleSource hU e Λ x rx) (rectangleSource hU e Λ y ry), hd, hm]
    with u hF hx hy hD hS hd hm
  apply continuousMap_ext_adjacent hV hW
  · intro t
    rw [hF, hS]
    change waveSource e Λ
      (intervalSplice hV hW (x.1 (projIcc 0 U hU u)) (y.1 (projIcc 0 U hU u)) _)
      (intervalSpliceLp hV hW x.2.2 y.2.2 u _)
      (intervalSplice hV hW (x.2.1 (projIcc 0 U hU u)) (y.2.1 (projIcc 0 U hU u)) _) = _
    rw [hD, intervalSplice_left, intervalSplice_left, intervalSplice_left, intervalSplice_left]
    exact (hx t).symm
  · intro t
    rw [hF, hS]
    change waveSource e Λ
      (intervalSplice hV hW (x.1 (projIcc 0 U hU u)) (y.1 (projIcc 0 U hU u)) _)
      (intervalSpliceLp hV hW x.2.2 y.2.2 u _)
      (intervalSplice hV hW (x.2.1 (projIcc 0 U hU u)) (y.2.1 (projIcc 0 U hU u)) _) = _
    rw [hD, intervalSplice_right_of_match hV hW _ _ (hz _), intervalSplice_right_of_match hV hW _ _ hd,
      intervalSplice_right_of_match hV hW _ _ (hw _), intervalSplice_right_of_match hV hW _ _ hm]
    exact (hy t).symm

theorem IsWaveIntegral.splice {hU : 0 ≤ U} {hV : 0 ≤ V} {hW : 0 ≤ W} {e Λ : ℝ}
    {zx zy : C(Icc 0 U, WaveVector)} {vx : C(Icc 0 V, WaveVector)} {vy : C(Icc 0 W, WaveVector)}
    {ux uy : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V} {y : WaveState U W}
    (hx : IsWaveIntegral hU hV e Λ zx vx ux x) (hy : IsWaveIntegral hU hW e Λ zy vy uy y)
    (hz : ∀ u, x.1 u ⟨V, hV, le_rfl⟩ = y.1 u ⟨0, le_rfl, hW⟩)
    (hw : ∀ u, x.2.1 u ⟨V, hV, le_rfl⟩ = y.2.1 u ⟨0, le_rfl, hW⟩)
    (hd : ∀ᵐ u ∂volume.restrict (Icc 0 U), x.2.2 u ⟨V, hV, le_rfl⟩ = y.2.2 u ⟨0, le_rfl, hW⟩) :
    IsWaveIntegral hU (add_nonneg hV hW) e Λ zx (intervalSplice hV hW vx vy) ux (waveSplice hV hW x y) := by
  let F := rectangleSource hU e Λ x hx.choose
  let G := rectangleSource hU e Λ y hy.choose
  let z := waveSplice hV hW x y
  have hr : ∀ u v, z.1 u v 0 ≠ 0 := waveSplice_radius hV hW x y hx.choose hy.choose hz
  obtain ⟨hm, hsource⟩ := rectangleSource_splice hU hV hW e Λ x y hx.choose hy.choose hz hw hd
  change rectangleSource hU e Λ z hr = intervalSpliceLp hV hW F G at hsource
  refine ⟨hr, ?_⟩
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    change ContinuousMap.const _ (zx u) + continuousPrimitive (add_nonneg hV hW)
      (intervalSplice hV hW (x.2.1 u) (y.2.1 u)) = intervalSplice hV hW (x.1 u) (y.1 u)
    have hxu : ContinuousMap.const _ (zx u) + continuousPrimitive hV (x.2.1 u) = x.1 u :=
      congrArg (fun q : WaveState U V => q.1 u) hx.choose_spec
    have hyu : ContinuousMap.const _ (zy u) + continuousPrimitive hW (y.2.1 u) = y.1 u :=
      congrArg (fun q : WaveState U W => q.1 u) hy.choose_spec
    rw [continuousPrimitive_splice hV hW _ _ (hw u), ← hxu, ← hyu, intervalSplice_add, intervalSplice_const]
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    change intervalSplice hV hW vx vy + horizontalPrimitive hU (rectangleSource hU e Λ z hr) u =
      intervalSplice hV hW (x.2.1 u) (y.2.1 u)
    have hxu : vx + horizontalPrimitive hU F u = x.2.1 u :=
      congrArg (fun q : WaveState U V => q.2.1 u) hx.choose_spec
    have hyu : vy + horizontalPrimitive hU G u = y.2.1 u :=
      congrArg (fun q : WaveState U W => q.2.1 u) hy.choose_spec
    rw [hsource, horizontalPrimitive_splice, ← hxu, ← hyu, intervalSplice_add]
  · apply Lp.ext
    filter_upwards [Lp.coeFn_add (incomingTransverse (V := V + W) ux)
        (verticalPrimitive (add_nonneg hV hW) (rectangleSource hU e Λ z hr)),
      (ContinuousLinearMap.const ℝ (Icc 0 (V + W))).coeFn_compLpL ux,
      verticalPrimitive_ae (add_nonneg hV hW) (rectangleSource hU e Λ z hr),
      intervalSpliceLp_ae hV hW F G, intervalSpliceLp_ae hV hW x.2.2 y.2.2,
      hx.transverse_identity hx.choose, hy.transverse_identity hy.choose, hm]
      with u hu hin hv hFG hxy hxu hyu hm
    change (incomingTransverse (V := V + W) ux +
      verticalPrimitive (add_nonneg hV hW) (rectangleSource hU e Λ z hr) : WaveTransverse U (V + W)) u =
      intervalSpliceLp hV hW x.2.2 y.2.2 u
    change incomingTransverse (V := V + W) ux u = ContinuousMap.const _ (ux u) at hin
    rw [hu, Pi.add_apply, hin, hv, hsource, hFG, hxy, continuousPrimitive_splice hV hW _ _ hm,
      hxu, hyu, intervalSplice_add, intervalSplice_const]

end CauchyHorizon
