import CauchyHorizon.Reduced.LongitudinalFlux
import CauchyHorizon.Analysis.PrimitiveLimit

/-! Continuous field derivatives recover the same integral equations used by the rough local solver. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

set_option maxHeartbeats 800000 in
theorem wave_integral_of_continuous_derivatives {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (z p q S : WaveRectangle U V) (hr : ∀ u v, z u v 0 ≠ 0)
    (hS : ∀ u v, S u v = waveSource e Λ (z u v) (p u v) (q u v))
    (hz : ∀ u v, HasDerivWithinAt (intervalExtension hV (z u)) (q u v) (Icc 0 V) v)
    (hp : ∀ u v, HasDerivWithinAt (intervalExtension hV (p u)) (S u v) (Icc 0 V) v)
    (hq : ∀ v u, HasDerivWithinAt (intervalExtension hU (flipRectangle q v)) (S u v) (Icc 0 U) u)
    (hinit : ∀ u, HasDerivWithinAt (intervalExtension hU (flipRectangle z ⟨0, le_rfl, hV⟩))
      (p u ⟨0, le_rfl, hV⟩) (Icc 0 U) u) :
    IsWaveIntegral hU hV e Λ (flipRectangle z ⟨0, le_rfl, hV⟩) (q ⟨0, le_rfl, hU⟩)
      (intervalToLp hU 2 (flipRectangle p ⟨0, le_rfl, hV⟩)) (z, q, intervalToLp hU 2 p) ∧
    flipRectangle z ⟨0, le_rfl, hV⟩ = ContinuousMap.const (Icc 0 U)
      (z ⟨0, le_rfl, hU⟩ ⟨0, le_rfl, hV⟩) +
      horizontalPrimitive hU (intervalToLp hU 2 (flipRectangle p ⟨0, le_rfl, hV⟩)) := by
  let u₀ : Icc 0 U := ⟨0, le_rfl, hU⟩
  let v₀ : Icc 0 V := ⟨0, le_rfl, hV⟩
  let uIn := intervalToLp hU 2 (flipRectangle p v₀)
  let x : WaveState U V := (z, q, intervalToLp hU 2 p)
  let F := intervalToLp hU 2 S
  have hinitprim : flipRectangle z v₀ = ContinuousMap.const (Icc 0 U) (z u₀ v₀) +
      horizontalPrimitive hU uIn := by
    change flipRectangle z v₀ = _ + horizontalPrimitive hU (intervalToLp hU 2 (flipRectangle p v₀))
    rw [horizontalPrimitive_intervalToLp]
    exact (continuous_derivative_limit (l := atTop) hU
      (f := fun _ : ℕ => flipRectangle z v₀) (d := fun _ : ℕ => flipRectangle p v₀)
      tendsto_const_nhds tendsto_const_nhds (Eventually.of_forall fun _ => hinit)).1
  have hsource : rectangleSource hU e Λ x hr = F := by
    apply Lp.ext
    filter_upwards [rectangleSource_ae hU e Λ x hr, intervalToLp_ae hU 2 p,
      intervalToLp_ae hU 2 S] with u hs hpu hsu
    apply ContinuousMap.ext
    intro v
    change rectangleSource hU e Λ x hr u v = intervalToLp hU 2 S u v
    rw [hs v, hsu]
    change waveSource e Λ (z (projIcc 0 U hU u) v) (intervalToLp hU 2 p u v)
      (q (projIcc 0 U hU u) v) = _
    rw [hpu]
    exact (hS _ _).symm
  have hzprim (u : Icc 0 U) := (continuous_derivative_limit (l := atTop) hV
    (f := fun _ : ℕ => z u) (d := fun _ : ℕ => q u)
    tendsto_const_nhds tendsto_const_nhds (Eventually.of_forall fun _ => hz u)).1
  have hpprim (u : Icc 0 U) := (continuous_derivative_limit (l := atTop) hV
    (f := fun _ : ℕ => p u) (d := fun _ : ℕ => S u)
    tendsto_const_nhds tendsto_const_nhds (Eventually.of_forall fun _ => hp u)).1
  have hqprim (v : Icc 0 V) := (continuous_derivative_limit (l := atTop) hU
    (f := fun _ : ℕ => flipRectangle q v) (d := fun _ : ℕ => flipRectangle S v)
    tendsto_const_nhds tendsto_const_nhds (Eventually.of_forall fun _ => hq v)).1
  refine ⟨⟨hr, ?_⟩, hinitprim⟩
  change (incomingField (flipRectangle z v₀) + longitudinalIntegral hV q,
    ContinuousMap.const _ (q u₀) + horizontalPrimitive hU (rectangleSource hU e Λ x hr),
    incomingTransverse uIn + verticalPrimitive hV (rectangleSource hU e Λ x hr)) = x
  rw [hsource]
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    exact (hzprim u).symm
  · apply Prod.ext
    · change ContinuousMap.const _ (q u₀) + horizontalPrimitive hU (intervalToLp hU 2 S) = q
      rw [horizontalPrimitive_intervalToLp]
      apply ContinuousMap.ext
      intro u
      apply ContinuousMap.ext
      intro v
      have hh := congrArg (fun f : C(Icc 0 U, WaveVector) => f u) (hqprim v)
      have he := congrArg (fun f : C(Icc 0 U, WaveVector) => f u)
        (continuousPrimitive_comp hU (ContinuousMap.evalCLM ℝ v) S)
      change continuousPrimitive hU (flipRectangle S v) u = continuousPrimitive hU S u v at he
      change q u v = q u₀ v + continuousPrimitive hU (flipRectangle S v) u at hh
      change q u₀ v + continuousPrimitive hU S u v = q u v
      rw [← he]
      exact hh.symm
    · apply Lp.ext
      filter_upwards [Lp.coeFn_add (incomingTransverse (V := V) uIn) (verticalPrimitive hV F),
        (ContinuousLinearMap.const ℝ (Icc 0 V)).coeFn_compLpL uIn,
        intervalToLp_ae hU 2 (flipRectangle p v₀), verticalPrimitive_ae hV F,
        intervalToLp_ae hU 2 S, intervalToLp_ae hU 2 p] with u hadd hin huIn hv hF hp
      change (incomingTransverse (V := V) uIn + verticalPrimitive hV F : WaveTransverse U V) u =
        intervalToLp hU 2 p u
      rw [hadd, hp]
      change incomingTransverse uIn u + verticalPrimitive hV F u = _
      change incomingTransverse uIn u = _ at hin
      rw [hin, hv]
      change ContinuousMap.const _ (intervalToLp hU 2 (flipRectangle p v₀) u) +
        continuousPrimitive hV (intervalToLp hU 2 S u) = _
      rw [huIn, hF]
      exact (hpprim _).symm

end CauchyHorizon
