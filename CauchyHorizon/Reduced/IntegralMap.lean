import CauchyHorizon.Reduced.MixedWave
import CauchyHorizon.Analysis.IntervalOperators

/-! The actual characteristic Picard map on one compact rectangle. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

abbrev WaveRectangle (U V : ℝ) := C(Icc 0 U, C(Icc 0 V, WaveVector))
noncomputable abbrev WaveTransverse (U V : ℝ) := Lp C(Icc 0 V, WaveVector) 2 (volume.restrict (Icc 0 U))
noncomputable abbrev WaveState (U V : ℝ) := WaveRectangle U V × WaveRectangle U V × WaveTransverse U V

variable {U V : ℝ}

theorem waveState_norm_equivalence (x : WaveState U V) :
    ‖x‖ ≤ ‖x.1‖ + ‖x.2.1‖ + ‖x.2.2‖ ∧
      ‖x.1‖ + ‖x.2.1‖ + ‖x.2.2‖ ≤ 3 * ‖x‖ := by
  have hz := norm_fst_le x
  have hv := (norm_fst_le x.2).trans (norm_snd_le x)
  have hu := (norm_snd_le x.2).trans (norm_snd_le x)
  constructor
  · apply norm_prod_le_iff.2
    constructor
    · linarith [norm_nonneg x.2.1, norm_nonneg x.2.2]
    · apply norm_prod_le_iff.2
      constructor <;> linarith [norm_nonneg x.1, norm_nonneg x.2.1, norm_nonneg x.2.2]
  · linarith

noncomputable def rectanglePotential (hU : 0 ≤ U) (e Λ : ℝ) (z : WaveRectangle U V)
    (hr : ∀ x y, z x y 0 ≠ 0) : WaveTransverse U V :=
  intervalToLp hU 2 (wavePotentialField e Λ z.uncurry (fun x => hr x.1 x.2)).curry

noncomputable def rectangleOperator (hU : 0 ≤ U) (z v : WaveRectangle U V)
    (hr : ∀ x y, z x y 0 ≠ 0) :
    Lp (C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, WaveVector)) ∞ (volume.restrict (Icc 0 U)) :=
  intervalToLp hU ∞
    (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
      (pointwiseOperatorL (J := Icc 0 V) (E := WaveVector))
      (waveLinearField z.uncurry v.uncurry (fun x => hr x.1 x.2)).curry)

noncomputable def rectangleSource (hU : 0 ≤ U) (e Λ : ℝ) (x : WaveState U V)
    (hr : ∀ u v, x.1 u v 0 ≠ 0) : WaveTransverse U V :=
  affineMixedSource (rectanglePotential hU e Λ x.1 hr) (rectangleOperator hU x.1 x.2.1 hr) x.2.2

theorem rectangleSource_ae (hU : 0 ≤ U) (e Λ : ℝ) (x : WaveState U V)
    (hr : ∀ u v, x.1 u v 0 ≠ 0) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      rectangleSource hU e Λ x hr u v =
        waveSource e Λ (x.1 (projIcc 0 U hU u) v) (x.2.2 u v) (x.2.1 (projIcc 0 U hU u) v) := by
  have hg := intervalToLp_ae hU 2 (wavePotentialField e Λ x.1.uncurry (fun q => hr q.1 q.2)).curry
  have hA := intervalToLp_ae (E := C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, WaveVector)) hU ∞
    (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (pointwiseOperatorL (J := Icc 0 V) (E := WaveVector))
      (waveLinearField x.1.uncurry x.2.1.uncurry (fun q => hr q.1 q.2)).curry)
  filter_upwards [affineMixedSource_ae (rectanglePotential hU e Λ x.1 hr)
    (rectangleOperator hU x.1 x.2.1 hr) x.2.2, hg, hA] with u hu hgu hAu
  intro v
  change rectanglePotential hU e Λ x.1 hr u = _ at hgu
  change rectangleOperator hU x.1 x.2.1 hr u = _ at hAu
  have he := congrArg (fun f : C(Icc 0 V, WaveVector) => f v) hu
  rw [hgu, hAu] at he
  change rectangleSource hU e Λ x hr u v = wavePotential e Λ (x.1 (projIcc 0 U hU u) v) +
    waveLinear (x.1 (projIcc 0 U hU u) v) (x.2.1 (projIcc 0 U hU u) v) (x.2.2 u v) at he
  simpa only [waveSource_affine] using he

noncomputable def longitudinalIntegral (hV : 0 ≤ V) : WaveRectangle U V →L[ℝ] WaveRectangle U V :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (continuousPrimitiveL hV)

theorem longitudinalIntegral_norm_le (hV : 0 ≤ V) (f : WaveRectangle U V) :
    ‖longitudinalIntegral hV f‖ ≤ V * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hV (norm_nonneg f))).2
  intro u
  change ‖continuousPrimitive hV (f u)‖ ≤ _
  have h := continuousPrimitive_norm_le hV (f u)
  rw [sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm u) hV)

noncomputable def incomingField (z : C(Icc 0 U, WaveVector)) : WaveRectangle U V :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (ContinuousLinearMap.const ℝ (Icc 0 V)) z

noncomputable def incomingTransverse (u : Lp WaveVector 2 (volume.restrict (Icc 0 U))) :
    WaveTransverse U V :=
  (ContinuousLinearMap.const ℝ (Icc 0 V)).compLpL 2 (volume.restrict (Icc 0 U)) u

noncomputable def waveIteration (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (x : WaveState U V) (hr : ∀ u v, x.1 u v 0 ≠ 0) : WaveState U V :=
  let F := rectangleSource hU e Λ x hr
  (incomingField zIn + longitudinalIntegral hV x.2.1,
    ContinuousMap.const _ vOut + horizontalPrimitive hU F,
    incomingTransverse uIn + verticalPrimitive hV F)

theorem waveIteration_difference (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (x y : WaveState U V) (hx : ∀ u v, x.1 u v 0 ≠ 0) (hy : ∀ u v, y.1 u v 0 ≠ 0) :
    let X := waveIteration hU hV e Λ zIn vOut uIn x hx
    let Y := waveIteration hU hV e Λ zIn vOut uIn y hy
    let dF := rectangleSource hU e Λ x hx - rectangleSource hU e Λ y hy
    ‖X.1 - Y.1‖ ≤ V * ‖x.2.1 - y.2.1‖ ∧
      ‖X.2.1 - Y.2.1‖ ≤ Real.sqrt U * ‖dF‖ ∧
      ‖X.2.2 - Y.2.2‖ ≤ V * ‖dF‖ := by
  dsimp only [waveIteration]
  simp only [add_sub_add_left_eq_sub, ← map_sub, ← horizontalPrimitive_sub]
  refine ⟨longitudinalIntegral_norm_le hV _, ?_, ?_⟩
  · simpa only [sub_zero] using horizontalPrimitive_norm_le hU
      (rectangleSource hU e Λ x hx - rectangleSource hU e Λ y hy)
  · simpa only [sub_zero] using verticalPrimitive_norm_le hV
      (rectangleSource hU e Λ x hx - rectangleSource hU e Λ y hy)

theorem waveIteration_incoming_value (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (x : WaveState U V) (hr : ∀ u v, x.1 u v 0 ≠ 0) (u : Icc 0 U) :
    (waveIteration hU hV e Λ zIn vOut uIn x hr).1 u ⟨0, le_rfl, hV⟩ = zIn u := by
  change zIn u + (∫ t in (0 : ℝ)..0, intervalExtension hV (x.2.1 u) t) = zIn u
  rw [intervalIntegral.integral_same, add_zero]

theorem waveIteration_outgoing_derivative (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (x : WaveState U V) (hr : ∀ u v, x.1 u v 0 ≠ 0) :
    (waveIteration hU hV e Λ zIn vOut uIn x hr).2.1 ⟨0, le_rfl, hU⟩ = vOut := by
  change vOut + (∫ t in (0 : ℝ)..0, rectangleSource hU e Λ x hr t) = vOut
  rw [intervalIntegral.integral_same, add_zero]

theorem waveIteration_incoming_derivative (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (x : WaveState U V) (hr : ∀ u v, x.1 u v 0 ≠ 0) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U),
      (waveIteration hU hV e Λ zIn vOut uIn x hr).2.2 u ⟨0, le_rfl, hV⟩ = uIn u := by
  let F := rectangleSource hU e Λ x hr
  have hin := (ContinuousLinearMap.const ℝ (Icc 0 V) : WaveVector →L[ℝ] C(Icc 0 V, WaveVector)).coeFn_compLpL
    (p := 2) (μ := volume.restrict (Icc 0 U)) uIn
  filter_upwards [Lp.coeFn_add (incomingTransverse (V := V) uIn) (verticalPrimitive hV F),
    hin, verticalPrimitive_ae hV F] with u hu hi hv
  have he := congrArg (fun f : C(Icc 0 V, WaveVector) => f ⟨0, le_rfl, hV⟩) hu
  change incomingTransverse (V := V) uIn u = ContinuousMap.const _ (uIn u) at hi
  change (waveIteration hU hV e Λ zIn vOut uIn x hr).2.2 u ⟨0, le_rfl, hV⟩ =
    incomingTransverse uIn u ⟨0, le_rfl, hV⟩ + verticalPrimitive hV F u ⟨0, le_rfl, hV⟩ at he
  rw [hi, hv] at he
  change (waveIteration hU hV e Λ zIn vOut uIn x hr).2.2 u ⟨0, le_rfl, hV⟩ =
    uIn u + (∫ t in (0 : ℝ)..0, intervalExtension hV (F u) t) at he
  simpa only [intervalIntegral.integral_same, add_zero] using he

end CauchyHorizon
