import CauchyHorizon.Reduced.WaveSource
import CauchyHorizon.Analysis.MixedSource
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! The three actual wave sources as elements of L2 in u with continuous v sections. -/

open MeasureTheory
open scoped ENNReal

namespace CauchyHorizon

variable {X : Type*} [TopologicalSpace X]

noncomputable def wavePotentialField (e Λ : ℝ) (z : C(X, WaveVector))
    (hr : ∀ x, z x 0 ≠ 0) : C(X, WaveVector) :=
  ⟨fun x => wavePotential e Λ (z x), continuous_iff_continuousAt.2
    (fun x => (wavePotential_contDiffAt (hr x) e Λ).continuousAt.comp z.continuous.continuousAt)⟩

noncomputable def waveLinearField (z v : C(X, WaveVector)) (hr : ∀ x, z x 0 ≠ 0) :
    C(X, WaveVector →L[ℝ] WaveVector) :=
  ⟨fun x => waveLinear (z x) (v x), continuous_iff_continuousAt.2 (fun x => by
    have hpair : ContinuousAt (fun y => (z y, v y)) x :=
      z.continuous.continuousAt.prodMk v.continuous.continuousAt
    exact (waveLinear_contDiffAt (p := (z x, v x)) (hr x)).continuousAt.comp
      (f := fun y => (z y, v y)) hpair)⟩

variable {I J : Type*} [TopologicalSpace I] [TopologicalSpace J]
  [CompactSpace I] [CompactSpace J] [MeasurableSpace I] [BorelSpace I]
  [SecondCountableTopology I] {μ : Measure I} [IsFiniteMeasure μ]

local instance : IsBoundedSMul ℝ (C(J, WaveVector) →L[ℝ] C(J, WaveVector)) :=
  IsBoundedSMul.of_norm_smul_le (fun (c : ℝ) (A : C(J, WaveVector) →L[ℝ] C(J, WaveVector)) =>
    NormedSpace.norm_smul_le c A)

noncomputable def wavePotentialLp (e Λ : ℝ) (z : C(I × J, WaveVector))
    (hr : ∀ x, z x 0 ≠ 0) : Lp C(J, WaveVector) 2 μ :=
  ContinuousMap.toLp 2 μ ℝ (wavePotentialField e Λ z hr).curry

noncomputable def waveOperatorLp (z v : C(I × J, WaveVector)) (hr : ∀ x, z x 0 ≠ 0) :
    Lp (C(J, WaveVector) →L[ℝ] C(J, WaveVector)) ∞ μ :=
  ContinuousMap.toLp ∞ μ ℝ
    (ContinuousLinearMap.compLeftContinuous ℝ I (pointwiseOperatorL (J := J) (E := WaveVector))
      (waveLinearField z v hr).curry)

noncomputable def waveMixedSource (e Λ : ℝ) (z v : C(I × J, WaveVector))
    (hr : ∀ x, z x 0 ≠ 0) (u : Lp C(J, WaveVector) 2 μ) : Lp C(J, WaveVector) 2 μ :=
  affineMixedSource (wavePotentialLp e Λ z hr) (waveOperatorLp z v hr) u

theorem waveMixedSource_ae (e Λ : ℝ) (z v : C(I × J, WaveVector))
    (hr : ∀ x, z x 0 ≠ 0) (u : Lp C(J, WaveVector) 2 μ) :
    ∀ᵐ x ∂μ, ∀ y : J, waveMixedSource e Λ z v hr u x y =
      waveSource e Λ (z (x, y)) (u x y) (v (x, y)) := by
  have hg := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (wavePotentialField e Λ z hr).curry
  have hA := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℝ) μ
    (ContinuousLinearMap.compLeftContinuous ℝ I (pointwiseOperatorL (J := J) (E := WaveVector))
      (waveLinearField z v hr).curry)
  filter_upwards [affineMixedSource_ae (wavePotentialLp e Λ z hr) (waveOperatorLp z v hr) u,
    hg, hA] with x hx hgx hAx
  intro y
  have he := congrArg (fun f : C(J, WaveVector) => f y) hx
  change wavePotentialLp (μ := μ) e Λ z hr x = _ at hgx
  change waveOperatorLp (μ := μ) z v hr x = _ at hAx
  rw [hgx, hAx] at he
  change waveMixedSource e Λ z v hr u x y =
    wavePotential e Λ (z (x, y)) + waveLinear (z (x, y)) (v (x, y)) (u x y) at he
  simpa only [waveSource_affine] using he

theorem waveMixedSource_difference_bound (e Λ : ℝ) (z z' v v' : C(I × J, WaveVector))
    (hr : ∀ x, z x 0 ≠ 0) (hr' : ∀ x, z' x 0 ≠ 0) (u u' : Lp C(J, WaveVector) 2 μ) :
    ‖waveMixedSource e Λ z v hr u - waveMixedSource e Λ z' v' hr' u'‖ ≤
      ‖wavePotentialLp (μ := μ) e Λ z hr - wavePotentialLp e Λ z' hr'‖ +
      ‖waveOperatorLp (μ := μ) z v hr - waveOperatorLp z' v' hr'‖ * ‖u‖ +
      ‖waveOperatorLp (μ := μ) z' v' hr'‖ * ‖u - u'‖ :=
  affineMixedSource_difference_bound _ _ _ _ _ _

end CauchyHorizon
