import CauchyHorizon.Reduced.ScalarRegularity
import CauchyHorizon.Analysis.PrimitiveRegularity

/-! Continuous positive-u data give continuous representatives of both horizontal derivatives. -/

open Set MeasureTheory

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem IsWaveIntegral.exists_continuous_horizontal_derivatives
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F) :
    ∃ D S : ℝ → C(Icc 0 V, WaveVector),
      ContinuousOn D (Ioi 0) ∧ ContinuousOn S (Ioi 0) ∧
        x.2.2 =ᵐ[volume.restrict (Icc 0 U)] D ∧
        rectangleSource hU e Λ x hx.choose =ᵐ[volume.restrict (Icc 0 U)] S ∧
        ∀ u ∈ Ioc 0 U,
          HasDerivWithinAt (intervalExtension hU x.1) (D u) (Icc 0 U) u ∧
          HasDerivWithinAt (intervalExtension hU x.2.1) (S u) (Icc 0 U) u := by
  let ν := radialNuField hV e Λ zIn x.1 hx.choose
  let A := scalarIncomingCoefficient zIn x.1 hx.choose
  let B := scalarRegularPart hV x.1 x.2.1 ν hx.choose
  let W₀ : WaveRectangle U V := (⟨fun z : Icc 0 U × Icc 0 V => ![ν z.1 z.2, B z.1 z.2, 0],
    by fun_prop⟩ : C(Icc 0 U × Icc 0 V, WaveVector)).curry
  let W₁ : WaveRectangle U V := (⟨fun z : Icc 0 U × Icc 0 V => ![0, A z.1 z.2, 0],
    by fun_prop⟩ : C(Icc 0 U × Icc 0 V, WaveVector)).curry
  let P := (wavePotentialField e Λ x.1.uncurry (fun z => hx.choose z.1 z.2)).curry
  let L : C(Icc 0 U, C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, WaveVector)) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
    (pointwiseOperatorL (J := Icc 0 V) (E := WaveVector))
    (waveLinearField x.1.uncurry x.2.1.uncurry (fun z => hx.choose z.1 z.2)).curry
  let S := fun u => intervalExtension hU P u + L (projIcc 0 U hU u)
    (intervalExtension hU W₀ u + (F u 1) • intervalExtension hU W₁ u)
  have hSc : ContinuousOn S (Ioi 0) := by dsimp only [S]; fun_prop
  have hSae : rectangleSource hU e Λ x hx.choose =ᵐ[volume.restrict (Icc 0 U)] S := by
    filter_upwards [rectangleSource_ae hU e Λ x hx.choose, hx.radialNu_ae hx.choose hinu,
      hx.scalar_decomposition hx.choose hinu, hif] with u hs hn hφ hf
    apply ContinuousMap.ext
    intro v
    have hφv := congrArg (fun z : C(Icc 0 V, ℝ) => z v) hφ
    change x.2.2 u v 1 = uIn u 1 * A (projIcc 0 U hU u) v + B (projIcc 0 U hU u) v at hφv
    rw [hf] at hφv
    rw [add_comm] at hφv
    rw [hs v]
    change waveSource e Λ (x.1 (projIcc 0 U hU u) v) (x.2.2 u v) (x.2.1 (projIcc 0 U hU u) v) =
      wavePotential e Λ (x.1 (projIcc 0 U hU u) v) +
        waveLinear (x.1 (projIcc 0 U hU u) v) (x.2.1 (projIcc 0 U hU u) v)
          (![ν (projIcc 0 U hU u) v, B (projIcc 0 U hU u) v, 0] +
            (F u 1) • ![0, A (projIcc 0 U hU u) v, 0])
    rw [← waveSource_affine]
    simp only [waveSource, hn v, hφv, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero, ν]
  let D := fun u => ContinuousMap.const (Icc 0 V) (F u) + continuousPrimitiveL hV (S u)
  have hDc : ContinuousOn D (Ioi 0) := by dsimp only [D]; fun_prop
  have hDae : x.2.2 =ᵐ[volume.restrict (Icc 0 U)] D := by
    filter_upwards [hx.transverse_identity hx.choose, hif, hSae] with u hu hf hs
    simpa only [D, hf, hs, continuousPrimitiveL_apply] using hu
  refine ⟨D, S, hDc, hSc, hDae, hSae, ?_⟩
  intro u hu
  have hd := horizontalPrimitive_hasDerivWithinAt_of_continuous hU x.2.2 hDc hDae hu
  have hs := horizontalPrimitive_hasDerivWithinAt_of_continuous hU
    (rectangleSource hU e Λ x hx.choose) hSc hSae hu
  constructor
  · rw [hx.horizontal_identity hzin, map_add]
    exact hd.const_add _
  · have hv : ContinuousMap.const _ vOut + horizontalPrimitive hU (rectangleSource hU e Λ x hx.choose) = x.2.1 :=
      congrArg (fun z : WaveState U V => z.2.1) hx.choose_spec
    rw [← hv, map_add]
    exact hs.const_add _

end CauchyHorizon
