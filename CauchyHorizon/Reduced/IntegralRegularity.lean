import CauchyHorizon.Reduced.LocalExistence
import CauchyHorizon.Analysis.PrimitiveCompatibility

/-! Compatible characteristic data identify the components of the fixed point as derivatives. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.transverse_identity (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (hr : ∀ u v, x.1 u v 0 ≠ 0) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U),
      x.2.2 u = ContinuousMap.const _ (uIn u) + continuousPrimitive hV (rectangleSource hU e Λ x hr u) := by
  let F := rectangleSource hU e Λ x hr
  have hd : incomingTransverse uIn + verticalPrimitive hV F = x.2.2 :=
    congrArg (fun z : WaveState U V => z.2.2) hx.choose_spec
  filter_upwards [Lp.coeFn_add (incomingTransverse (V := V) uIn) (verticalPrimitive hV F),
    (ContinuousLinearMap.const ℝ (Icc 0 V)).coeFn_compLpL uIn, verticalPrimitive_ae hV F] with u hu hi hv
  rw [← hd]
  change (incomingTransverse (V := V) uIn + verticalPrimitive hV F : WaveTransverse U V) u = _
  rw [hu, Pi.add_apply, hv]
  exact congrArg (fun z => z + continuousPrimitive hV (F u)) hi

theorem IsWaveIntegral.horizontal_identity (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    x.1 = ContinuousMap.const _ (ContinuousMap.const _ c + continuousPrimitive hV vOut) +
      horizontalPrimitive hU x.2.2 := by
  obtain ⟨hr, hfix⟩ := hx
  let F := rectangleSource hU e Λ x hr
  have hz : incomingField zIn + longitudinalIntegral hV x.2.1 = x.1 := congrArg Prod.fst hfix
  have hv : ContinuousMap.const _ vOut + horizontalPrimitive hU F = x.2.1 :=
    congrArg (fun y : WaveState U V => y.2.1) hfix
  have hu : incomingTransverse uIn + verticalPrimitive hV F = x.2.2 :=
    congrArg (fun y : WaveState U V => y.2.2) hfix
  have hin : incomingField (V := V) (horizontalPrimitive hU uIn) = horizontalPrimitive hU (incomingTransverse uIn) :=
    (horizontalPrimitive_compLp (E := WaveVector) (F := C(Icc 0 V, WaveVector)) hU
      (ContinuousLinearMap.const ℝ (Icc 0 V)) uIn).symm
  have hcomm : longitudinalIntegral hV (horizontalPrimitive hU F) = horizontalPrimitive hU (verticalPrimitive hV F) :=
    (horizontalPrimitive_compLp hU (continuousPrimitiveL (E := WaveVector) hV) F).symm
  have hsum : incomingField (V := V) (ContinuousMap.const _ c + horizontalPrimitive hU uIn) =
      incomingField (ContinuousMap.const _ c) + incomingField (horizontalPrimitive hU uIn) := by
    exact (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
      (ContinuousLinearMap.const ℝ (Icc 0 V) : WaveVector →L[ℝ] C(Icc 0 V, WaveVector))).map_add _ _
  rw [hzin, hsum, hin, ← hv, map_add, hcomm] at hz
  rw [← hz, ← hu, horizontalPrimitive_add]
  apply ContinuousMap.ext
  intro u
  apply ContinuousMap.ext
  intro v
  change c + horizontalPrimitive hU (incomingTransverse uIn) u v +
    (continuousPrimitive hV vOut v + horizontalPrimitive hU (verticalPrimitive hV F) u v) =
    (c + continuousPrimitive hV vOut v) +
      (horizontalPrimitive hU (incomingTransverse uIn) u v + horizontalPrimitive hU (verticalPrimitive hV F) u v)
  abel

theorem IsWaveIntegral.longitudinal_derivative (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (u : Icc 0 U) {v : ℝ} (hv : v ∈ Icc 0 V) :
    HasDerivWithinAt (intervalExtension hV (x.1 u)) (x.2.1 u ⟨v, hv⟩) (Icc 0 V) v := by
  obtain ⟨hr, hfix⟩ := hx
  have hz : ContinuousMap.const _ (zIn u) + continuousPrimitive hV (x.2.1 u) = x.1 u :=
    congrArg (fun y : WaveState U V => y.1 u) hfix
  rw [← hz, map_add]
  change HasDerivWithinAt (fun t => zIn u + intervalExtension hV (continuousPrimitive hV (x.2.1 u)) t)
    (x.2.1 u ⟨v, hv⟩) (Icc 0 V) v
  exact (continuousPrimitive_hasDerivWithinAt hV (x.2.1 u) hv).const_add _

theorem IsWaveIntegral.horizontal_derivative (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (intervalExtension hU x.1) (x.2.2 u) (Icc 0 U) u := by
  rw [hx.horizontal_identity hzin, map_add]
  filter_upwards [horizontalPrimitive_ae_hasDerivWithinAt hU x.2.2] with u hu
  change HasDerivWithinAt (fun t => (ContinuousMap.const _ c + continuousPrimitive hV vOut) +
    intervalExtension hU (horizontalPrimitive hU x.2.2) t) (x.2.2 u) (Icc 0 U) u
  exact hu.const_add _

theorem IsWaveIntegral.mixed_derivative (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (hr : ∀ u v, x.1 u v 0 ≠ 0) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (intervalExtension hU x.2.1) (rectangleSource hU e Λ x hr u) (Icc 0 U) u := by
  obtain ⟨_, hfix⟩ := hx
  have hv : ContinuousMap.const _ vOut + horizontalPrimitive hU (rectangleSource hU e Λ x hr) = x.2.1 :=
    congrArg (fun y : WaveState U V => y.2.1) hfix
  rw [← hv, map_add]
  filter_upwards [horizontalPrimitive_ae_hasDerivWithinAt hU (rectangleSource hU e Λ x hr)] with u hu
  change HasDerivWithinAt (fun t => vOut + intervalExtension hU
    (horizontalPrimitive hU (rectangleSource hU e Λ x hr)) t)
    (rectangleSource hU e Λ x hr u) (Icc 0 U) u
  exact hu.const_add _

theorem IsWaveIntegral.wave_equation (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      HasDerivWithinAt (fun t => intervalExtension hU x.2.1 t v)
        (waveSource e Λ (x.1 (projIcc 0 U hU u) v) (x.2.2 u v)
          (x.2.1 (projIcc 0 U hU u) v)) (Icc 0 U) u := by
  filter_upwards [hx.mixed_derivative hx.choose, rectangleSource_ae hU e Λ x hx.choose] with u hu he
  intro v
  have hd := (ContinuousMap.evalCLM ℝ v : C(Icc 0 V, WaveVector) →L[ℝ] WaveVector).hasFDerivAt.comp_hasDerivWithinAt u hu
  change HasDerivWithinAt (fun t => intervalExtension hU x.2.1 t v)
    (rectangleSource hU e Λ x hx.choose u v) (Icc 0 U) u at hd
  rwa [he v] at hd

end CauchyHorizon
