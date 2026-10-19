import CauchyHorizon.Reduced.ScalarTransport

/-! The conformal transverse derivative retains its incoming integrability exponent. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

noncomputable def conformalRegularSource (e Λ : ℝ) (z w : WaveRectangle U V)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (hr : ∀ u v, z u v 0 ≠ 0) : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  let G := wavePotentialField e Λ z.uncurry (fun q => hr q.1 q.2)
  (⟨fun q : Icc 0 U × Icc 0 V => G q 2 + 2 * ν.uncurry q * w.uncurry q 0 / (z.uncurry q 0) ^ 2, by
    have hG : Continuous (fun q : Icc 0 U × Icc 0 V => G q 2) := by fun_prop
    have hn : Continuous (fun q : Icc 0 U × Icc 0 V => 2 * ν.uncurry q * w.uncurry q 0) := by fun_prop
    have hd : Continuous (fun q : Icc 0 U × Icc 0 V => (z.uncurry q 0) ^ 2) := by fun_prop
    exact hG.add (hn.div hd (fun q => pow_ne_zero 2 (hr q.1 q.2)))⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry

theorem IsWaveIntegral.transverse_coordinate_primitive
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0) (i : Fin 3) :
    let T := ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ)
    ∀ᵐ u ∂volume.restrict (Icc 0 U),
      T (x.2.2 u) = ContinuousMap.const _ (uIn u i) + continuousPrimitive hV (T (rectangleSource hU e Λ x hr u)) := by
  let F := rectangleSource hU e Λ x hr
  let T := ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ)
  have hu : incomingTransverse uIn + verticalPrimitive hV F = x.2.2 :=
    congrArg (fun y : WaveState U V => y.2.2) hx.choose_spec
  have hin := (ContinuousLinearMap.const ℝ (Icc 0 V) : WaveVector →L[ℝ] C(Icc 0 V, WaveVector)).coeFn_compLpL
    (p := 2) (μ := volume.restrict (Icc 0 U)) uIn
  filter_upwards [Lp.coeFn_add (incomingTransverse (V := V) uIn) (verticalPrimitive hV F),
    hin, verticalPrimitive_ae hV F] with u hs hi hv
  rw [hu] at hs
  change x.2.2 u = incomingTransverse uIn u + verticalPrimitive hV F u at hs
  change incomingTransverse (V := V) uIn u = ContinuousMap.const _ (uIn u) at hi
  rw [hi, hv] at hs
  have he := congrArg T hs
  rw [map_add, ← continuousPrimitive_comp hV (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ) (F u)] at he
  exact he

theorem IsWaveIntegral.conformal_source_memLp
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {p : ℝ≥0∞} (hf : MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u)) p (volume.restrict (Icc 0 U))) :
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (2 : Fin 3))) (rectangleSource hU e Λ x hr u)) p (volume.restrict (Icc 0 U)) := by
  let N := radialNuField hV e Λ zIn x.1 hr
  let C := conformalRegularSource e Λ x.1 x.2.1 N hr
  let L := waveCoordinateField 1 x.2.1
  have hL : MemLp (intervalExtension hU L) ∞ (volume.restrict (Icc 0 U)) :=
    (intervalExtension hU L).memLp_top
  have hC : MemLp (intervalExtension hU C) p (volume.restrict (Icc 0 U)) :=
    (intervalExtension hU C).memLp_top.mono_exponent le_top
  apply (((hf.mul hL).const_smul (-2 : ℝ)).add hC).ae_eq
  filter_upwards [rectangleSource_ae hU e Λ x hr, hx.radialNu_ae hr hinu] with u hs hn
  apply ContinuousMap.ext
  intro v
  change -2 * (x.2.1 (projIcc 0 U hU u) v 1 * x.2.2 u v 1) + C (projIcc 0 U hU u) v =
    rectangleSource hU e Λ x hr u v 2
  rw [hs v]
  change -2 * (_ * _) +
    (Real.exp (x.1 (projIcc 0 U hU u) v 2) * conformalPotential (x.1 (projIcc 0 U hU u) v 0) e +
      2 * N (projIcc 0 U hU u) v * x.2.1 (projIcc 0 U hU u) v 0 / (x.1 (projIcc 0 U hU u) v 0) ^ 2) =
    -2 * x.2.2 u v 1 * x.2.1 (projIcc 0 U hU u) v 1 + _ +
      2 * x.2.2 u v 0 * x.2.1 (projIcc 0 U hU u) v 0 / (x.1 (projIcc 0 U hU u) v 0) ^ 2
  rw [hn v]
  ring

theorem IsWaveIntegral.conformal_transverse_memLp
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {p : ℝ≥0∞} (hf : MemLp (fun u => uIn u 1) p (volume.restrict (Icc 0 U)))
    (hℓ : MemLp (fun u => uIn u 2) p (volume.restrict (Icc 0 U))) :
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (2 : Fin 3))) (x.2.2 u)) p (volume.restrict (Icc 0 U)) := by
  have hs := hx.conformal_source_memLp hr hinu (hx.scalar_transverse_memLp hr hinu hf)
  have hp := (continuousPrimitiveL (E := ℝ) hV).comp_memLp' hs
  have hi := (ContinuousLinearMap.const ℝ (Icc 0 V) : ℝ →L[ℝ] C(Icc 0 V, ℝ)).comp_memLp' hℓ
  apply (hi.add hp).ae_eq
  filter_upwards [hx.transverse_coordinate_primitive hr 2] with u hu
  exact hu.symm

end CauchyHorizon
