import CauchyHorizon.Reduced.TransverseRegularity
import CauchyHorizon.Reduced.ConstraintIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The actual transverse scalar trace is C1 in positive u when the incoming scalar is C1. -/

open Set MeasureTheory

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem IsWaveIntegral.scalar_transverse_contDiff
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F)
    (hfs : ContDiffOn ℝ 1 (fun u => F u 1) (Ioi 0)) :
    let ν := radialNuField hV e Λ zIn x.1 hx.choose
    let C := scalarTransportCorrection hV ν x.2.1
    let ζ := fun u => ContinuousMap.const (Icc 0 V) (zIn (projIcc 0 U hU u) 0 * F u 1) +
      intervalExtension hU C u
    ContDiffOn ℝ 1 (intervalExtension hU x.1) (Ioo 0 U) ∧
      ContDiffOn ℝ 1 (intervalExtension hU x.2.1) (Ioo 0 U) ∧
      ContDiffOn ℝ 1 (intervalExtension hU ν) (Ioo 0 U) ∧
      ContDiffOn ℝ 1 ζ (Ioo 0 U) := by
  intro ν C ζ
  obtain ⟨D, S, hDc, hSc, _hDae, _hSae, hder⟩ :=
    hx.exists_continuous_horizontal_derivatives hzin hinu hF hif
  have hreg {g d : ℝ → C(Icc 0 V, WaveVector)} (hd : ContinuousOn d (Ioi 0))
      (hg : ∀ u ∈ Ioo 0 U, HasDerivAt g (d u) u) : ContDiffOn ℝ 1 g (Ioo 0 U) := by
    apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).2
    refine ⟨fun u hu => (hg u hu).differentiableAt.differentiableWithinAt, ?_⟩
    apply (hd.mono (fun _ hu => hu.1)).congr
    intro u hu
    exact (hg u hu).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt hu)
  have hZ : ContDiffOn ℝ 1 (intervalExtension hU x.1) (Ioo 0 U) :=
    hreg hDc (fun u hu => ((hder u ⟨hu.1, hu.2.le⟩).1).hasDerivAt (Icc_mem_nhds hu.1 hu.2))
  have hW : ContDiffOn ℝ 1 (intervalExtension hU x.2.1) (Ioo 0 U) :=
    hreg hSc (fun u hu => ((hder u ⟨hu.1, hu.2.le⟩).2).hasDerivAt (Icc_mem_nhds hu.1 hu.2))
  have hNeq : (fun u => radialNuOperator hV e Λ (intervalExtension hU x.1 u)) = intervalExtension hU ν := by
    funext u
    exact hx.radialNu_operator hx.choose (projIcc 0 U hU u)
  have hN : ContDiffOn ℝ 1 (intervalExtension hU ν) (Ioo 0 U) := by
    rw [← hNeq]
    intro u hu
    exact (radialNuOperator_contDiffAt hV e Λ _ (hx.choose (projIcc 0 U hU u))).comp_contDiffWithinAt u (hZ u hu)
  refine ⟨hZ, hW, hN, ?_⟩
  let E₀ : C(Icc 0 V, WaveVector) →L[ℝ] WaveVector := ContinuousMap.evalCLM ℝ ⟨0, le_rfl, hV⟩
  have hIeq : (fun u => E₀ (intervalExtension hU x.1 u)) = intervalExtension hU zIn := by
    funext u
    have hh := waveIteration_incoming_value hU hV e Λ zIn vOut uIn x hx.choose (projIcc 0 U hU u)
    rw [hx.choose_spec] at hh
    exact hh
  have hI : ContDiffOn ℝ 1 (intervalExtension hU zIn) (Ioo 0 U) := by
    rw [← hIeq]
    exact E₀.contDiff.comp_contDiffOn hZ
  let P₀ : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hinit := (P₀.contDiff.comp_contDiffOn hI).mul (hfs.mono (fun _ hu => hu.1))
  have hiC := (ContinuousLinearMap.const ℝ (Icc 0 V)).contDiff.comp_contDiffOn hinit
  let T₁ : C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, ℝ) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj 1)
  have hsrc := hN.neg.mul (T₁.contDiff.comp_contDiffOn hW)
  have hcor := (continuousPrimitiveL (E := ℝ) hV).contDiff.comp_contDiffOn hsrc
  have hh := hiC.add hcor
  exact hh

end CauchyHorizon
