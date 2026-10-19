import CauchyHorizon.Reduced.RadialSecond
import CauchyHorizon.Reduced.ConstraintIntegral

/-! Radial flux and longitudinal differentiation in the continuous transverse norm. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V : ℝ}

noncomputable def flipRectangle {E : Type*} [TopologicalSpace E]
    (z : C(Icc 0 U, C(Icc 0 V, E))) : C(Icc 0 V, C(Icc 0 U, E)) :=
  (z.uncurry.comp ⟨Prod.swap, continuous_swap⟩).curry

variable {e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.longitudinal_section_identity
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) :
    flipRectangle x.1 = ContinuousMap.const _ zIn + continuousPrimitive hV (flipRectangle x.2.1) := by
  apply ContinuousMap.ext
  intro v
  apply ContinuousMap.ext
  intro u
  have hz := congrArg (fun y : WaveState U V => y.1 u v) hx.choose_spec
  change zIn u + continuousPrimitive hV (x.2.1 u) v = x.1 u v at hz
  have hp := (ContinuousMap.evalCLM ℝ u : C(Icc 0 U, WaveVector) →L[ℝ] WaveVector).intervalIntegral_comp_comm
    ((intervalExtension hV (flipRectangle x.2.1)).continuous.intervalIntegrable (μ := volume) (0 : ℝ) v)
  change continuousPrimitive hV (x.2.1 u) v = continuousPrimitive hV (flipRectangle x.2.1) v u at hp
  change x.1 u v = zIn u + continuousPrimitive hV (flipRectangle x.2.1) v u
  rw [← hp]
  exact hz.symm

theorem IsWaveIntegral.longitudinal_section_derivative
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {v : ℝ} (hv : v ∈ Icc 0 V) :
    HasDerivWithinAt (intervalExtension hV (flipRectangle x.1))
      (flipRectangle x.2.1 ⟨v, hv⟩) (Icc 0 V) v := by
  rw [hx.longitudinal_section_identity, map_add]
  exact (continuousPrimitive_hasDerivWithinAt hV (flipRectangle x.2.1) hv).const_add zIn

theorem IsWaveIntegral.velocity_horizontal_absolutelyContinuous
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) :
    AbsolutelyContinuousOnInterval (intervalExtension hU x.2.1) 0 U := by
  have hv : ContinuousMap.const _ vOut + horizontalPrimitive hU
      (rectangleSource hU e Λ x hx.choose) = x.2.1 :=
    congrArg (fun y : WaveState U V => y.2.1) hx.choose_spec
  rw [← hv, map_add]
  exact horizontalPrimitive_absolutelyContinuous hU _ vOut

theorem IsWaveIntegral.horizontal_radial_flux
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.1 u v 0 * x.2.1 u v 0 = x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 0 +
      continuousPrimitive hU (radialFluxField e Λ (flipRectangle x.1) (fun v u => hr u v) v) u := by
  let F := radialFluxField e Λ (flipRectangle x.1) (fun v u => hr u v) v
  let E : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  let R := fun t => E (intervalExtension hU x.1 t)
  let W := fun t => E (intervalExtension hU x.2.1 t)
  let q := fun t => R t * W t
  have hR : AbsolutelyContinuousOnInterval R 0 U :=
    absolutelyContinuous_comp_contDiffAt (hx.horizontal_absolutelyContinuous hzin)
      (fun _ _ => E.contDiff.contDiffAt)
  have hW : AbsolutelyContinuousOnInterval W 0 U :=
    absolutelyContinuous_comp_contDiffAt hx.velocity_horizontal_absolutelyContinuous
      (fun _ _ => E.contDiff.contDiffAt)
  have hq : AbsolutelyContinuousOnInterval q 0 U := hR.mul hW
  have he : deriv q =ᵐ[volume.restrict (Icc 0 U)] intervalExtension hU F := by
    filter_upwards [hx.horizontal_derivative hzin, hx.wave_equation,
      ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc 0 U)).ae_ne 0,
      (volume.restrict (Icc 0 U)).ae_ne U] with t hz hw ht ht0 htU
    have hR := E.hasFDerivAt.comp_hasDerivWithinAt t hz
    have hW := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      t (hw v)
    have hh := hR.mul hW
    change HasDerivWithinAt q _ (Icc 0 U) t at hh
    have hd : HasDerivWithinAt q (intervalExtension hU F t) (Icc 0 U) t := by
      apply hh.congr_deriv
      simp only [Function.comp_apply, ContinuousLinearMap.proj_apply,
        intervalExtension_apply, projIcc_of_mem hU ht]
      change x.2.2 t v 0 * x.2.1 ⟨t, ht⟩ v 0 + x.1 ⟨t, ht⟩ v 0 *
        (Real.exp (x.1 ⟨t, ht⟩ v 2) * radialPotential (x.1 ⟨t, ht⟩ v 0) e Λ -
          x.2.2 t v 0 * x.2.1 ⟨t, ht⟩ v 0 / x.1 ⟨t, ht⟩ v 0) =
        x.1 ⟨t, ht⟩ v 0 * (Real.exp (x.1 ⟨t, ht⟩ v 2) * radialPotential (x.1 ⟨t, ht⟩ v 0) e Λ)
      field_simp [hr ⟨t, ht⟩ v]
      ring
    exact (hd.hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne ht.1 ht0.symm)
      (lt_of_le_of_ne ht.2 htU))).deriv
  have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le u.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl u.property.2
  have hp := (hq.mono hsub).integral_deriv_eq_sub
  have hs : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
  rw [intervalIntegral.integral_of_le u.property.1,
    integral_congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) he)] at hp
  have hprim : continuousPrimitive hU F u = q u - q 0 := by
    change (∫ t in (0 : ℝ)..u, intervalExtension hU F t) = _
    rwa [intervalIntegral.integral_of_le u.property.1]
  simp only [q, R, W, E, ContinuousLinearMap.comp_apply,
    ContinuousMap.evalCLM_apply, ContinuousLinearMap.proj_apply, intervalExtension_apply,
    projIcc_of_mem hU u.property,
    projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩)] at hprim
  have hb := waveIteration_outgoing_derivative hU hV e Λ zIn vOut uIn x hx.choose
  rw [hx.choose_spec] at hb
  change continuousPrimitive hU F u = x.1 u v 0 * x.2.1 u v 0 -
    x.1 ⟨0, le_rfl, hU⟩ v 0 * x.2.1 ⟨0, le_rfl, hU⟩ v 0 at hprim
  rw [hb] at hprim
  linarith only [hprim]

end CauchyHorizon
