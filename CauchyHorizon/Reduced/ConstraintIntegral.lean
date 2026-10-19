import CauchyHorizon.Reduced.TransverseConstraint
import CauchyHorizon.Analysis.PrimitiveContinuity

/-! Absolute continuity supplies the integral transverse constraint. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}

noncomputable def radialNuOperator (hV : 0 ≤ V) (e Λ : ℝ)
    (z : C(Icc 0 V, WaveVector)) : C(Icc 0 V, ℝ) :=
  let T (i : Fin 3) := ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
    (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ)
  (-ContinuousMap.const _ (z ⟨0, le_rfl, hV⟩ 0) +
    continuousPrimitiveL hV (NormedSpace.exp (T 2 z) *
      (ContinuousMap.const _ (-1 / 4 : ℝ) + (e ^ 2 / 4) • (Ring.inverse (T 0 z) * Ring.inverse (T 0 z)) +
        (Λ / 4) • (T 0 z * T 0 z)))) * Ring.inverse (T 0 z)

theorem radialNuOperator_contDiffAt (hV : 0 ≤ V) (e Λ : ℝ)
    (z : C(Icc 0 V, WaveVector)) (hr : ∀ v, z v 0 ≠ 0) :
    ContDiffAt ℝ 1 (radialNuOperator hV e Λ) z := by
  let T (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, ℝ) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj i)
  let H : C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, ℝ) :=
    (ContinuousLinearMap.const ℝ (Icc 0 V)).comp
      ((ContinuousLinearMap.proj (0 : Fin 3)).comp (ContinuousMap.evalCLM ℝ ⟨0, le_rfl, hV⟩))
  have hu := ((T 0 z).isUnit_iff_forall_ne_zero).2 hr
  have hi := contDiffAt_ringInverse ℝ (n := 1) hu.unit
  rw [hu.unit_spec] at hi
  have hI := hi.comp z (T 0).contDiff.contDiffAt
  have hE := (NormedSpace.exp_analytic (𝕂 := ℝ) (T 2 z)).contDiffAt (n := 1) |>.comp z (T 2).contDiff.contDiffAt
  have hB := ((contDiffAt_const (c := ContinuousMap.const _ (-1 / 4 : ℝ))).add
    ((hI.mul hI).const_smul (e ^ 2 / 4))).add
      (((T 0).contDiff.contDiffAt.mul (T 0).contDiff.contDiffAt).const_smul (Λ / 4))
  have hP := (continuousPrimitiveL (E := ℝ) hV).contDiff.contDiffAt.comp z (hE.mul hB)
  exact (H.contDiff.contDiffAt.neg.add hP).mul hI

variable {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.radialNu_operator
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (u : Icc 0 U) :
    radialNuOperator hV e Λ (x.1 u) = radialNuField hV e Λ zIn x.1 hr u := by
  let T (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, ℝ) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj i)
  have hn : ∀ v, T 0 (x.1 u) v ≠ 0 := hr u
  have hF : NormedSpace.exp (T 2 (x.1 u)) *
      (ContinuousMap.const _ (-1 / 4 : ℝ) + (e ^ 2 / 4) •
        (Ring.inverse (T 0 (x.1 u)) * Ring.inverse (T 0 (x.1 u))) +
          (Λ / 4) • (T 0 (x.1 u) * T 0 (x.1 u))) = radialFluxField e Λ x.1 hr u := by
    apply ContinuousMap.ext
    intro v
    simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.const_apply,
      ContinuousMap.smul_apply, smul_eq_mul, continuousMap_exp_apply,
      continuousMap_inverse_apply _ hn, radialFluxField_apply]
    change Real.exp (x.1 u v 2) * (-1 / 4 + (e ^ 2 / 4) * ((x.1 u v 0)⁻¹ * (x.1 u v 0)⁻¹) +
      (Λ / 4) * (x.1 u v 0 * x.1 u v 0)) = _
    unfold radialPotential
    field_simp [hr u v]
  have hz := waveIteration_incoming_value hU hV e Λ zIn vOut uIn x hx.choose u
  rw [hx.choose_spec] at hz
  change (-ContinuousMap.const _ (x.1 u ⟨0, le_rfl, hV⟩ 0) + continuousPrimitiveL hV _) *
    Ring.inverse (T 0 (x.1 u)) = _
  rw [hF, hz]
  apply ContinuousMap.ext
  intro v
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.neg_apply,
    ContinuousMap.const_apply, continuousMap_inverse_apply _ hn, radialNuField_apply]
  rfl

theorem IsWaveIntegral.horizontal_absolutelyContinuous
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    AbsolutelyContinuousOnInterval (intervalExtension hU x.1) 0 U := by
  rw [hx.horizontal_identity hzin, map_add]
  exact horizontalPrimitive_absolutelyContinuous hU x.2.2 _

theorem IsWaveIntegral.weightedNu_absolutelyContinuous
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (v : Icc 0 V) :
    AbsolutelyContinuousOnInterval (fun t =>
      intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v *
        Real.exp (-intervalExtension hU x.1 t v 2)) 0 U := by
  let G : C(Icc 0 V, WaveVector) → ℝ := fun z =>
    radialNuOperator hV e Λ z v * Real.exp (-z v 2)
  have hG : ∀ z ∈ (intervalExtension hU x.1) '' uIcc (0 : ℝ) U, ContDiffAt ℝ 1 G z := by
    intro z hz
    obtain ⟨t, _, rfl⟩ := hz
    have hN := (ContinuousMap.evalCLM ℝ v : C(Icc 0 V, ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp _
      (radialNuOperator_contDiffAt hV e Λ _ (hr (projIcc 0 U hU t)))
    have hE : ContDiffAt ℝ 1 (fun z : C(Icc 0 V, WaveVector) => Real.exp (-z v 2))
        (intervalExtension hU x.1 t) := by
      let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
        (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
      exact Real.contDiff_exp.contDiffAt.comp _ T.contDiff.contDiffAt.neg
    exact hN.mul hE
  have hc := absolutelyContinuous_comp_contDiffAt (hx.horizontal_absolutelyContinuous hzin) hG
  have he : G ∘ intervalExtension hU x.1 = fun t =>
      intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v *
        Real.exp (-intervalExtension hU x.1 t v 2) := by
    funext t
    change radialNuOperator hV e Λ (x.1 (projIcc 0 U hU t)) v * _ = _
    rw [hx.radialNu_operator hr]
    rfl
  exact he ▸ hc

theorem IsWaveIntegral.transverse_constraint_integral
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2)
    (v : Icc 0 V) :
    IntervalIntegrable (fun t => intervalExtension hU x.1 t v 0 *
      Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2) volume 0 U ∧
    ∀ u : Icc 0 U,
      radialNuField hV e Λ zIn x.1 hr u v * Real.exp (-x.1 u v 2) =
        radialNuField hV e Λ zIn x.1 hr ⟨0, le_rfl, hU⟩ v *
          Real.exp (-x.1 ⟨0, le_rfl, hU⟩ v 2) -
        ∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 *
          Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2 := by
  let Q : ℝ → ℝ := fun t => intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v *
    Real.exp (-intervalExtension hU x.1 t v 2)
  let ρ : ℝ → ℝ := fun t => intervalExtension hU x.1 t v 0 *
    Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2
  have hc : AbsolutelyContinuousOnInterval Q 0 U := hx.weightedNu_absolutelyContinuous hr hzin v
  have he : deriv Q =ᵐ[volume.restrict (Icc 0 U)] fun t => -ρ t := by
    filter_upwards [hx.transverse_constraint hr hzin hinu hinell, hx.horizontal_derivative hzin,
      ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc 0 U)).ae_ne 0,
      (volume.restrict (Icc 0 U)).ae_ne U] with t hn hz ht ht0 htU
    let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
    have hl := T.hasFDerivAt.comp_hasDerivWithinAt t hz
    have hh := (hn v).mul (Real.hasDerivAt_exp _ |>.comp_hasDerivWithinAt t hl.neg)
    have hd : HasDerivWithinAt Q (-ρ t) (Icc 0 U) t := by
      apply hh.congr_deriv
      change (x.2.2 t v 2 * radialNuField hV e Λ zIn x.1 hr (projIcc 0 U hU t) v -
          x.1 (projIcc 0 U hU t) v 0 * (x.2.2 t v 1) ^ 2) *
          Real.exp (-intervalExtension hU x.1 t v 2) +
        intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v *
          (Real.exp (-intervalExtension hU x.1 t v 2) * (-x.2.2 t v 2)) = -ρ t
      simp only [intervalExtension_apply, ρ]
      ring
    exact (hd.hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne ht.1 ht0.symm)
      (lt_of_le_of_ne ht.2 htU))).deriv
  have hs : uIoc (0 : ℝ) U ⊆ Icc 0 U := by rw [uIoc_of_le hU]; exact Ioc_subset_Icc_self
  have hi := hc.intervalIntegrable_deriv.congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) he)
  refine ⟨?_, fun u => ?_⟩
  · have hneg := hi.neg
    change IntervalIntegrable (fun t => -(-ρ t)) volume 0 U at hneg
    simpa only [neg_neg, ρ] using hneg
  · have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
      rw [uIcc_of_le u.property.1, uIcc_of_le hU]
      exact Icc_subset_Icc le_rfl u.property.2
    have hp := (hc.mono hsub).integral_deriv_eq_sub
    have hs' : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
    rw [intervalIntegral.integral_of_le u.property.1,
      integral_congr_ae (ae_mono (Measure.restrict_mono hs' le_rfl) he), integral_neg] at hp
    simp only [Q, intervalExtension_apply, projIcc_of_mem hU u.property,
      projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩)] at hp
    rw [intervalIntegral.integral_of_le u.property.1]
    linarith only [hp]

end CauchyHorizon
