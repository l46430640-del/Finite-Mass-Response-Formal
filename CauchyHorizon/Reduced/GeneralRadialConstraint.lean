import CauchyHorizon.Reduced.ConstraintIntegral

/-! The transverse constraint propagates from a general continuous incoming radial velocity. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

noncomputable def radialVelocityField {U V : ℝ} (hV : 0 ≤ V) (e Λ : ℝ)
    (n : C(Icc 0 U, ℝ)) (zIn : C(Icc 0 U, WaveVector)) (z : WaveRectangle U V)
    (hr : ∀ u v, z u v 0 ≠ 0) : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  let p := ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (continuousPrimitiveL hV)
    (radialFluxField e Λ z hr)
  (⟨fun q : Icc 0 U × Icc 0 V => (zIn q.1 0 * n q.1 + p.uncurry q) / z.uncurry q 0, by
    have hn : Continuous (fun q : Icc 0 U × Icc 0 V => zIn q.1 0 * n q.1 + p.uncurry q) := by fun_prop
    have hd : Continuous (fun q : Icc 0 U × Icc 0 V => z.uncurry q 0) := by fun_prop
    exact hn.div hd (fun q => hr q.1 q.2)⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.general_radial_constraint {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (n : C(Icc 0 U, ℝ))
    (hn : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = n (projIcc 0 U hU u))
    (hnd : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (intervalExtension hU n)
        (uIn u 2 * n (projIcc 0 U hU u) - zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2) (Icc 0 U) u) :
    let N := radialVelocityField hV e Λ n zIn x.1 hr
    (∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      x.2.2 u v 0 = N (projIcc 0 U hU u) v) ∧
    (∀ (u : Icc 0 U) (v : Icc 0 V),
      HasDerivWithinAt (fun t => intervalExtension hU x.1 t v 0) (N u v) (Icc 0 U) u) ∧
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      HasDerivWithinAt (fun t => intervalExtension hU N t v)
        (x.2.2 u v 2 * N (projIcc 0 U hU u) v -
          x.1 (projIcc 0 U hU u) v 0 * (x.2.2 u v 1) ^ 2) (Icc 0 U) u := by
  let N := radialVelocityField hV e Λ n zIn x.1 hr
  have hN (u : Icc 0 U) (v : Icc 0 V) : N u v =
      (zIn u 0 * n u + continuousPrimitive hV (radialFluxField e Λ x.1 hr u) v) / x.1 u v 0 := rfl
  have hnae : ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      x.2.2 u v 0 = N (projIcc 0 U hU u) v := by
    filter_upwards [hx.radial_flux hr, hn] with u hf hn
    intro v
    rw [hN]
    apply (eq_div_iff (hr _ _)).2
    simpa only [hn, mul_comm] using hf v
  refine ⟨hnae, ?_, ?_⟩
  · let P : C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, ℝ) :=
      ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj (0 : Fin 3))
    have he : P.compLpL 2 (volume.restrict (Icc 0 U)) x.2.2 = intervalToLp hU 2 N := by
      apply Lp.ext
      filter_upwards [P.coeFn_compLpL x.2.2, intervalToLp_ae hU 2 N, hnae] with u hp hn ha
      rw [hp, hn]
      apply ContinuousMap.ext
      exact ha
    have hid := congrArg (fun z : WaveRectangle U V => ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) P z)
      (hx.horizontal_identity hzin)
    rw [map_add, ← horizontalPrimitive_compLp hU P x.2.2, he, horizontalPrimitive_intervalToLp] at hid
    intro u v
    have hd := (ContinuousMap.evalCLM ℝ v : C(Icc 0 V, ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      (u : ℝ) (continuousPrimitive_hasDerivWithinAt hU N u.property)
    apply (hd.const_add (c 0 + continuousPrimitive hV vOut v 0)).congr_of_mem _ u.property
    intro t ht
    have he := congrArg (fun z : C(Icc 0 U, C(Icc 0 V, ℝ)) => z ⟨t, ht⟩ v) hid
    change x.1 ⟨t, ht⟩ v 0 = c 0 + continuousPrimitive hV vOut v 0 + continuousPrimitive hU N ⟨t, ht⟩ v at he
    change intervalExtension hU x.1 t v 0 =
      c 0 + continuousPrimitive hV vOut v 0 + intervalExtension hU (continuousPrimitive hU N) t v
    simpa only [intervalExtension_apply, projIcc_of_mem hU ht] using he
  · have hzi : ∀ᵐ u ∂volume.restrict (Icc 0 U),
        HasDerivWithinAt (intervalExtension hU zIn) (uIn u) (Icc 0 U) u := by
      rw [hzin, map_add]
      filter_upwards [horizontalPrimitive_ae_hasDerivWithinAt hU uIn] with u hu
      exact hu.const_add c
    filter_upwards [hx.horizontal_derivative hzin, hzi, hn, hnd, hnae,
      hx.radialFluxVariation_transverse_integral hr, ae_restrict_mem measurableSet_Icc]
      with u hz hi hn hd ha hc hu
    let a : Icc 0 U := ⟨u, hu⟩
    have hF := radialFluxField_hasDerivWithinAt x.1 hr hu hz (e := e) (Λ := Λ)
    have hP := (continuousPrimitiveL (E := ℝ) hV).hasFDerivAt.comp_hasDerivWithinAt u hF
    have hI := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u hi
    intro v
    let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (0 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
    have hR := T.hasFDerivAt.comp_hasDerivWithinAt u hz
    have hPv := (ContinuousMap.evalCLM ℝ v : C(Icc 0 V, ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u hP
    have hzero : intervalExtension hU x.1 u v 0 ≠ 0 := by
      simpa only [intervalExtension_apply, projIcc_of_mem hU hu] using hr a v
    have hh := ((hI.mul hd).add hPv).div hR hzero
    change HasDerivWithinAt (fun t => intervalExtension hU N t v) _ (Icc 0 U) u at hh
    apply hh.congr_deriv
    simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, ContinuousLinearMap.proj_apply,
      intervalExtension_apply, projIcc_of_mem hU hu] at hn ha hc ⊢
    have hflux := (eq_div_iff (hr a v)).1 ((ha v).trans (hN a v))
    have hvar := hc v
    change radialFluxVariation (x.1 a v) (x.2.2 u v) =
      radialFluxVariation (zIn a) (uIn u) + continuousPrimitive hV
        (radialFluxDifferential e Λ (x.1 a) (x.2.2 u) (hr a)) v at hvar
    rw [← ha v]
    change ((uIn u 0 * n a + zIn a 0 * (uIn u 2 * n a - zIn a 0 * (uIn u 1) ^ 2) +
        continuousPrimitive hV (radialFluxDifferential e Λ (x.1 a) (x.2.2 u) (hr a)) v) * x.1 a v 0 -
      (zIn a 0 * n a + continuousPrimitive hV (radialFluxField e Λ x.1 hr a) v) * x.2.2 u v 0) /
      (x.1 a v 0) ^ 2 = _
    rw [← hflux, ← hn]
    unfold radialFluxVariation at hvar
    field_simp [hr a v]
    nlinarith only [hvar]

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.general_radial_constraint_integral {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (n : C(Icc 0 U, ℝ))
    (hn : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = n (projIcc 0 U hU u))
    (hnAC : AbsolutelyContinuousOnInterval (intervalExtension hU n) 0 U)
    (hnd : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (intervalExtension hU n)
        (uIn u 2 * n (projIcc 0 U hU u) - zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2) (Icc 0 U) u)
    (v : Icc 0 V) :
    let N := radialVelocityField hV e Λ n zIn x.1 hr
    AbsolutelyContinuousOnInterval (fun t => intervalExtension hU N t v *
      Real.exp (-intervalExtension hU x.1 t v 2)) 0 U ∧
    IntervalIntegrable (fun t => intervalExtension hU x.1 t v 0 *
      Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2) volume 0 U ∧
    ∀ u : Icc 0 U, N u v * Real.exp (-x.1 u v 2) =
      N ⟨0, le_rfl, hU⟩ v * Real.exp (-x.1 ⟨0, le_rfl, hU⟩ v 2) -
        ∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 *
          Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2 := by
  let N := radialVelocityField hV e Λ n zIn x.1 hr
  let Q := fun t => intervalExtension hU N t v * Real.exp (-intervalExtension hU x.1 t v 2)
  let ρ := fun t => intervalExtension hU x.1 t v 0 *
    Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2
  have hziAC : AbsolutelyContinuousOnInterval (intervalExtension hU zIn) 0 U := by
    rw [hzin, map_add]
    exact horizontalPrimitive_absolutelyContinuous hU uIn c
  let E : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj (0 : Fin 3)
  have hinit : AbsolutelyContinuousOnInterval (fun t => intervalExtension hU zIn t 0) 0 U :=
    absolutelyContinuous_comp_contDiffAt (g := E) hziAC (fun _ _ => E.contDiff.contDiffAt)
  let F := fun z : C(Icc 0 V, WaveVector) => Real.exp (-z v 2) / z v 0
  have hF : ∀ z ∈ (intervalExtension hU x.1) '' uIcc (0 : ℝ) U, ContDiffAt ℝ 1 F z := by
    intro z hz
    obtain ⟨t, _ht, rfl⟩ := hz
    let T (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v)
    exact (Real.contDiff_exp.contDiffAt.comp _ (T 2).contDiff.contDiffAt.neg).div
      (T 0).contDiff.contDiffAt (hr (projIcc 0 U hU t) v)
  have hfac := absolutelyContinuous_comp_contDiffAt (hx.horizontal_absolutelyContinuous hzin) hF
  have hn1 : AbsolutelyContinuousOnInterval (fun t => intervalExtension hU n t + 1) 0 U :=
    absolutelyContinuous_comp_contDiffAt hnAC (g := fun r : ℝ => r + 1)
      (fun _ _ => contDiffAt_id.add contDiffAt_const)
  have hc : AbsolutelyContinuousOnInterval Q 0 U := by
    have hh := (hx.weightedNu_absolutelyContinuous hr hzin v).add ((hinit.mul hn1).mul hfac)
    have he : (fun t => intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v *
        Real.exp (-intervalExtension hU x.1 t v 2) +
        (intervalExtension hU zIn t 0 * (intervalExtension hU n t + 1)) *
          F (intervalExtension hU x.1 t)) = Q := by
      funext t
      change ((-zIn (projIcc 0 U hU t) 0 + continuousPrimitive hV
          (radialFluxField e Λ x.1 hr (projIcc 0 U hU t)) v) / x.1 (projIcc 0 U hU t) v 0) *
          Real.exp (-x.1 (projIcc 0 U hU t) v 2) +
        (zIn (projIcc 0 U hU t) 0 * (n (projIcc 0 U hU t) + 1)) *
          (Real.exp (-x.1 (projIcc 0 U hU t) v 2) / x.1 (projIcc 0 U hU t) v 0) =
        ((zIn (projIcc 0 U hU t) 0 * n (projIcc 0 U hU t) + continuousPrimitive hV
          (radialFluxField e Λ x.1 hr (projIcc 0 U hU t)) v) / x.1 (projIcc 0 U hU t) v 0) *
          Real.exp (-x.1 (projIcc 0 U hU t) v 2)
      ring
    exact he ▸ hh
  have hconstraint := (hx.general_radial_constraint hr hzin n hn hnd).2.2
  have he : deriv Q =ᵐ[volume.restrict (Icc 0 U)] fun t => -ρ t := by
    filter_upwards [hconstraint, hx.horizontal_derivative hzin, ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc 0 U)).ae_ne 0, (volume.restrict (Icc 0 U)).ae_ne U]
      with t hn hz ht ht0 htU
    let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
    have hl := T.hasFDerivAt.comp_hasDerivWithinAt t hz
    have hh := (hn v).mul (Real.hasDerivAt_exp _ |>.comp_hasDerivWithinAt t hl.neg)
    have hd : HasDerivWithinAt Q (-ρ t) (Icc 0 U) t := by
      apply hh.congr_deriv
      change (x.2.2 t v 2 * N (projIcc 0 U hU t) v -
          x.1 (projIcc 0 U hU t) v 0 * (x.2.2 t v 1) ^ 2) *
          Real.exp (-intervalExtension hU x.1 t v 2) +
        intervalExtension hU N t v * (Real.exp (-intervalExtension hU x.1 t v 2) * (-x.2.2 t v 2)) = -ρ t
      simp only [intervalExtension_apply, ρ]
      ring
    exact (hd.hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne ht.1 ht0.symm)
      (lt_of_le_of_ne ht.2 htU))).deriv
  have hs : uIoc (0 : ℝ) U ⊆ Icc 0 U := by rw [uIoc_of_le hU]; exact Ioc_subset_Icc_self
  have hi := hc.intervalIntegrable_deriv.congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) he)
  refine ⟨hc, ?_, fun u => ?_⟩
  · have hh := hi.neg
    change IntervalIntegrable (fun t => -(-ρ t)) volume 0 U at hh
    simpa only [neg_neg, ρ] using hh
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
