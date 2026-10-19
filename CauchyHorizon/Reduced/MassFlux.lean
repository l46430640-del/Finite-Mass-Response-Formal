import CauchyHorizon.Reduced.ConstraintIntegral
import CauchyHorizon.Reduced.LongitudinalConstraint
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! The renormalized mass and its fluxes for the actual mixed-regularity solution. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

noncomputable def renormalizedMass (r ν l ell e Λ : ℝ) : ℝ :=
  r / 2 + e ^ 2 / (2 * r) - Λ * r ^ 3 / 6 + 2 * r * ν * l * Real.exp (-ell)

theorem renormalizedMass_symm (r ν l ell e Λ : ℝ) :
    renormalizedMass r ν l ell e Λ = renormalizedMass r l ν ell e Λ := by
  unfold renormalizedMass
  ring

theorem renormalizedMass_horizonFunction {r : ℝ} (hr : r ≠ 0) (ν l ell e Λ : ℝ) :
    horizonFunction r (renormalizedMass r ν l ell e Λ) e Λ = -4 * ν * l * Real.exp (-ell) := by
  unfold horizonFunction renormalizedMass
  field_simp [hr]
  ring

theorem renormalizedMass_flux_forms {r ν : ℝ} (hr : r ≠ 0) (hν : ν ≠ 0) (l ell ψ e Λ : ℝ) :
    -2 * r ^ 2 * ν * Real.exp (-ell) * ψ ^ 2 = (r * ψ) ^ 2 / (2 * (-Real.exp ell / (4 * ν))) ∧
    -2 * r ^ 2 * l * Real.exp (-ell) * ψ ^ 2 =
      horizonFunction r (renormalizedMass r ν l ell e Λ) e Λ * (r * ψ) ^ 2 / (2 * ν) := by
  rw [renormalizedMass_horizonFunction hr]
  constructor <;> rw [Real.exp_neg] <;> field_simp [hν, Real.exp_ne_zero] <;> ring

-- Swapping the two null derivatives gives the second flux from the same calculation.
theorem renormalizedMass_hasDerivWithinAt {R N L E : ℝ → ℝ} {s : Set ℝ} {t a ψ e Λ : ℝ}
    (hr : R t ≠ 0) (hR : HasDerivWithinAt R (N t) s t)
    (hN : HasDerivWithinAt N (a * N t - R t * ψ ^ 2) s t)
    (hL : HasDerivWithinAt L (Real.exp (E t) * radialPotential (R t) e Λ - N t * L t / R t) s t)
    (hE : HasDerivWithinAt E a s t) :
    HasDerivWithinAt (fun w => renormalizedMass (R w) (N w) (L w) (E w) e Λ)
      (-2 * (R t) ^ 2 * L t * Real.exp (-E t) * ψ ^ 2) s t := by
  have hd := (((hR.div_const 2).add ((hasDerivWithinAt_const t s (e ^ 2)).div (hR.const_mul 2)
    (mul_ne_zero (by norm_num) hr))).sub (((hR.pow 3).const_mul Λ).div_const 6)).add
      (((hR.const_mul 2).mul hN).mul hL |>.mul hE.neg.exp)
  apply hd.congr_deriv
  simp only [Pi.mul_apply, Pi.neg_apply, radialPotential, Real.exp_neg]
  field_simp [hr, Real.exp_ne_zero]
  ring

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

noncomputable def massField (e Λ : ℝ) (z w : WaveRectangle U V)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (hr : ∀ u v, z u v 0 ≠ 0) :
    C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  (⟨fun q : Icc 0 U × Icc 0 V => renormalizedMass (z.uncurry q 0) (ν.uncurry q)
      (w.uncurry q 0) (z.uncurry q 2) e Λ, by
    unfold renormalizedMass
    have hR := (continuous_apply (0 : Fin 3)).comp z.uncurry.continuous
    have hL := (continuous_apply (0 : Fin 3)).comp w.uncurry.continuous
    have hE := (continuous_apply (2 : Fin 3)).comp z.uncurry.continuous
    have hI := (continuous_const (y := e ^ 2)).div (hR.const_mul 2)
      (fun q => mul_ne_zero (by norm_num) (hr q.1 q.2))
    exact ((hR.div_const 2).add hI |>.sub ((hR.pow 3).const_mul Λ |>.div_const 6)).add
      ((((hR.const_mul 2).mul ν.uncurry.continuous).mul hL).mul (Real.continuous_exp.comp hE.neg))⟩ :
    C(Icc 0 U × Icc 0 V, ℝ)).curry

theorem massField_apply (e Λ : ℝ) (z w : WaveRectangle U V)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (hr : ∀ u v, z u v 0 ≠ 0) (u : Icc 0 U) (v : Icc 0 V) :
    massField e Λ z w ν hr u v = renormalizedMass (z u v 0) (ν u v) (w u v 0) (z u v 2) e Λ := rfl

theorem IsWaveIntegral.mass_horizontal_derivative
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2) :
    let N := radialNuField hV e Λ zIn x.1 hr
    let m := massField e Λ x.1 x.2.1 N hr
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      HasDerivWithinAt (fun t => intervalExtension hU m t v)
        (-2 * (intervalExtension hU x.1 u v 0) ^ 2 * intervalExtension hU x.2.1 u v 0 *
          Real.exp (-intervalExtension hU x.1 u v 2) * (x.2.2 u v 1) ^ 2) (Icc 0 U) u := by
  dsimp only
  filter_upwards [hx.transverse_constraint hr hzin hinu hinell, hx.horizontal_derivative hzin,
    ae_restrict_mem measurableSet_Icc] with t hn hz ht
  intro v
  let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  have hE := T.hasFDerivAt.comp_hasDerivWithinAt t hz
  have hR := hx.radial_hasDerivWithinAt hr hzin hinu v ht
  have hL := hx.lambda_hasDerivWithinAt hr hinu v ht
  have hN := hn v
  have hd := renormalizedMass_hasDerivWithinAt
    (R := fun s => intervalExtension hU x.1 s v 0)
    (N := fun s => intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) s v)
    (L := fun s => intervalExtension hU x.2.1 s v 0)
    (E := fun s => intervalExtension hU x.1 s v 2)
    (ψ := x.2.2 t v 1) (hr (projIcc 0 U hU t) v)
    (by simpa only [intervalExtension_apply, projIcc_of_mem hU ht] using hR) hN
    (by simpa only [intervalExtension_apply, projIcc_of_mem hU ht, radialSourceField_apply] using hL) hE
  exact hd

theorem IsWaveIntegral.mass_longitudinal_derivative
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (u : Icc 0 U) (v : Icc 0 V)
    (hl : HasDerivWithinAt (fun t => intervalExtension hV (x.2.1 u) t 0)
      (x.2.1 u v 2 * x.2.1 u v 0 - x.1 u v 0 * (x.2.1 u v 1) ^ 2) (Icc 0 V) v) :
    let N := radialNuField hV e Λ zIn x.1 hr
    HasDerivWithinAt (intervalExtension hV (massField e Λ x.1 x.2.1 N hr u))
      (-2 * (x.1 u v 0) ^ 2 * N u v * Real.exp (-x.1 u v 2) * (x.2.1 u v 1) ^ 2) (Icc 0 V) v := by
  dsimp only
  have hz := hx.longitudinal_derivative u v.property
  have hR := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt (v : ℝ) hz
  have hE := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt (v : ℝ) hz
  change HasDerivWithinAt (fun s => intervalExtension hV (x.1 u) s 0) (x.2.1 u v 0) (Icc 0 V) v at hR
  change HasDerivWithinAt (fun s => intervalExtension hV (x.1 u) s 2) (x.2.1 u v 2) (Icc 0 V) v at hE
  have hN := hx.radialNu_hasDerivWithinAt hr u v
  have hd := renormalizedMass_hasDerivWithinAt
    (R := fun s => intervalExtension hV (x.1 u) s 0)
    (N := fun s => intervalExtension hV (x.2.1 u) s 0)
    (L := intervalExtension hV (radialNuField hV e Λ zIn x.1 hr u))
    (E := fun s => intervalExtension hV (x.1 u) s 2)
    (ψ := x.2.1 u v 1)
    (by simpa only [intervalExtension_apply, projIcc_of_mem hV v.property] using hr u v)
    (by simpa only [intervalExtension_apply, projIcc_of_mem hV v.property] using hR)
    (by simpa only [intervalExtension_apply, projIcc_of_mem hV v.property] using hl)
    (by simpa only [intervalExtension_apply, projIcc_of_mem hV v.property, radialSourceField_apply, mul_comm] using hN) hE
  simp only [intervalExtension_apply, projIcc_of_mem hV v.property] at hd
  apply hd.congr_of_mem _ v.property
  intro t _ht
  exact renormalizedMass_symm _ _ _ _ _ _

theorem IsWaveIntegral.mass_horizontal_absolutelyContinuous
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (v : Icc 0 V) :
    AbsolutelyContinuousOnInterval (fun t => intervalExtension hU
      (massField e Λ x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr) t v) 0 U := by
  let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  let G : C(Icc 0 V, WaveVector) → ℝ := fun z => T z / 2 + e ^ 2 / (2 * T z) - Λ * T z ^ 3 / 6
  have hG : ∀ z ∈ (intervalExtension hU x.1) '' uIcc (0 : ℝ) U, ContDiffAt ℝ 1 G z := by
    rintro z ⟨t, _ht, rfl⟩
    have hR := T.contDiff.contDiffAt (x := intervalExtension hU x.1 t) (n := 1)
    have hn : 2 * T (intervalExtension hU x.1 t) ≠ 0 :=
      mul_ne_zero (by norm_num) (hr (projIcc 0 U hU t) v)
    exact ((hR.div_const 2).add (contDiffAt_const.div (contDiffAt_const.mul hR) hn)).sub
      (contDiffAt_const.mul (hR.pow 3) |>.div_const 6)
  have hB := absolutelyContinuous_comp_contDiffAt (hx.horizontal_absolutelyContinuous hzin) hG
  have hR := absolutelyContinuous_comp_contDiffAt (hx.horizontal_absolutelyContinuous hzin)
    (fun _ _ => T.contDiff.contDiffAt (n := 1))
  have hL := absolutelyContinuous_comp_contDiffAt hx.velocity_horizontal_absolutelyContinuous
    (fun _ _ => T.contDiff.contDiffAt (n := 1))
  have hM := hB.add (((hR.mul hL).mul (hx.weightedNu_absolutelyContinuous hr hzin v)).const_mul 2)
  have he : (fun t => intervalExtension hU
      (massField e Λ x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr) t v) =
      G ∘ intervalExtension hU x.1 + fun t => 2 *
        ((T ∘ intervalExtension hU x.1) t * (T ∘ intervalExtension hU x.2.1) t *
          (intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v *
            Real.exp (-intervalExtension hU x.1 t v 2))) := by
    funext t
    simp only [intervalExtension_apply, massField_apply, renormalizedMass, Pi.add_apply,
      Function.comp_apply, G, T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousMap.evalCLM_apply]
    ring
  rw [he]
  exact hM

theorem IsWaveIntegral.mass_horizontal_integral
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2)
    (v : Icc 0 V) :
    let m := massField e Λ x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr
    let J := fun t => -2 * (intervalExtension hU x.1 t v 0) ^ 2 * intervalExtension hU x.2.1 t v 0 *
      Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2
    IntervalIntegrable J volume 0 U ∧ ∀ u : Icc 0 U,
      m u v = m ⟨0, le_rfl, hU⟩ v + ∫ t in (0 : ℝ)..u, J t := by
  let m := massField e Λ x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr
  let Q := fun t => intervalExtension hU m t v
  let J := fun t => -2 * (intervalExtension hU x.1 t v 0) ^ 2 * intervalExtension hU x.2.1 t v 0 *
    Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2
  have hc : AbsolutelyContinuousOnInterval Q 0 U := hx.mass_horizontal_absolutelyContinuous hr hzin v
  have he : deriv Q =ᵐ[volume.restrict (Icc 0 U)] J := by
    filter_upwards [hx.mass_horizontal_derivative hr hzin hinu hinell,
      ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc 0 U)).ae_ne 0,
      (volume.restrict (Icc 0 U)).ae_ne U] with t hd ht ht0 htU
    exact ((hd v).hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne ht.1 ht0.symm)
      (lt_of_le_of_ne ht.2 htU))).deriv
  have hs : uIoc (0 : ℝ) U ⊆ Icc 0 U := by rw [uIoc_of_le hU]; exact Ioc_subset_Icc_self
  refine ⟨hc.intervalIntegrable_deriv.congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) he), ?_⟩
  intro u
  have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le u.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl u.property.2
  have hp := (hc.mono hsub).integral_deriv_eq_sub
  have hs' : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
  rw [intervalIntegral.integral_of_le u.property.1,
    integral_congr_ae (ae_mono (Measure.restrict_mono hs' le_rfl) he),
    ← intervalIntegral.integral_of_le u.property.1] at hp
  simp only [Q, intervalExtension_apply, projIcc_of_mem hU u.property,
    projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩)] at hp
  change m u v = m ⟨0, le_rfl, hU⟩ v + ∫ t in (0 : ℝ)..u, J t
  linarith only [hp]

theorem IsWaveIntegral.mass_longitudinal_integral
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (u : Icc 0 U)
    (hl : ∀ v : Icc 0 V, HasDerivWithinAt (fun t => intervalExtension hV (x.2.1 u) t 0)
      (x.2.1 u v 2 * x.2.1 u v 0 - x.1 u v 0 * (x.2.1 u v 1) ^ 2) (Icc 0 V) v)
    (v : Icc 0 V) :
    let N := radialNuField hV e Λ zIn x.1 hr
    let m := massField e Λ x.1 x.2.1 N hr
    m u v = m u ⟨0, le_rfl, hV⟩ + ∫ t in (0 : ℝ)..v,
      -2 * (intervalExtension hV (x.1 u) t 0) ^ 2 * intervalExtension hV (N u) t *
        Real.exp (-intervalExtension hV (x.1 u) t 2) * (intervalExtension hV (x.2.1 u) t 1) ^ 2 := by
  let N := radialNuField hV e Λ zIn x.1 hr
  let m := massField e Λ x.1 x.2.1 N hr
  let J : C(Icc 0 V, ℝ) := ⟨fun w => -2 * (x.1 u w 0) ^ 2 * N u w *
    Real.exp (-x.1 u w 2) * (x.2.1 u w 1) ^ 2, by
      have hR := (continuous_apply (0 : Fin 3)).comp (x.1 u).continuous
      have hE := (continuous_apply (2 : Fin 3)).comp (x.1 u).continuous
      have hP := (continuous_apply (1 : Fin 3)).comp (x.2.1 u).continuous
      exact ((((hR.pow 2).const_mul (-2)).mul (N u).continuous).mul
        (Real.continuous_exp.comp hE.neg)).mul (hP.pow 2)⟩
  have hd (t : ℝ) (ht : t ∈ Icc 0 V) :
      HasDerivWithinAt (intervalExtension hV (m u)) (intervalExtension hV J t) (Icc 0 V) t := by
    simpa only [intervalExtension_apply, projIcc_of_mem hV ht, J, m, N, ContinuousMap.coe_mk] using
      hx.mass_longitudinal_derivative hr u ⟨t, ht⟩ (hl ⟨t, ht⟩)
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le v.property.1
    (intervalExtension hV (m u)).continuous.continuousOn
    (fun t ht => (hd t ⟨ht.1.le, ht.2.le.trans v.property.2⟩).hasDerivAt
      (Icc_mem_nhds ht.1 (ht.2.trans_le v.property.2)))
    ((intervalExtension hV J).continuous.intervalIntegrable (0 : ℝ) v)
  simp only [intervalExtension_apply, projIcc_of_mem hV v.property,
    projIcc_of_mem hV (show (0 : ℝ) ∈ Icc 0 V from ⟨le_rfl, hV⟩)] at hp
  change m u v = m u ⟨0, le_rfl, hV⟩ + ∫ t in (0 : ℝ)..v, intervalExtension hV J t
  change (∫ t in (0 : ℝ)..v, intervalExtension hV J t) = m u v - m u ⟨0, le_rfl, hV⟩ at hp
  linarith only [hp]

end CauchyHorizon
