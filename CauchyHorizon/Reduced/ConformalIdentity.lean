import CauchyHorizon.Reduced.KappaRegularity
import CauchyHorizon.Reduced.MassFlux
import CauchyHorizon.Characteristic.Outgoing

/-! The exact horizontal conformal identity for the actual rough integral solution. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 300000 in
theorem IsWaveIntegral.conformal_horizontal_identity {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v ≠ 0) (v : Icc 0 V) :
    let N := radialNuField hV e Λ zIn x.1 hr
    let R := fun t => intervalExtension hU x.1 t v 0
    let m := fun t => intervalExtension hU (massField e Λ x.1 x.2.1 N hr) t v
    let κ := fun t => -Real.exp (intervalExtension hU x.1 t v 2) / (4 * intervalExtension hU N t v)
    let K := fun t => horizonK (R t) (m t) e Λ
    let S := fun t => 2 * K t * deriv κ t + 2 * κ t * deriv m t / (R t) ^ 2 +
      2 * x.2.2 t v 1 * intervalExtension hU x.2.1 t v 1
    IntervalIntegrable S volume 0 U ∧ ∀ a b : Icc 0 U, a ≤ b →
      (x.2.1 b v 2 - 2 * K b) - (x.2.1 a v 2 - 2 * K a) =
        2 * K b * (κ b - 1) - 2 * K a * (κ a - 1) - ∫ t in (a : ℝ)..b, S t := by
  let N := radialNuField hV e Λ zIn x.1 hr
  let R := fun t => intervalExtension hU x.1 t v 0
  let m := fun t => intervalExtension hU (massField e Λ x.1 x.2.1 N hr) t v
  let κ := fun t => -Real.exp (intervalExtension hU x.1 t v 2) / (4 * intervalExtension hU N t v)
  let K := fun t => horizonK (R t) (m t) e Λ
  let W := fun t => intervalExtension hU x.2.1 t v 2
  let F := fun t => W t - 2 * (κ t * K t)
  let S := fun t => 2 * K t * deriv κ t + 2 * κ t * deriv m t / (R t) ^ 2 +
    2 * x.2.2 t v 1 * intervalExtension hU x.2.1 t v 1
  let T (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v)
  have hRc : AbsolutelyContinuousOnInterval R 0 U :=
    absolutelyContinuous_comp_contDiffAt (g := T 0) (hx.horizontal_absolutelyContinuous hzin)
      (fun _ _ => (T 0).contDiff.contDiffAt)
  have hRi : AbsolutelyContinuousOnInterval (fun t => (R t)⁻¹) 0 U := by
    apply absolutelyContinuous_comp_contDiffAt (g := fun y : ℝ => y⁻¹) hRc
    rintro y ⟨t, _ht, rfl⟩
    exact contDiffAt_id.inv (hr (projIcc 0 U hU t) v)
  have hmc : AbsolutelyContinuousOnInterval m 0 U := hx.mass_horizontal_absolutelyContinuous hr hzin v
  obtain ⟨hκc, hκd⟩ := hx.kappa_horizontal_regular hr hzin hinu hinell hnu v
  have hKc : AbsolutelyContinuousOnInterval K 0 U := by
    have he : K = fun t => m t * ((R t)⁻¹ * (R t)⁻¹) -
        e ^ 2 * (((R t)⁻¹ * (R t)⁻¹) * (R t)⁻¹) - (Λ / 3) * R t := by
      funext t
      dsimp only [K, horizonK]
      ring
    rw [he]
    exact ((hmc.mul (hRi.mul hRi)).sub (((hRi.mul hRi).mul hRi).const_mul (e ^ 2))).sub
      (hRc.const_mul (Λ / 3))
  have hWc : AbsolutelyContinuousOnInterval W 0 U :=
    absolutelyContinuous_comp_contDiffAt (g := T 2) hx.velocity_horizontal_absolutelyContinuous
      (fun _ _ => (T 2).contDiff.contDiffAt)
  have hFc : AbsolutelyContinuousOnInterval F 0 U := hWc.sub ((hκc.mul hKc).const_mul 2)
  have hd : deriv F =ᵐ[volume.restrict (Icc 0 U)] fun t => -S t := by
    filter_upwards [hκd, hx.mass_horizontal_derivative hr hzin hinu hinell,
      hx.wave_equation, hx.radialNu_ae hr hinu, ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc 0 U)).ae_ne 0, (volume.restrict (Icc 0 U)).ae_ne U]
      with t hk hm hw hn ht ht0 htU
    have hnhds := Icc_mem_nhds (lt_of_le_of_ne ht.1 ht0.symm) (lt_of_le_of_ne ht.2 htU)
    have hk' : HasDerivWithinAt κ (deriv κ t) (Icc 0 U) t :=
      (hk.hasDerivAt hnhds).differentiableAt.hasDerivAt.hasDerivWithinAt
    have hm' : HasDerivWithinAt m (deriv m t) (Icc 0 U) t :=
      ((hm v).hasDerivAt hnhds).differentiableAt.hasDerivAt.hasDerivWithinAt
    have hR := hx.radial_hasDerivWithinAt hr hzin hinu v ht
    have hrr : R t ≠ 0 := hr (projIcc 0 U hU t) v
    have hK := ((hm'.div (hR.pow 2) (pow_ne_zero 2 hrr)).sub
      ((hasDerivWithinAt_const t (Icc 0 U) (e ^ 2)).div (hR.pow 3) (pow_ne_zero 3 hrr))).sub
        ((hR.const_mul Λ).div_const 3)
    have hW := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hw v)
    have hh := hW.sub ((hk'.mul hK).const_mul 2)
    have he : HasDerivWithinAt F (-S t) (Icc 0 U) t := by
      apply hh.congr_deriv
      dsimp only [S]
      generalize deriv κ t = dk
      generalize deriv m t = dm
      simp only [Pi.sub_apply, Pi.div_apply, Pi.pow_apply, ContinuousLinearMap.proj_apply,
        waveSource, Matrix.cons_val, hn v, R, κ, K, m, N, intervalExtension_apply,
        projIcc_of_mem hU ht, massField_apply, horizonK, renormalizedMass, conformalPotential, Real.exp_neg]
      have hn0 := hnu ⟨t, ht⟩ v
      have hr0 := hr ⟨t, ht⟩ v
      field_simp [hn0, hr0, Real.exp_ne_zero]
      ring
    exact (he.hasDerivAt hnhds).deriv
  have hsu : uIoc (0 : ℝ) U ⊆ Icc 0 U := by rw [uIoc_of_le hU]; exact Ioc_subset_Icc_self
  have hSi : IntervalIntegrable S volume 0 U := by
    have hh := hFc.intervalIntegrable_deriv.congr_ae (ae_mono (Measure.restrict_mono hsu le_rfl) hd)
    simpa only [neg_neg] using (show IntervalIntegrable (-S) volume 0 U from hh).neg
  refine ⟨hSi, ?_⟩
  intro a b hab
  have hsub : uIcc (a : ℝ) b ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le (show (a : ℝ) ≤ b from hab), uIcc_of_le hU]
    exact Icc_subset_Icc a.property.1 b.property.2
  have hp := (hFc.mono hsub).integral_deriv_eq_sub
  have hs : Ioc (a : ℝ) b ⊆ Icc 0 U := fun _ ht => ⟨a.property.1.trans ht.1.le, ht.2.trans b.property.2⟩
  rw [intervalIntegral.integral_of_le (show (a : ℝ) ≤ b from hab),
    integral_congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) hd),
    ← intervalIntegral.integral_of_le (show (a : ℝ) ≤ b from hab), intervalIntegral.integral_neg] at hp
  simp only [F, W, intervalExtension_apply, projIcc_of_mem hU a.property, projIcc_of_mem hU b.property] at hp
  dsimp only
  change _ = 2 * K b * (κ b - 1) - 2 * K a * (κ a - 1) - ∫ t in (a : ℝ)..b, S t
  nlinarith only [hp]

end CauchyHorizon
