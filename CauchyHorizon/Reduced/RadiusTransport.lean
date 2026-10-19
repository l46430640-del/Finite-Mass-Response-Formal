import CauchyHorizon.Reduced.RadialRegularity
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! The lapse derivative and the inverse outgoing speed along radius curves. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.kappa_longitudinal_derivative
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (u : Icc 0 U) (v : Icc 0 V) (hn : radialNuField hV e Λ zIn x.1 hr u v ≠ 0) :
    let ν := radialNuField hV e Λ zIn x.1 hr
    let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) /
      (4 * intervalExtension hV (ν u) t)
    HasDerivWithinAt κ (κ v * (x.2.1 u v 2 -
      radialSourceField e Λ x.1 x.2.1 ν hr u v / ν u v)) (Icc 0 V) v := by
  let ν := radialNuField hV e Λ zIn x.1 hr
  have hE := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
    (v : ℝ) (hx.longitudinal_derivative u v.property)
  have hN := hx.radialNu_hasDerivWithinAt hr u v
  have hnonzero : 4 * intervalExtension hV (ν u) v ≠ 0 := by
    simpa only [intervalExtension_apply, projIcc_of_mem hV v.property] using
      mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hn
  have hd := hE.exp.neg.div (hN.const_mul 4) hnonzero
  apply hd.congr_deriv
  simp only [Function.comp_apply, ContinuousLinearMap.proj_apply, Pi.neg_apply,
    intervalExtension_apply, projIcc_of_mem hV v.property]
  field_simp [hn]
  ring

set_option maxHeartbeats 800000 in
theorem IsWaveIntegral.inverse_lambda_curve_derivative
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hl : ∀ (u : Icc 0 U) (v : Icc 0 V),
      HasDerivWithinAt (fun t => intervalExtension hV (x.2.1 u) t 0)
        (x.2.1 u v 2 * x.2.1 u v 0 - x.1 u v 0 * (x.2.1 u v 1) ^ 2) (Icc 0 V) v)
    (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ∈ Ioo 0 U) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hl0 : x.2.1 u v 0 ≠ 0)
    {S : Set ℝ} {g : ℝ → ℝ} (hgv : g v = u)
    (hg : HasDerivWithinAt g (-x.2.1 u v 0 / radialNuField hV e Λ zIn x.1 hr u v) S v) :
    let ν := radialNuField hV e Λ zIn x.1 hr
    HasDerivWithinAt (fun t => -1 / intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 0)
      ((x.2.1 u v 2 - radialSourceField e Λ x.1 x.2.1 ν hr u v / ν u v) / x.2.1 u v 0 -
        x.1 u v 0 * (x.2.1 u v 1) ^ 2 / (x.2.1 u v 0) ^ 2) S v := by
  let ν := radialNuField hV e Λ zIn x.1 hr
  let G := radialSourceField e Λ x.1 x.2.1 ν hr
  let F := fun q t : ℝ => intervalExtension hV (intervalExtension hU x.2.1 q) t 0
  let dU := fun q t : ℝ => ContinuousLinearMap.toSpanSingleton ℝ
    (intervalExtension hV (intervalExtension hU G q) t)
  let dV := fun q t : ℝ => ContinuousLinearMap.toSpanSingleton ℝ
    (intervalExtension hV (intervalExtension hU x.2.1 q) t 2 * F q t -
      intervalExtension hV (intervalExtension hU x.1 q) t 0 *
        (intervalExtension hV (intervalExtension hU x.2.1 q) t 1) ^ 2)
  have hcU : Continuous (Function.uncurry dU) := by
    change Continuous (fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ
      (intervalExtension hV (intervalExtension hU G p.1) p.2))
    fun_prop
  have hcV : Continuous (Function.uncurry dV) := by
    change Continuous (fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ
      (intervalExtension hV (intervalExtension hU x.2.1 p.1) p.2 2 * F p.1 p.2 -
        intervalExtension hV (intervalExtension hU x.1 p.1) p.2 0 *
          (intervalExtension hV (intervalExtension hU x.2.1 p.1) p.2 1) ^ 2))
    dsimp only [F]
    fun_prop
  have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 ((u : ℝ), (v : ℝ)), p ∈ Ioo 0 U ×ˢ Ioo 0 V :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hu, hv⟩
  have hdU : ∀ᶠ p : ℝ × ℝ in 𝓝 ((u : ℝ), (v : ℝ)),
      HasFDerivAt (F · p.2) (dU p.1 p.2) p.1 := by
    filter_upwards [hnear] with p hp
    have hpU : p.1 ∈ Icc 0 U := ⟨hp.1.1.le, hp.1.2.le⟩
    have hpV : p.2 ∈ Icc 0 V := ⟨hp.2.1.le, hp.2.2.le⟩
    simpa only [F, dU, G, intervalExtension_apply, projIcc_of_mem hV hpV, projIcc_of_mem hU hpU] using
      ((hx.lambda_hasDerivWithinAt hr hinu ⟨p.2, hpV⟩ hpU).hasDerivAt
        (Icc_mem_nhds hp.1.1 hp.1.2)).hasFDerivAt
  have hdV : ∀ᶠ p : ℝ × ℝ in 𝓝 ((u : ℝ), (v : ℝ)),
      HasFDerivAt (F p.1 ·) (dV p.1 p.2) p.2 := by
    filter_upwards [hnear] with p hp
    have hpU : p.1 ∈ Icc 0 U := ⟨hp.1.1.le, hp.1.2.le⟩
    have hpV : p.2 ∈ Icc 0 V := ⟨hp.2.1.le, hp.2.2.le⟩
    simpa only [F, dV, intervalExtension_apply, projIcc_of_mem hV hpV, projIcc_of_mem hU hpU] using
      ((hl ⟨p.1, hpU⟩ ⟨p.2, hpV⟩).hasDerivAt (Icc_mem_nhds hp.2.1 hp.2.2)).hasFDerivAt
  have hF := (hasStrictFDerivAt_uncurry_coprod (f := F) (f₁ := dU) (f₂ := dV)
    (u := ((u : ℝ), (v : ℝ))) hdU hdV hcU.continuousAt hcV.continuousAt).hasFDerivAt
  have hpair : HasDerivWithinAt (fun t => (g t, t))
      (-x.2.1 u v 0 / ν u v, 1) S v := hg.prodMk (hasDerivWithinAt_id (v : ℝ) S)
  have hd := hF.comp_hasDerivWithinAt_of_eq (v : ℝ) hpair (Prod.ext hgv.symm rfl)
  have hFv : F (g v) v = x.2.1 u v 0 := by
    simp only [F, hgv, intervalExtension_apply, projIcc_of_mem hU u.property, projIcc_of_mem hV v.property]
  have hd' := (hasDerivWithinAt_const (v : ℝ) S (-1 : ℝ)).div hd (by exact hFv.trans_ne hl0)
  apply hd'.congr_deriv
  change (0 * F (g v) v - -1 * (dU u v (-x.2.1 u v 0 / ν u v) + dV u v 1)) /
    (F (g v) v) ^ 2 = (x.2.1 u v 2 - G u v / ν u v) / x.2.1 u v 0 -
      x.1 u v 0 * (x.2.1 u v 1) ^ 2 / (x.2.1 u v 0) ^ 2
  rw [hFv]
  dsimp only [dU, dV, F]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    intervalExtension_apply, projIcc_of_mem hU u.property, projIcc_of_mem hV v.property]
  field_simp [hl0]
  ring

theorem IsWaveIntegral.inverse_lambda_coefficient_eq
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (u : Icc 0 U) (v : Icc 0 V) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hn : radialNuField hV e Λ zIn x.1 hx.choose u v ≠ 0) (hl : x.2.1 u v 0 ≠ 0) :
    let ν := radialNuField hV e Λ zIn x.1 hx.choose
    let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) /
      (4 * intervalExtension hV (ν u) t)
    (x.2.1 u v 2 - radialSourceField e Λ x.1 x.2.1 ν hx.choose u v / ν u v) / x.2.1 u v 0 -
      x.1 u v 0 * (x.2.1 u v 1) ^ 2 / (x.2.1 u v 0) ^ 2 =
        (deriv κ v / κ v) / x.2.1 u v 0 -
          (x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2) := by
  intro ν κ
  have hk : κ v ≠ 0 := by
    simp only [κ, intervalExtension_apply, projIcc_of_mem hV v.property]
    exact div_ne_zero (neg_ne_zero.2 (Real.exp_ne_zero _)) (mul_ne_zero (by norm_num) hn)
  have hd := (hx.kappa_longitudinal_derivative hx.choose u v hn).hasDerivAt
    (Icc_mem_nhds hv.1 hv.2)
  change HasDerivAt κ (κ v * (x.2.1 u v 2 -
    radialSourceField e Λ x.1 x.2.1 ν hx.choose u v / ν u v)) v at hd
  rw [hd.deriv]
  field_simp [hk, hl, hx.choose u v]

end CauchyHorizon
