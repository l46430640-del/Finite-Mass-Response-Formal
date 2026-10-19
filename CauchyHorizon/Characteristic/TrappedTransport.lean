import CauchyHorizon.Characteristic.OutgoingConstraint
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exact outgoing transport after trapping, at the actual characteristic regularity. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.trapped_q_transport {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0) :
    let J := fun t => intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)
    let q := fun v => Real.exp (x.1 u v 2) / (4 * (-x.2.1 u v 0))
    IntervalIntegrable J volume a b ∧ 0 ≤ ∫ t in (a : ℝ)..b, J t ∧
      q b = q a * Real.exp (-(∫ t in (a : ℝ)..b, J t)) ∧ 0 < q b ∧ q b ≤ q a ∧
      -x.2.1 u b 0 = -x.2.1 u a 0 *
        Real.exp (x.1 u b 2 - x.1 u a 2 + ∫ t in (a : ℝ)..b, J t) := by
  let R : ℝ → ℝ := fun t => intervalExtension hV (x.1 u) t 0
  let E : ℝ → ℝ := fun t => intervalExtension hV (x.1 u) t 2
  let L : ℝ → ℝ := fun t => intervalExtension hV (x.2.1 u) t 0
  let P : ℝ → ℝ := fun t => intervalExtension hV (x.2.1 u) t 1
  let J : ℝ → ℝ := fun t => R t * (P t) ^ 2 / (-L t)
  let F : ℝ → ℝ := fun t => E t - Real.log (-L t)
  have hsub : Icc (a : ℝ) b ⊆ Icc 0 V :=
    fun _ ht => ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
  have hL (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) : L t < 0 := by
    simpa only [L, intervalExtension_apply, projIcc_of_mem hV (hsub ht)] using
      (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a ⟨t, hsub ht⟩ ht.1 ha).1
  have hEc : Continuous E := by fun_prop
  have hLc : Continuous L := by fun_prop
  have hJc : ContinuousOn J (Icc (a : ℝ) b) :=
    ((by fun_prop : ContinuousOn R _).mul (by fun_prop : ContinuousOn (fun t => (P t) ^ 2) _)).div
      hLc.neg.continuousOn (fun t ht => (neg_pos.2 (hL t ht)).ne')
  have hFc : ContinuousOn F (Icc (a : ℝ) b) :=
    hEc.continuousOn.sub (hLc.neg.continuousOn.log (fun t ht => (neg_pos.2 (hL t ht)).ne'))
  have hJi : IntervalIntegrable J volume a b := hJc.intervalIntegrable_of_Icc hab
  have hJnonneg (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) : 0 ≤ J t := by
    have hr := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
      u (projIcc 0 V hV t)).2.1.le
    exact div_nonneg (mul_nonneg hr (sq_nonneg _)) (neg_pos.2 (hL t ht)).le
  have hJ0 : 0 ≤ ∫ t in (a : ℝ)..b, J t :=
    intervalIntegral.integral_nonneg hab hJnonneg
  have hd (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) : HasDerivAt F (-J t) t := by
    have htV := hsub (Ioo_subset_Icc_self ht)
    have hE := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      t (hx.longitudinal_derivative u htV)
    have hvel := hx.outgoing_radial_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp hf u htV
    have hn : -L t ≠ 0 := (neg_pos.2 (hL t (Ioo_subset_Icc_self ht))).ne'
    have hh := hE.sub (hvel.neg.log hn)
    have hh' : HasDerivWithinAt F (-J t) (Icc 0 V) t := by
      apply hh.congr_deriv
      simp only [Pi.neg_apply, ContinuousLinearMap.proj_apply, J, R, P, L,
        intervalExtension_apply, projIcc_of_mem hV htV] at hn ⊢
      field_simp [neg_ne_zero.mp hn]
      ring
    exact hh'.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (a : ℝ) ≤ b from hab)
    hFc hd hJi.neg
  rw [intervalIntegral.integral_neg] at hftc
  simp only [F, E, L, intervalExtension_apply, projIcc_of_mem hV a.property,
    projIcc_of_mem hV b.property] at hftc
  have hlb := (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha).1
  have hlog : x.1 u b 2 - Real.log (-x.2.1 u b 0) =
      (x.1 u a 2 - Real.log (-x.2.1 u a 0)) - ∫ t in (a : ℝ)..b, J t := by
    linarith only [hftc]
  have hexp := congrArg Real.exp hlog
  simp only [Real.exp_sub, Real.exp_log (neg_pos.2 ha), Real.exp_log (neg_pos.2 hlb)] at hexp
  have hq : Real.exp (x.1 u b 2) / (4 * (-x.2.1 u b 0)) =
      Real.exp (x.1 u a 2) / (4 * (-x.2.1 u a 0)) * Real.exp (-(∫ t in (a : ℝ)..b, J t)) := by
    rw [Real.exp_neg]
    calc
      _ = (Real.exp (x.1 u b 2) / (-x.2.1 u b 0)) / 4 := by ring
      _ = _ := by rw [hexp]; ring
  refine ⟨hJi, hJ0, hq, div_pos (Real.exp_pos _) (mul_pos (by norm_num) (neg_pos.2 hlb)), ?_, ?_⟩
  · change Real.exp (x.1 u b 2) / (4 * (-x.2.1 u b 0)) ≤
      Real.exp (x.1 u a 2) / (4 * (-x.2.1 u a 0))
    rw [hq]
    exact mul_le_of_le_one_right (div_nonneg (Real.exp_pos _).le (by linarith only [ha]))
      (Real.exp_le_one_iff.2 (neg_nonpos.2 hJ0))
  · have hl : Real.log (-x.2.1 u b 0) = Real.log (-x.2.1 u a 0) +
        (x.1 u b 2 - x.1 u a 2 + ∫ t in (a : ℝ)..b, J t) := by linarith only [hftc]
    have hh := congrArg Real.exp hl
    simpa only [Real.exp_add, Real.exp_log (neg_pos.2 ha), Real.exp_log (neg_pos.2 hlb)] using hh

end CauchyHorizon
