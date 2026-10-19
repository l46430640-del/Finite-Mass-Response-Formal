import CauchyHorizon.Characteristic.OutgoingConstraint
import CauchyHorizon.Analysis.DampedScalar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual outgoing velocity damping from the conformal and scalar bounds. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.lambda_damping {M e Λ U V q c H R : ℝ} {h r : ℝ → ℝ}
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
    (hq : 0 < q) (hc0 : 0 < c) (hH : 0 ≤ H) (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b)
    (hR : ∀ w ∈ Icc a b, x.1 u w 0 ≤ R)
    (hscalar : ∀ w ∈ Icc a b, |x.2.1 u w 1| ≤ H * Real.exp (-c * w))
    (hell : ∀ w ∈ Icc a b, x.2.1 u w 2 ≤ -q) :
    (∀ w ∈ Icc a b, |x.2.1 u w 0| ≤ Real.exp (-q * ((w : ℝ) - a)) *
      (|x.2.1 u a 0| + ∫ t in (a : ℝ)..w,
        Real.exp (q * (t - a)) * (R * H ^ 2 * Real.exp (-(2 * c) * t)))) ∧
    (∫ t in (a : ℝ)..b, |intervalExtension hV (x.2.1 u) t 0|) ≤
      (|x.2.1 u a 0| + (R * H ^ 2) / (2 * c) * Real.exp (-(2 * c) * a)) / q := by
  let L := fun t => intervalExtension hV (x.2.1 u) t 0
  let Q := fun t => -intervalExtension hV (x.2.1 u) t 2
  let F := fun t => -(intervalExtension hV (x.1 u) t 0 * (intervalExtension hV (x.2.1 u) t 1) ^ 2)
  let G := fun t : ℝ => R * H ^ 2 * Real.exp (-(2 * c) * t)
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hR0 : 0 ≤ R := (hg u a).2.1.le.trans (hR a (left_mem_Icc.2 hab))
  have hsub : Icc (a : ℝ) b ⊆ Icc 0 V :=
    fun _ ht => ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
  have hd (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) : HasDerivAt L (-Q t * L t + F t) t := by
    have htV := hsub (Ioo_subset_Icc_self ht)
    have hh := hx.outgoing_radial_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp hf u htV
    apply (hh.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1)
      (ht.2.trans_le b.property.2))).congr_deriv
    simp only [L, Q, F, intervalExtension_apply, projIcc_of_mem hV htV]
    ring
  have hcoef (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) : q ≤ Q t := by
    have hh := hell ⟨t, hsub ht⟩ ht
    simp only [Q, intervalExtension_apply, projIcc_of_mem hV (hsub ht)]
    linarith only [hh]
  have hforce (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) : |F t| ≤ G t := by
    let w : Icc 0 V := ⟨t, hsub ht⟩
    have hs : (x.2.1 u w 1) ^ 2 ≤ H ^ 2 * Real.exp (-(2 * c) * t) := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hH (Real.exp_pos _).le)).2 (hscalar w ht)
      rw [sq_abs, mul_pow, ← Real.exp_nat_mul] at hh
      simpa only [w, Nat.cast_ofNat, show (2 : ℝ) * (-c * t) = -(2 * c) * t by ring] using hh
    simp only [F, G, intervalExtension_apply, projIcc_of_mem hV (hsub ht)]
    rw [abs_neg, abs_mul, abs_of_pos (hg u w).2.1, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul (hR w ht) hs (sq_nonneg _) hR0).trans_eq (by ring)
  have hb := damped_scalar_bound (show (a : ℝ) ≤ b from hab) hq
    (show ContinuousOn L (Icc (a : ℝ) b) by fun_prop)
    (show ContinuousOn Q (Icc (a : ℝ) b) by fun_prop)
    (show ContinuousOn G (Icc (a : ℝ) b) by fun_prop) hd hcoef hforce
  have hGI : (∫ t in (a : ℝ)..b, G t) ≤ (R * H ^ 2) / (2 * c) * Real.exp (-(2 * c) * a) := by
    dsimp only [G]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.2 (mul_pos (by norm_num) hc0).ne'),
      integral_exp, smul_eq_mul]
    have hh := mul_nonneg (div_nonneg (mul_nonneg hR0 (sq_nonneg H))
      (by positivity : 0 ≤ 2 * c)) (Real.exp_pos (-(2 * c) * (b : ℝ))).le
    simp only [inv_neg, div_eq_mul_inv] at hh ⊢
    nlinarith only [hh]
  constructor
  · intro w hw
    simpa only [L, G, intervalExtension_apply, projIcc_of_mem hV a.property,
      projIcc_of_mem hV w.property] using hb.1 w hw
  · have hh := hb.2.trans (div_le_div_of_nonneg_right (add_le_add le_rfl hGI) hq.le)
    simpa only [L, intervalExtension_apply, projIcc_of_mem hV a.property] using hh

theorem IsWaveIntegral.lambda_damping_exp {M e Λ U V q c H R : ℝ} {h r : ℝ → ℝ}
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
    (hc0 : 0 < c) (hqc : 2 * c < q) (hH : 0 ≤ H) (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b)
    (hR : ∀ w ∈ Icc a b, x.1 u w 0 ≤ R)
    (hscalar : ∀ w ∈ Icc a b, |x.2.1 u w 1| ≤ H * Real.exp (-c * w))
    (hell : ∀ w ∈ Icc a b, x.2.1 u w 2 ≤ -q) :
    |x.2.1 u b 0| ≤ Real.exp (-q * ((b : ℝ) - a)) * |x.2.1 u a 0| +
      R * H ^ 2 / (q - 2 * c) * Real.exp (-(2 * c) * b) := by
  have hq : 0 < q := (by positivity : 0 < 2 * c).trans hqc
  have hgap : 0 < q - 2 * c := sub_pos.2 hqc
  have hR0 : 0 ≤ R := (hx.incoming_radius_pos hU hV hUR hp hf u a).le.trans (hR a ⟨le_rfl, hab⟩)
  have hb := (hx.lambda_damping hU hV hUR hc hi hrc hr0 hφ hrd hp hf hq hc0 hH u a b hab
    hR hscalar hell).1 b (right_mem_Icc.2 hab)
  rw [mul_add] at hb
  apply hb.trans (add_le_add le_rfl ?_)
  have hfun (t : ℝ) : Real.exp (q * (t - a)) * (R * H ^ 2 * Real.exp (-(2 * c) * t)) =
      (R * H ^ 2 * Real.exp (-q * a)) * Real.exp ((q - 2 * c) * t) := by
    have he : Real.exp (q * (t - a)) * Real.exp (-(2 * c) * t) =
        Real.exp (-q * a) * Real.exp ((q - 2 * c) * t) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc
      _ = (R * H ^ 2) * (Real.exp (q * (t - a)) * Real.exp (-(2 * c) * t)) := by ring
      _ = _ := by rw [he]; ring
  simp_rw [hfun]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ hgap.ne', integral_exp, smul_eq_mul]
  let K := (R * H ^ 2 / (q - 2 * c)) *
    (Real.exp (-q * ((b : ℝ) - a)) * Real.exp (-q * a))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have he : Real.exp (-q * ((b : ℝ) - a)) * Real.exp (-q * a) * Real.exp ((q - 2 * c) * b) =
      Real.exp (-(2 * c) * b) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc
    _ = K * (Real.exp ((q - 2 * c) * b) - Real.exp ((q - 2 * c) * a)) := by
      dsimp only [K]; ring
    _ ≤ K * Real.exp ((q - 2 * c) * b) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos _).le) hK
    _ = _ := by dsimp only [K]; rw [mul_assoc, he]

end CauchyHorizon
