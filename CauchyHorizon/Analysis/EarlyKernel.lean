import CauchyHorizon.Analysis.IntegratingFactor
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-! A finite-endpoint identity reduces the early double kernel without Fubini. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem exponential_double_kernel_bound {k q l v : ℝ} (hsum : 0 < k + q) (hlv : l ≤ v)
    {M : ℝ → ℝ} (hc : Continuous M) (hM : ∀ t ∈ Icc l v, 0 ≤ M t) :
    let R := fun t => ∫ w in t..v, Real.exp (-(q) * (w - t)) * M w
    ContinuousOn R (Icc l v) ∧
      ((k + q)) * (∫ t in l..v, Real.exp (-k * (v - t)) * R t) =
        (∫ t in l..v, Real.exp (-k * (v - t)) * M t) - Real.exp (-k * (v - l)) * R l ∧
      (∫ t in l..v, Real.exp (-k * (v - t)) * R t) ≤
        (1 / ((k + q))) * ∫ t in l..v, Real.exp (-k * (v - t)) * M t := by
  let R := fun t => ∫ w in t..v, Real.exp (-(q) * (w - t)) * M w
  let g := fun t => Real.exp (-(q) * t) * M t
  let P := fun t => ∫ w in l..t, g w
  let Q := fun t => Real.exp ((q) * t) * (P v - P t)
  have hgc : Continuous g := by fun_prop
  have hPc : ContinuousOn P (Icc l v) := by
    simpa only [uIcc_of_le hlv] using intervalIntegral.continuousOn_primitive_interval'
      (hgc.intervalIntegrable (μ := volume) l v) left_mem_uIcc
  have hQc : ContinuousOn Q (Icc l v) := by dsimp only [Q]; fun_prop
  have hRQ : R = Q := by
    funext t
    have hp : P v - P t = ∫ w in t..v, g w := by
      have hh := intervalIntegral.integral_add_adjacent_intervals
        (hgc.intervalIntegrable (μ := volume) l t) (hgc.intervalIntegrable t v)
      change P t + (∫ w in t..v, g w) = P v at hh
      linarith only [hh]
    dsimp only [R, Q]
    rw [hp, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro w _
    dsimp only [g]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hQd (t : ℝ) (ht : t ∈ Ioo l v) : HasDerivAt Q (q * Q t - M t) t := by
    have hp := primitive_hasDerivAt_interior (hgc.intervalIntegrable (μ := volume) l v)
      hgc.continuousOn ht
    have he := ((hasDerivAt_id t).const_mul (q)).exp
    have hex : Real.exp ((q) * t) * Real.exp (-(q) * t) = 1 := by
      rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
    apply (he.mul (hp.const_sub (P v))).congr_deriv
    dsimp only [Q, g, id_eq]
    nlinarith only [congrArg (fun a => a * M t) hex]
  let F := fun t => Real.exp (-k * (v - t)) * Q t
  let m := fun t => Real.exp (-k * (v - t)) * M t
  have hFc : ContinuousOn F (Icc l v) := by dsimp only [F]; fun_prop
  have hmc : Continuous m := by fun_prop
  have hFd (t : ℝ) (ht : t ∈ Ioo l v) : HasDerivAt F ((k + q) * F t - m t) t := by
    have he := (((hasDerivAt_id t).const_sub v).const_mul (-k)).exp
    apply (he.mul (hQd t ht)).congr_deriv
    dsimp only [F, m, id_eq]
    ring
  have hFi : IntervalIntegrable F volume l v := hFc.intervalIntegrable_of_Icc hlv
  have hmi := hmc.intervalIntegrable (μ := volume) l v
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlv hFc hFd
    ((hFi.const_mul ((k + q))).sub hmi)
  have hFv : F v = 0 := by simp [F, Q]
  rw [intervalIntegral.integral_sub (hFi.const_mul ((k + q))) hmi,
    intervalIntegral.integral_const_mul, hFv, zero_sub] at hi
  have he : ((k + q)) * (∫ t in l..v, F t) = (∫ t in l..v, m t) - F l := by
    linarith only [hi]
  have hFl : 0 ≤ F l := by
    change 0 ≤ Real.exp (-k * (v - l)) * Q l
    rw [← hRQ]
    exact mul_nonneg (Real.exp_pos _).le (intervalIntegral.integral_nonneg hlv
      (fun w hw => mul_nonneg (Real.exp_pos _).le (hM w hw)))
  change ContinuousOn R (Icc l v) ∧
    ((k + q)) * (∫ t in l..v, Real.exp (-k * (v - t)) * R t) =
      (∫ t in l..v, Real.exp (-k * (v - t)) * M t) - Real.exp (-k * (v - l)) * R l ∧
    (∫ t in l..v, Real.exp (-k * (v - t)) * R t) ≤
      (1 / ((k + q))) * ∫ t in l..v, Real.exp (-k * (v - t)) * M t
  rw [hRQ]
  refine ⟨hQc, he, ?_⟩
  have hden : 0 < (k + q) := hsum
  have hb : (∫ t in l..v, F t) ≤ (∫ t in l..v, m t) / ((k + q)) := by
    apply (le_div_iff₀ hden).2
    nlinarith only [he, hFl]
  exact hb.trans_eq (by ring)

theorem early_double_kernel_bound {k l v : ℝ} (hk : 0 < k) (hlv : l ≤ v)
    {M : ℝ → ℝ} (hc : Continuous M) (hM : ∀ t ∈ Icc l v, 0 ≤ M t) :
    let R := fun t => ∫ w in t..v, Real.exp (-(3 * k) * (w - t)) * M w
    ContinuousOn R (Icc l v) ∧
      (4 * k) * (∫ t in l..v, Real.exp (-k * (v - t)) * R t) =
        (∫ t in l..v, Real.exp (-k * (v - t)) * M t) - Real.exp (-k * (v - l)) * R l ∧
      (∫ t in l..v, Real.exp (-k * (v - t)) * R t) ≤
        (1 / (4 * k)) * ∫ t in l..v, Real.exp (-k * (v - t)) * M t := by
  have hh := exponential_double_kernel_bound (k := k) (q := 3 * k)
    (by linarith only [hk]) hlv hc hM
  dsimp only at hh ⊢
  rwa [show k + 3 * k = 4 * k by ring] at hh

end CauchyHorizon
