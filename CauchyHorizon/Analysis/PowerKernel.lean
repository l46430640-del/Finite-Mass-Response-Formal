import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! The normalized late-region kernel, including its sharp Holder power. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem power_kernel_integral {z u σ s : ℝ} (hz : 0 < z) (hzu : z ≤ u) (hs : s < σ) :
    (∫ t in z..u, z ^ σ * t ^ (s - σ - 1)) ≤ z ^ s / (σ - s) := by
  have hu := hz.trans_le hzu
  have hzero : (0 : ℝ) ∉ uIcc z u := by rw [uIcc_of_le hzu]; simp only [mem_Icc, not_and]; intro h; linarith
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by linarith only [hs], hzero⟩)]
  have he : z ^ σ * ((u ^ (s - σ - 1 + 1) - z ^ (s - σ - 1 + 1)) / (s - σ - 1 + 1)) =
      (z ^ s - z ^ σ * u ^ (s - σ)) / (σ - s) := by
    rw [sub_add_cancel]
    have hp : z ^ σ * z ^ (s - σ) = z ^ s := by rw [← Real.rpow_add hz]; congr 1; ring
    rw [← hp]
    field_simp [sub_ne_zero.2 hs.ne, sub_ne_zero.2 hs.ne']
    ring
  rw [he]
  exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (sub_pos.2 hs).le

theorem power_kernel_holder {U z u σ p q : ℝ} {f : ℝ → ℝ}
    (hz : 0 < z) (hzu : z ≤ u) (huU : u ≤ U) (hpq : p.HolderConjugate q)
    (hσ : 1 / q < σ) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Icc 0 U))) :
    (∫ t in z..u, (z ^ σ * t ^ (-σ)) * |f t|) ≤
      (eLpNorm f (ENNReal.ofReal p) (volume.restrict (Icc 0 U))).toReal *
        z ^ (1 / q) / (σ * q - 1) ^ (1 / q) := by
  have hσ0 : 0 < σ := hpq.symm.one_div_pos.trans hσ
  have hσq : 1 < σ * q := (div_lt_iff₀ hpq.symm.pos).1 hσ
  have hsub : Icc z u ⊆ Icc 0 U := Icc_subset_Icc hz.le huU
  let μ := volume.restrict (Icc z u)
  let w := fun t : ℝ => z ^ σ * t ^ (-σ)
  have hwtop : MemLp w ∞ μ := by
    apply memLp_top_of_bound (by dsimp only [w, μ]; fun_prop) 1
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 := hz.trans_le ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [w]; positivity)]
    calc
      _ ≤ z ^ σ * z ^ (-σ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hz ht.1 (neg_nonpos.2 hσ0.le)) (Real.rpow_nonneg hz.le _)
      _ = 1 := by rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  have hwp : MemLp w (ENNReal.ofReal q) μ := hwtop.mono_exponent le_top
  have hfp := hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hhold := integral_mul_norm_le_Lp_mul_Lq hpq hfp hwp
  have hwnorm : (∫ t, ‖w t‖ ^ q ∂μ) ≤ z / (σ * q - 1) := by
    have he : (∫ t, ‖w t‖ ^ q ∂μ) = ∫ t in z..u, z ^ (σ * q) * t ^ (1 - σ * q - 1) := by
      rw [intervalIntegral.integral_of_le hzu, ← integral_Icc_eq_integral_Ioc]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have ht0 := hz.trans_le ht.1
      dsimp only [w]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hz.le, ← Real.rpow_mul ht0.le]
      congr 2
      ring
    rw [he]
    simpa only [Real.rpow_one] using power_kernel_integral hz hzu hσq
  have hfnorm : (∫ t, ‖f t‖ ^ p ∂μ) ^ (1 / p) = (eLpNorm f (ENNReal.ofReal p) μ).toReal := by
    rw [toReal_eLpNorm hfp.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (ne_of_gt (ENNReal.ofReal_pos.2 hpq.pos))
        ENNReal.ofReal_ne_top hfp.aestronglyMeasurable]
    simp only [μ, ENNReal.toReal_ofReal hpq.nonneg, one_div]
  have hleft : (∫ t, ‖f t‖ * ‖w t‖ ∂μ) = ∫ t in z..u, w t * |f t| := by
    rw [intervalIntegral.integral_of_le hzu, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 := hz.trans_le ht.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ w t by dsimp only [w]; positivity)]
    ring
  rw [hleft, hfnorm] at hhold
  have hnorm := ENNReal.toReal_mono hf.2.ne (eLpNorm_mono_measure f (Measure.restrict_mono hsub le_rfl))
  have hpw := Real.rpow_le_rpow (integral_nonneg (fun t => Real.rpow_nonneg (norm_nonneg _) _))
    hwnorm hpq.symm.one_div_nonneg
  apply (hhold.trans (mul_le_mul hnorm hpw (by positivity) ENNReal.toReal_nonneg)).trans_eq
  rw [Real.div_rpow hz.le (sub_pos.2 hσq).le]
  ring

end CauchyHorizon
