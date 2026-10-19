import CauchyHorizon.Analysis.IntervalOperators

/-! A pointwise affine majorant controls the actual Bochner L2 norm. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem l2_norm_le_affine_majorant {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U C : ℝ} (hU : 0 ≤ U) (hC : 0 ≤ C)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp F 2 (volume.restrict (Icc 0 U)))
    (hb : ∀ᵐ t ∂volume.restrict (Icc 0 U), ‖f t‖ ≤ C * (‖g t‖ + 1)) :
    ‖f‖ ≤ C * (‖g‖ + Real.sqrt U) := by
  let G := (Lp.memLp g).norm.toLp (fun t => ‖g t‖)
  let one := intervalToLp hU 2 (ContinuousMap.const _ (1 : ℝ))
  have hG : ‖G‖ = ‖g‖ := by rw [Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]
  have hone : ‖one‖ ≤ Real.sqrt U := by
    have hh := intervalToL2_norm_le hU (ContinuousMap.const (Icc 0 U) (1 : ℝ))
    have hc : ‖ContinuousMap.const (Icc 0 U) (1 : ℝ)‖ ≤ 1 :=
      (ContinuousMap.norm_le _ zero_le_one).2 (fun _ => by norm_num)
    rw [sub_zero] at hh
    exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg U))
  have hm : ‖f‖ ≤ ‖C • (G + one)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hb, Lp.coeFn_smul C (G + one), Lp.coeFn_add G one,
      (Lp.memLp g).norm.coeFn_toLp, intervalToLp_ae hU 2 (ContinuousMap.const _ (1 : ℝ))]
      with t ht hs ha hg ho
    change G t = ‖g t‖ at hg
    change one t = 1 at ho
    rw [hs, Pi.smul_apply, ha, Pi.add_apply, hg, ho, smul_eq_mul,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (by positivity))]
    exact ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left ((norm_add_le G one).trans (by rw [hG]; exact add_le_add_right hone _)) hC)

end CauchyHorizon
