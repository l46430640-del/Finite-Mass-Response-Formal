import CauchyHorizon.Analysis.NormalizedPacket
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! The concrete unit-height packet used in the analytic profiles. -/

open MeasureTheory Set
open scoped ContDiff

namespace CauchyHorizon

noncomputable def unitPacketBump (y : ℝ) : ℝ :=
  Real.exp 4 * expNegInvGlue (y * (1 - y))

theorem unitPacketBump_eq (y : ℝ) :
    unitPacketBump y = if y ∈ Ioo (0 : ℝ) 1 then
      Real.exp (4 - 1 / (y * (1 - y))) else 0 := by
  by_cases hy : y ∈ Ioo (0 : ℝ) 1
  · have hp : 0 < y * (1 - y) := mul_pos hy.1 (sub_pos.mpr hy.2)
    rw [unitPacketBump, expNegInvGlue, if_pos hy, if_neg hp.not_ge]
    simp only [sub_eq_add_neg, one_div, Real.exp_add]
  · have hn : y * (1 - y) ≤ 0 := by
      by_cases h0 : 0 < y
      · have h1 : 1 ≤ y := le_of_not_gt (fun h1 => hy ⟨h0, h1⟩)
        exact mul_nonpos_of_nonneg_of_nonpos h0.le (sub_nonpos.mpr h1)
      · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h0) (by linarith)
    simp [unitPacketBump, expNegInvGlue.zero_of_nonpos hn, hy]

theorem unitPacketBump_properties :
    ContDiff ℝ ∞ unitPacketBump ∧ HasCompactSupport unitPacketBump ∧
      (∀ y ∈ Ioo (0 : ℝ) 1, 0 < unitPacketBump y) ∧
      (∀ y, y ∉ Ioo (0 : ℝ) 1 → unitPacketBump y = 0) ∧
      Integrable (fun y => unitPacketBump y ^ 2) ∧
      0 < ∫ y, unitPacketBump y ^ 2 := by
  have hc : ContDiff ℝ ∞ unitPacketBump :=
    contDiff_const.mul (expNegInvGlue.contDiff.comp (contDiff_id.mul (contDiff_const.sub contDiff_id)))
  have hp (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : 0 < unitPacketBump y := by
    rw [unitPacketBump_eq, if_pos hy]
    exact Real.exp_pos _
  have hs (y : ℝ) (hy : y ∉ Ioo (0 : ℝ) 1) : unitPacketBump y = 0 := by
    rw [unitPacketBump_eq, if_neg hy]
  have hk : HasCompactSupport unitPacketBump :=
    HasCompactSupport.intro isCompact_Icc (fun y hy =>
      hs y (fun h => hy ⟨h.1.le, h.2.le⟩))
  have hsq : HasCompactSupport (fun y => unitPacketBump y ^ 2) :=
    hk.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact ⟨hc, hk, hp, hs, (hc.continuous.pow 2).integrable_of_hasCompactSupport hsq,
    (hc.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero hsq
      (fun y => sq_nonneg _) (pow_ne_zero 2 (hp (1 / 2) (by constructor <;> norm_num)).ne')⟩

end CauchyHorizon
