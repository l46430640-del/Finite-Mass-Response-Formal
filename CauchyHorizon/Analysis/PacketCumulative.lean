import CauchyHorizon.Analysis.NormalizedPacket
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Exact cumulative packet energy and its uniform control under translations. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

noncomputable def packetCumulative (ψ : ℝ → ℝ) (y : ℝ) : ℝ :=
  (∫ x in Iic y, ψ x ^ 2) / (∫ x, ψ x ^ 2)

theorem integral_Iic_translate_dilate {L : ℝ} (hL : 0 < L)
    (f : ℝ → ℝ) (t z : ℝ) :
    (∫ x in Iic z, f ((x - t) / L)) = L * ∫ y in Iic ((z - t) / L), f y := by
  have he (x : ℝ) :
      (Iic z).indicator (fun x => f ((x - t) / L)) x =
        (Iic ((z - t) / L)).indicator f ((x - t) / L) := by
    have hx : (x - t) / L ≤ (z - t) / L ↔ x ≤ z := by
      rw [div_le_div_iff_of_pos_right hL, sub_le_sub_iff_right]
    simp only [indicator, mem_Iic, hx]
  rw [← integral_indicator measurableSet_Iic]
  simp_rw [he]
  rw [integral_sub_right_eq_self
      (fun x => (Iic ((z - t) / L)).indicator f (x / L)) t,
    Measure.integral_comp_div, abs_of_pos hL,
    smul_eq_mul, integral_indicator measurableSet_Iic]

theorem packet_cumulative_integral {E L : ℝ} (hE : 0 ≤ E) (hL : 0 < L)
    (ψ : ℝ → ℝ) (hM : 0 < ∫ x, ψ x ^ 2) (t z : ℝ) :
    (∫ x in Iic z, (Real.sqrt (E / ((∫ y, ψ y ^ 2) * L)) * ψ ((x - t) / L)) ^ 2) =
      E * packetCumulative ψ ((z - t) / L) := by
  simp_rw [mul_pow, Real.sq_sqrt (div_nonneg hE (mul_pos hM hL).le)]
  rw [integral_const_mul, integral_Iic_translate_dilate hL (fun y => ψ y ^ 2), packetCumulative]
  field_simp

theorem packetCumulative_sub_le {ψ : ℝ → ℝ} (hi : Integrable (fun x => ψ x ^ 2))
    (hM : 0 < ∫ x, ψ x ^ 2) {R : ℝ} (hb : ∀ x, |ψ x| ≤ R)
    (x y : ℝ) :
    |packetCumulative ψ y - packetCumulative ψ x| ≤
      (R ^ 2 / (∫ z, ψ z ^ 2)) * |y - x| := by
  have hh : ‖∫ z in x..y, ψ z ^ 2‖ ≤ R ^ 2 * |y - x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro z _hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_abs (ψ z)).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) (hb z) 2)
  rw [packetCumulative, packetCumulative, ← sub_div,
    intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn,
    abs_div, abs_of_pos hM]
  simpa only [Real.norm_eq_abs, mul_div_right_comm] using (div_le_div_of_nonneg_right hh hM.le)

end CauchyHorizon
