import CauchyHorizon.Analysis.PacketCumulative

/-! Exact density normalization and the exterior values of its cumulative profile. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem packet_density_integrals {ψ : ℝ → ℝ} (hM : 0 < ∫ z, ψ z ^ 2)
    {L : ℝ} (hL : 0 < L) (t y : ℝ) :
    (∫ x, ψ ((x - t) / L) ^ 2 / ((∫ z, ψ z ^ 2) * L)) = 1 ∧
      (∫ x in Iic y, ψ ((x - t) / L) ^ 2 / ((∫ z, ψ z ^ 2) * L)) =
        packetCumulative ψ ((y - t) / L) := by
  constructor
  · rw [integral_div, integral_sub_right_eq_self (fun x => ψ (x / L) ^ 2) t,
      Measure.integral_comp_div (fun x => ψ x ^ 2), smul_eq_mul, abs_of_pos hL]
    field_simp
  · rw [integral_div, integral_Iic_translate_dilate hL (fun x => ψ x ^ 2), packetCumulative]
    field_simp

theorem packetCumulative_exterior {ψ : ℝ → ℝ} (hM : 0 < ∫ z, ψ z ^ 2)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) (y : ℝ) :
    (y ≤ 0 → packetCumulative ψ y = 0) ∧
      (1 ≤ y → packetCumulative ψ y = 1) := by
  constructor
  · intro hy
    have hz : (∫ x in Iic y, ψ x ^ 2) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by
        rw [hs x (fun h => (not_lt_of_ge (hx.trans hy)) h.1), zero_pow (by decide)])
    simp only [packetCumulative, hz, zero_div]
  · intro hy
    have he : (∫ x in Iic y, ψ x ^ 2) = ∫ x, ψ x ^ 2 :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hs x (fun h => hx (h.2.le.trans hy)), zero_pow (by decide)])
    simp only [packetCumulative, he, div_self hM.ne']

end CauchyHorizon
