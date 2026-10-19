import CauchyHorizon.Characteristic.MassProfile

/-! Vanishing profile supremum removes a fixed phase uniformly over all endpoints. -/

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace CauchyHorizon

theorem MassProfileLimit.remove_constant_phase {K : Type*}
    [TopologicalSpace K] [CompactSpace K]
    {M : ℕ → ℝ → C(K, ℝ)} {Γ : C(K, ℝ)} {a ℓ : ℝ} {P : ℕ → ℝ →ᵇ ℝ}
    (hprofile : MassProfileLimit M Γ a (fun _ => ℓ) (fun n => P n))
    (hi : ∀ n, Integrable (fun x => P n x ^ 2))
    (hsmall : Tendsto (fun n => ‖P n‖) atTop (𝓝 0)) :
    MassProfileLimit M Γ a (fun _ => 0) (fun n => P n) := by
  obtain ⟨T, hT, Z, hZ, herr⟩ := hprofile
  have hlim : Tendsto (fun n => ‖P n‖ ^ 2 * |ℓ| * ‖Γ‖) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul] using
      ((hsmall.pow 2).mul_const |ℓ|).mul_const ‖Γ‖
  have hphase (n : ℕ) (v : ℝ) :
      ‖((∫ x in Iic (a * v + ℓ), P n x ^ 2) - ∫ x in Iic (a * v), P n x ^ 2) • Γ‖ ≤
        ‖P n‖ ^ 2 * |ℓ| * ‖Γ‖ := by
    rw [norm_smul, intervalIntegral.integral_Iic_sub_Iic
      (hi n).integrableOn (hi n).integrableOn]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg Γ)
    have hh : ‖∫ x in a * v..a * v + ℓ, P n x ^ 2‖ ≤
        ‖P n‖ ^ 2 * |a * v + ℓ - a * v| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x _hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb : |P n x| ≤ ‖P n‖ := by
        simpa only [Real.norm_eq_abs] using (P n).norm_coe_le_norm x
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    simpa only [add_sub_cancel_left] using hh
  refine ⟨T, hT, Z, hZ, fun d hd => ?_⟩
  filter_upwards [herr (d / 2) (half_pos hd),
    (tendsto_order.1 hlim).2 (d / 2) (half_pos hd)] with n hn hsn
  refine ⟨fun v hv => ?_, (hn.2).trans (half_lt_self hd)⟩
  simp only [add_zero]
  calc
    _ = ‖(M n v - M 0 v - (∫ x in Iic (a * v + ℓ), P n x ^ 2) • Γ) +
        (((∫ x in Iic (a * v + ℓ), P n x ^ 2) - ∫ x in Iic (a * v), P n x ^ 2) • Γ)‖ := by
      rw [sub_smul]
      congr 1
      abel
    _ ≤ _ := norm_add_le _ _
    _ < d / 2 + d / 2 := add_lt_add (hn.1 v hv) ((hphase n v).trans_lt hsn)
    _ = d := add_halves d

end CauchyHorizon
