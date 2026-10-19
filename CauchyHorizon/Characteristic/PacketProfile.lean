import CauchyHorizon.Analysis.PacketCumulative
import CauchyHorizon.Characteristic.MassProfile

/-! The normalized mass curve, uniformly over all late finite endpoints. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

theorem MassProfileLimit.packet_cumulative {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {M : ℕ → ℝ → C(K, ℝ)} {Γ : C(K, ℝ)} {a ℓ E R : ℝ}
    {P : ℕ → ℝ → ℝ} {ψ : ℝ → ℝ} {t L : ℕ → ℝ}
    (hprofile : MassProfileLimit M Γ a (fun _ => ℓ) P)
    (hE : 0 ≤ E) (hi : Integrable (fun x => ψ x ^ 2)) (hM : 0 < ∫ x, ψ x ^ 2)
    (hb : ∀ x, |ψ x| ≤ R)
    (hL : ∀ n, 0 < L n) (hLtop : Tendsto L atTop atTop)
    (hP : ∀ n, n ≠ 0 → ∀ x, P n x =
      Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) * ψ ((x - t n) / L n)) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ d > (0 : ℝ), ∀ᶠ n in atTop, ∀ v, T ≤ v →
      ‖M n v - M 0 v - packetCumulative ψ ((a * v - t n) / L n) • (E • Γ)‖ < d := by
  obtain ⟨T, hT, Z, _hZ, herr⟩ := hprofile
  let C := |E| * (R ^ 2 / (∫ x, ψ x ^ 2)) * |ℓ| * ‖Γ‖
  have hlim : Tendsto (fun n => C / L n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hLtop).const_mul C
  have hphase (n : ℕ) (hn : n ≠ 0) (v : ℝ) :
      ‖(∫ x in Iic (a * v + ℓ), P n x ^ 2) • Γ -
        packetCumulative ψ ((a * v - t n) / L n) • (E • Γ)‖ ≤ C / L n := by
    have hc : (∫ x in Iic (a * v + ℓ), P n x ^ 2) =
        E * packetCumulative ψ ((a * v + ℓ - t n) / L n) := by
      simp_rw [hP n hn]
      exact packet_cumulative_integral hE (hL n) ψ hM (t n) (a * v + ℓ)
    have hh := packetCumulative_sub_le hi hM hb
      ((a * v - t n) / L n) ((a * v + ℓ - t n) / L n)
    rw [show (a * v + ℓ - t n) / L n - (a * v - t n) / L n = ℓ / L n by ring,
      abs_div, abs_of_pos (hL n)] at hh
    rw [hc, smul_smul, mul_comm (packetCumulative ψ ((a * v - t n) / L n)) E,
      ← sub_smul, ← mul_sub, norm_smul, Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |E| * ((R ^ 2 / (∫ x, ψ x ^ 2)) * (|ℓ| / L n)) * ‖Γ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (abs_nonneg E)) (norm_nonneg Γ)
      _ = C / L n := by dsimp only [C]; ring
  refine ⟨T, hT, ?_⟩
  intro d hd
  filter_upwards [herr (d / 2) (half_pos hd), (tendsto_order.1 hlim).2 (d / 2) (half_pos hd),
    eventually_gt_atTop (0 : ℕ)] with n hn hsmall hnpos v hv
  calc
    _ = ‖(M n v - M 0 v - (∫ x in Iic (a * v + ℓ), P n x ^ 2) • Γ) +
        ((∫ x in Iic (a * v + ℓ), P n x ^ 2) • Γ -
          packetCumulative ψ ((a * v - t n) / L n) • (E • Γ))‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ < d / 2 + d / 2 := add_lt_add (hn.1 v hv) ((hphase n hnpos.ne' v).trans_lt hsmall)
    _ = d := add_halves d

end CauchyHorizon
