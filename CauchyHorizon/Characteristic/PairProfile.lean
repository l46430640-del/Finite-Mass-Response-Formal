import CauchyHorizon.Analysis.PacketPair
import CauchyHorizon.Characteristic.MassProfile
import Mathlib.Topology.Order.Compact

/-! Normalized two-packet response, with the same component-energy normalization at the horizon. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

def PairMassProfileLimit {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (M : ℕ → ℝ → C(K, ℝ)) (Γ : C(K, ℝ)) (a E : ℝ) (t L : ℕ → ℝ)
    (ψ : ℝ → ℝ) (δ σ : ℝ) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧ ∃ Mh : ℕ → C(K, ℝ),
    (∀ n, Tendsto (M n) atTop (𝓝 (Mh n))) ∧
    ∀ d > (0 : ℝ), ∀ᶠ n in atTop,
      (∀ v, T ≤ v → ∀ u, |(M n v - M 0 v) u / (2 * E * Γ u) -
        packetPairCumulative ψ δ σ ((a * v - t n) / L n)| < d) ∧
      ∀ u, |(Mh n - Mh 0) u / (2 * E * Γ u) - packetPairTotal ψ δ σ| < d

theorem MassProfileLimit.pair_normalized {K : Type*}
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {M : ℕ → ℝ → C(K, ℝ)} {Γ : C(K, ℝ)} {a E δ σ : ℝ} {t L : ℕ → ℝ}
    {ψ : ℝ → ℝ} {P : ℕ → ℝ → ℝ}
    (hprofile : MassProfileLimit M Γ a (fun _ => 0) P)
    (hE : 0 < E) (hL : ∀ n, 0 < L n) (hM : 0 < ∫ z, ψ z ^ 2)
    (hΓ : ∀ u, 0 < Γ u)
    (hP : ∀ n, n ≠ 0 → ∀ x, P n x = Real.sqrt (E / ((∫ z, ψ z ^ 2) * L n)) *
      (ψ ((x - t n) / L n) + σ * ψ ((x - t n) / L n - δ))) :
    PairMassProfileLimit M Γ a E t L ψ δ σ := by
  obtain ⟨T, hT, Mh, hMh, herr⟩ := hprofile
  obtain ⟨u₀, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (show (univ : Set K).Nonempty from ⟨Classical.arbitrary K, mem_univ _⟩)
    Γ.continuous.continuousOn
  let C := 2 * E * Γ u₀
  have hC : 0 < C := mul_pos (mul_pos (by norm_num) hE) (hΓ u₀)
  refine ⟨T, hT, Mh, hMh, fun d hd => ?_⟩
  have hquot (D : C(K, ℝ)) (s : ℝ) (he : ‖D - (2 * E * s) • Γ‖ < d * C) (u : K) :
      |D u / (2 * E * Γ u) - s| < d := by
    have hden : 0 < 2 * E * Γ u := mul_pos (mul_pos (by norm_num) hE) (hΓ u)
    have hminu : Γ u₀ ≤ Γ u := hmin (mem_univ u)
    have hdc : C ≤ 2 * E * Γ u := mul_le_mul_of_nonneg_left hminu (by positivity)
    have hh : |D u - (2 * E * s) * Γ u| < d * C := by
      simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
        Real.norm_eq_abs] using (ContinuousMap.norm_coe_le_norm (D - (2 * E * s) • Γ) u).trans_lt he
    rw [show D u / (2 * E * Γ u) - s =
      (D u - (2 * E * s) * Γ u) / (2 * E * Γ u) by
        field_simp [ne_of_gt hE, ne_of_gt (hΓ u)],
      abs_div, abs_of_pos hden]
    exact (div_lt_iff₀ hden).2 (hh.trans_le (mul_le_mul_of_nonneg_left hdc hd.le))
  filter_upwards [herr (d * C) (mul_pos hd hC), eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hint (v : ℝ) : (∫ x in Iic (a * v), P n x ^ 2) =
      2 * E * packetPairCumulative ψ δ σ ((a * v - t n) / L n) := by
    simp_rw [hP n hn0.ne']
    exact (packet_pair_integrals hE.le (hL n) ψ hM (t n) δ σ (a * v)).1
  have hterminal : (∫ x, P n x ^ 2) = 2 * E * packetPairTotal ψ δ σ := by
    simp_rw [hP n hn0.ne']
    exact (packet_pair_integrals hE.le (hL n) ψ hM (t n) δ σ 0).2
  constructor
  · intro v hv
    exact hquot _ _ (by simpa only [add_zero, hint] using hn.1 v hv)
  · exact hquot _ _ (by simpa only [hterminal] using hn.2)

end CauchyHorizon
