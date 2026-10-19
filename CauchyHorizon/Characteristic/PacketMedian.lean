import CauchyHorizon.Characteristic.PacketQuantiles

/-! Reflection symmetry identifies the actual first half-response time. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

theorem HasMassQuantileAsymptotics.symmetric_median
    {K : Type*} [TopologicalSpace K] {ψ : ℝ → ℝ} {a T : ℝ} {t L : ℕ → ℝ}
    {M : ℕ → ℝ → C(K, ℝ)} {Mh : ℕ → C(K, ℝ)}
    (hq : HasMassQuantileAsymptotics ψ a t L M Mh T)
    (hi : Integrable (fun x => ψ x ^ 2)) (hM : 0 < ∫ x, ψ x ^ 2)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) (hsym : ∀ x, ψ (1 - x) = ψ x) :
    packetCumulative ψ (1 / 2) = 1 / 2 ∧
      ∀ d > (0 : ℝ), ∀ᶠ n in atTop, ∀ u,
        |firstCrossing (fun v => (M n v - M 0 v) u) T ((1 / 2 : ℝ) * (Mh n - Mh 0) u) -
          (t n + L n / 2) / a| < d * L n := by
  have hr : (∫ x in (0 : ℝ)..1 / 2, ψ x ^ 2) = ∫ x in (1 / 2 : ℝ)..1, ψ x ^ 2 := by
    have he := intervalIntegral.integral_comp_sub_left (fun x => ψ x ^ 2)
      (a := (0 : ℝ)) (b := 1 / 2) 1
    norm_num only [hsym, sub_zero, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at he
    exact he
  obtain ⟨h0, h1⟩ := packetCumulative_endpoints hM hs
  have he : packetCumulative ψ (1 / 2) - packetCumulative ψ 0 =
      packetCumulative ψ 1 - packetCumulative ψ (1 / 2) := by
    simp only [packetCumulative, ← sub_div,
      intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn, hr]
  have hm : packetCumulative ψ (1 / 2) = 1 / 2 := by rw [h0, h1] at he; linarith only [he]
  obtain ⟨Q, hQ, hquant⟩ := hq
  let mid : Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
  have hmid : Q mid = mid := Subtype.ext ((hQ mid).trans hm)
  have hinv : (Q.symm mid : ℝ) = 1 / 2 := by rw [← hmid, Q.symm_apply_apply]
  refine ⟨hm, fun d hd => ?_⟩
  filter_upwards [hquant (1 / 4) (3 / 4) (by norm_num) (by norm_num) d hd] with n hn
  intro u
  have hh := hn u mid (by norm_num [mid]) (by norm_num [mid])
  simpa only [hinv, mid, mul_one_div] using hh

end CauchyHorizon
