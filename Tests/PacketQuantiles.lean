import CauchyHorizon.Characteristic.PacketQuantiles

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon.Tests

-- The inverse is an actual inverse of the integral-defined packet distribution.
example {ψ : ℝ → ℝ} (hi : Integrable (fun x => ψ x ^ 2))
    (hM : 0 < ∫ x, ψ x ^ 2) {R : ℝ} (hb : ∀ x, |ψ x| ≤ R)
    (hp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) :
    ∃ Q : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
      ∀ q, packetCumulative ψ (Q.symm q) = (q : ℝ) := by
  obtain ⟨Q, hQ⟩ := exists_packetCumulative_orderIso hi hM hb hp hs
  refine ⟨Q, fun q => ?_⟩
  rw [← hQ, Q.apply_symm_apply]

-- The cumulative function has a unique point at each interior fraction.
example {ψ : ℝ → ℝ} (hi : Integrable (fun x => ψ x ^ 2))
    (hM : 0 < ∫ x, ψ x ^ 2) (hp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (he : packetCumulative ψ x = packetCumulative ψ y) : x = y :=
  (packetCumulative_strictMonoOn hi hM hp).injOn hx hy he

-- The median uses half the actual terminal excess, and its width-normalized error tends to zero.
example {K : Type*} [TopologicalSpace K] {ψ : ℝ → ℝ} {a T : ℝ} {t L : ℕ → ℝ}
    {M : ℕ → ℝ → C(K, ℝ)} {Mh : ℕ → C(K, ℝ)} (hL : ∀ n, 0 < L n)
    (hq : HasMassQuantileAsymptotics ψ a t L M Mh T) :
    ∃ Q : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
      (∀ x, (Q x : ℝ) = packetCumulative ψ x) ∧ ∀ u,
      Tendsto (fun n =>
        (firstCrossing (fun v => (M n v - M 0 v) u) T ((1 / 2 : ℝ) * (Mh n - Mh 0) u) -
          (t n + L n * (Q.symm ⟨1 / 2, by constructor <;> norm_num⟩ : ℝ)) / a) / L n)
        atTop (𝓝 0) := by
  obtain ⟨Q, hQ, hquant⟩ := hq
  refine ⟨Q, hQ, fun u => Metric.tendsto_nhds.2 (fun ε hε => ?_)⟩
  filter_upwards [hquant (1 / 4) (3 / 4) (by norm_num) (by norm_num) ε hε] with n hn
  have hh := hn u ⟨1 / 2, by constructor <;> norm_num⟩ (by norm_num) (by norm_num)
  simpa only [Real.dist_eq, sub_zero, abs_div, abs_of_pos (hL n)] using
    (div_lt_iff₀ (hL n)).2 hh

-- One eventual index controls every ray and every fraction in a fixed compact interval.
example {K : Type*} [TopologicalSpace K] {ψ : ℝ → ℝ} {a T : ℝ} {t L : ℕ → ℝ}
    {M : ℕ → ℝ → C(K, ℝ)} {Mh : ℕ → C(K, ℝ)}
    (hq : HasMassQuantileAsymptotics ψ a t L M Mh T) :
    ∃ Q : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
      ∀ d > (0 : ℝ), ∀ᶠ n in atTop, ∀ u, ∀ q : Icc (0 : ℝ) 1,
        1 / 4 ≤ (q : ℝ) → (q : ℝ) ≤ 3 / 4 →
        |firstCrossing (fun v => (M n v - M 0 v) u) T (q * (Mh n - Mh 0) u) -
          (t n + L n * (Q.symm q : ℝ)) / a| < d * L n := by
  obtain ⟨Q, _hQ, hh⟩ := hq
  exact ⟨Q, hh (1 / 4) (3 / 4) (by norm_num) (by norm_num)⟩

-- The duration between the lower and upper quartiles has the corresponding inverse-CDF width.
example {K : Type*} [TopologicalSpace K] {ψ : ℝ → ℝ} {a T : ℝ} {t L : ℕ → ℝ}
    {M : ℕ → ℝ → C(K, ℝ)} {Mh : ℕ → C(K, ℝ)}
    (hq : HasMassQuantileAsymptotics ψ a t L M Mh T) :
    ∃ Q : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
      ∀ d > (0 : ℝ), ∀ᶠ n in atTop, ∀ u,
        let v := fun q : ℝ => firstCrossing (fun v => (M n v - M 0 v) u) T
          (q * (Mh n - Mh 0) u)
        |v (3 / 4) - v (1 / 4) - L n *
          ((Q.symm ⟨3 / 4, by constructor <;> norm_num⟩ : ℝ) -
            (Q.symm ⟨1 / 4, by constructor <;> norm_num⟩ : ℝ)) / a| < d * L n := by
  obtain ⟨Q, _hQ, hh⟩ := hq
  refine ⟨Q, fun d hd => ?_⟩
  filter_upwards [hh (1 / 4) (3 / 4) (by norm_num) (by norm_num) (d / 2) (half_pos hd)]
    with n hn
  intro u
  have h1 := hn u ⟨1 / 4, by constructor <;> norm_num⟩ le_rfl (by norm_num)
  have h3 := hn u ⟨3 / 4, by constructor <;> norm_num⟩ (by norm_num) le_rfl
  obtain ⟨h1l, h1r⟩ := abs_lt.1 h1
  obtain ⟨h3l, h3r⟩ := abs_lt.1 h3
  dsimp only
  simp only [mul_sub, sub_div, add_div] at *
  exact abs_lt.2 ⟨by linarith, by linarith⟩

end CauchyHorizon.Tests
