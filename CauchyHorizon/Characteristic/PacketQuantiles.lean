import CauchyHorizon.Analysis.FirstCrossing
import CauchyHorizon.Analysis.PacketQuantile
import Mathlib.Topology.UniformSpace.HeineCantor

/-! First attainment of fractions of the actual terminal mass excess. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

def HasMassFirstCrossings {K : Type*} [TopologicalSpace K]
    (M : ℕ → ℝ → C(K, ℝ)) (Mh : ℕ → C(K, ℝ)) (T : ℝ) : Prop :=
  (∀ n, ContinuousOn (M n) (Ici T)) ∧
    ∀ q₀ > (0 : ℝ), ∀ᶠ n in atTop, ∀ u, 0 < (Mh n - Mh 0) u ∧
      ∀ q, q₀ ≤ q → q < 1 →
        IsLeast {v | T ≤ v ∧ (M n v - M 0 v) u = q * (Mh n - Mh 0) u}
          (firstCrossing (fun v => (M n v - M 0 v) u) T (q * (Mh n - Mh 0) u))

theorem mass_first_crossings {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {M : ℕ → ℝ → C(K, ℝ)} {Mh : ℕ → C(K, ℝ)} {A : C(K, ℝ)} {T : ℝ}
    (hc : ∀ n, ContinuousOn (M n) (Ici T))
    (hMh : ∀ n, Tendsto (M n) atTop (𝓝 (Mh n)))
    (hstart : Tendsto (fun n => M n T - M 0 T) atTop (𝓝 0))
    (hterminal : Tendsto (fun n => Mh n - Mh 0) atTop (𝓝 A)) (hA : ∀ u, 0 < A u) :
    HasMassFirstCrossings M Mh T := by
  refine ⟨hc, fun q₀ hq₀ => ?_⟩
  exact firstCrossing_uniform_terminal_levels (fun n => (hc n).sub (hc 0))
    (fun n => (hMh n).sub (hMh 0)) hstart hterminal hA hq₀

/-- The error is little-o of the packet width, uniformly in space and on every
compact interval of terminal mass fractions. The target uses the actual terminal excess. -/
def HasMassQuantileAsymptotics {K : Type*} [TopologicalSpace K]
    (ψ : ℝ → ℝ) (a : ℝ) (t L : ℕ → ℝ)
    (M : ℕ → ℝ → C(K, ℝ)) (Mh : ℕ → C(K, ℝ)) (T : ℝ) : Prop :=
  ∃ Q : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
    (∀ x, (Q x : ℝ) = packetCumulative ψ x) ∧
    ∀ q₀ q₁ : ℝ, 0 < q₀ → q₁ < 1 → ∀ d > (0 : ℝ),
      ∀ᶠ n in atTop, ∀ u, ∀ q : Icc (0 : ℝ) 1, q₀ ≤ (q : ℝ) → (q : ℝ) ≤ q₁ →
        |firstCrossing (fun v => (M n v - M 0 v) u) T (q * (Mh n - Mh 0) u) -
          (t n + L n * (Q.symm q : ℝ)) / a| < d * L n

theorem mass_quantile_asymptotics {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K]
    {ψ : ℝ → ℝ} {a T : ℝ} {t L : ℕ → ℝ}
    {M : ℕ → ℝ → C(K, ℝ)} {Mh : ℕ → C(K, ℝ)} {A : C(K, ℝ)}
    (hi : MeasureTheory.Integrable (fun x => ψ x ^ 2))
    (hM : 0 < ∫ x, ψ x ^ 2) {R : ℝ} (hb : ∀ x, |ψ x| ≤ R)
    (hp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (ha : 0 < a) (hL : ∀ n, 0 < L n) (hA : ∀ u, 0 < A u)
    (hfirst : HasMassFirstCrossings M Mh T)
    (herr : ∀ d > (0 : ℝ), ∀ᶠ n in atTop,
      (∀ v, T ≤ v →
        ‖M n v - M 0 v - packetCumulative ψ ((a * v - t n) / L n) • A‖ < d) ∧
      ‖Mh n - Mh 0 - A‖ < d) :
    HasMassQuantileAsymptotics ψ a t L M Mh T := by
  obtain ⟨Q, hQ⟩ := exists_packetCumulative_orderIso hi hM hb hp hs
  refine ⟨Q, hQ, fun q₀ q₁ hq₀ hq₁ d hd => ?_⟩
  have huc : UniformContinuous (fun q : Icc (0 : ℝ) 1 => (Q.symm q : ℝ)) :=
    CompactSpace.uniformContinuous_of_continuous
      (continuous_subtype_val.comp Q.symm.continuous)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.1 huc (d * a) (mul_pos hd ha)
  let κ := min δ (min q₀ (1 - q₁)) / 2
  have hκ : 0 < κ := div_pos (lt_min hδ (lt_min hq₀ (sub_pos.2 hq₁))) (by norm_num)
  have hκδ : κ < δ := by
    have := min_le_left δ (min q₀ (1 - q₁))
    dsimp [κ]
    linarith
  have hκq₀ : κ < q₀ := by
    have := (min_le_right δ (min q₀ (1 - q₁))).trans (min_le_left _ _)
    dsimp [κ]
    linarith
  have hκq₁ : κ < 1 - q₁ := by
    have := (min_le_right δ (min q₀ (1 - q₁))).trans (min_le_right _ _)
    dsimp [κ]
    linarith
  obtain ⟨u₀, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (show (univ : Set K).Nonempty from ⟨Classical.arbitrary K, mem_univ _⟩)
    A.continuous.continuousOn
  let ε := κ * A u₀ / 4
  have hε : 0 < ε := div_pos (mul_pos hκ (hA u₀)) (by norm_num)
  obtain ⟨hF0, hF1⟩ := packetCumulative_endpoints hM hs
  have hF := packetCumulative_monotone hi hM
  filter_upwards [herr ε hε, hfirst.2 q₀ hq₀] with n hn hfn
  intro u q hq0 hq1
  let v := firstCrossing (fun v => (M n v - M 0 v) u) T (q * (Mh n - Mh 0) u)
  let z := (a * v - t n) / L n
  have hroot := (hfn u).2 q hq0 (hq1.trans_lt hq₁)
  have hv : T ≤ v := hroot.1.1
  have heq : (M n v - M 0 v) u = q * (Mh n - Mh 0) u := hroot.1.2
  have he : |(M n v - M 0 v) u - packetCumulative ψ z * A u| < ε := by
    have hh := (ContinuousMap.norm_coe_le_norm
      (M n v - M 0 v - packetCumulative ψ z • A) u).trans_lt (hn.1 v hv)
    simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
      Real.norm_eq_abs] using hh
  have ht : |(Mh n - Mh 0) u - A u| < ε := by
    have hh := (ContinuousMap.norm_coe_le_norm (Mh n - Mh 0 - A) u).trans_lt hn.2
    simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using hh
  have hsmall : |packetCumulative ψ z - (q : ℝ)| < κ := by
    have hbound : A u * |packetCumulative ψ z - (q : ℝ)| < 2 * ε := by
      calc
        _ = |A u * (packetCumulative ψ z - (q : ℝ))| := by
          rw [abs_mul, abs_of_pos (hA u)]
        _ = |-((M n v - M 0 v) u - packetCumulative ψ z * A u) +
            q * ((Mh n - Mh 0) u - A u)| := by
          congr 1
          rw [heq]
          ring
        _ ≤ |(M n v - M 0 v) u - packetCumulative ψ z * A u| +
            |(q : ℝ)| * |(Mh n - Mh 0) u - A u| := by
          simpa only [abs_neg, abs_mul] using abs_add_le
            (-((M n v - M 0 v) u - packetCumulative ψ z * A u))
            ((q : ℝ) * ((Mh n - Mh 0) u - A u))
        _ ≤ |(M n v - M 0 v) u - packetCumulative ψ z * A u| +
            |(Mh n - Mh 0) u - A u| := by
          gcongr
          exact mul_le_of_le_one_left (abs_nonneg _) (by
            rw [abs_of_nonneg q.property.1]
            exact q.property.2)
        _ < 2 * ε := by linarith
    have hminu : A u₀ ≤ A u := hmin (mem_univ u)
    have hbound' : 2 * ε < A u * κ := by
      have := mul_le_mul_of_nonneg_right hminu hκ.le
      dsimp [ε]
      nlinarith [mul_pos hκ (hA u₀)]
    exact (mul_lt_mul_iff_right₀ (hA u)).1 (hbound.trans hbound')
  have hFz : 0 < packetCumulative ψ z ∧ packetCumulative ψ z < 1 := by
    obtain ⟨hl, hr⟩ := abs_lt.1 hsmall
    constructor <;> linarith
  have hz : z ∈ Icc (0 : ℝ) 1 := by
    constructor
    · by_contra hnz
      have := hF (le_of_lt (lt_of_not_ge hnz))
      rw [hF0] at this
      linarith [hFz.1]
    · by_contra hnz
      have := hF (le_of_lt (lt_of_not_ge hnz))
      rw [hF1] at this
      linarith [hFz.2]
  let x : Icc (0 : ℝ) 1 := ⟨z, hz⟩
  have hdist : dist (Q x) q < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, hQ]
    exact hsmall.trans hκδ
  have hinv : |z - (Q.symm q : ℝ)| < d * a := by
    simpa only [Q.symm_apply_apply, Real.dist_eq] using hclose hdist
  have halg : v - (t n + L n * (Q.symm q : ℝ)) / a =
      (L n / a) * (z - (Q.symm q : ℝ)) := by
    dsimp [z]
    field_simp [ha.ne', (hL n).ne']
    ring
  change |v - (t n + L n * (Q.symm q : ℝ)) / a| < d * L n
  rw [halg, abs_mul, abs_of_pos (div_pos (hL n) ha)]
  calc
    _ < (L n / a) * (d * a) := mul_lt_mul_of_pos_left hinv (div_pos (hL n) ha)
    _ = d * L n := by field_simp

end CauchyHorizon
