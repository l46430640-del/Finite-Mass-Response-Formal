import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Linarith

/-! First attainment of a level by a continuous, possibly nonmonotone curve. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

noncomputable def firstCrossing (f : ℝ → ℝ) (T q : ℝ) : ℝ :=
  sInf {v | T ≤ v ∧ f v = q}

theorem firstCrossing_of_bracket {f : ℝ → ℝ} {T a b q : ℝ}
    (hc : ContinuousOn f (Ici T)) (hTa : T ≤ a) (hab : a ≤ b)
    (hbefore : ∀ v, T ≤ v → v < a → f v < q) (ha : f a ≤ q) (hb : q ≤ f b) :
    IsLeast {v | T ≤ v ∧ f v = q} (firstCrossing f T q) ∧
      a ≤ firstCrossing f T q ∧ firstCrossing f T q ≤ b := by
  let S := {v | T ≤ v ∧ f v = q}
  have hclosed : IsClosed S :=
    hc.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  obtain ⟨v, hv, he⟩ := intermediate_value_Icc hab
    (hc.mono (fun _ hx => hTa.trans hx.1)) ⟨ha, hb⟩
  have hvS : v ∈ S := ⟨hTa.trans hv.1, he⟩
  have hleast := hclosed.isLeast_csInf ⟨v, hvS⟩ ⟨T, fun _ hx => hx.1⟩
  change IsLeast S (firstCrossing f T q) at hleast
  refine ⟨hleast, ?_, (hleast.2 hvS).trans hv.2⟩
  by_contra hn
  have hh := hbefore (firstCrossing f T q) hleast.1.1 (lt_of_not_ge hn)
  rw [hleast.1.2] at hh
  exact lt_irrefl _ hh

theorem firstCrossing_of_limit {f : ℝ → ℝ} {T q H : ℝ}
    (hc : ContinuousOn f (Ici T)) (hT : f T < q)
    (hlim : Tendsto f atTop (𝓝 H)) (hq : q < H) :
    IsLeast {v | T ≤ v ∧ f v = q} (firstCrossing f T q) := by
  obtain ⟨b, hb, hfb⟩ := ((eventually_ge_atTop T).and
    (hlim.eventually (eventually_gt_nhds hq))).exists
  exact (firstCrossing_of_bracket hc le_rfl hb
    (fun _ hv hvT => False.elim (not_lt_of_ge hv hvT)) hT.le hfb.le).1

theorem firstCrossing_profile_bracket {f F : ℝ → ℝ} {T a b q A d : ℝ}
    (hc : ContinuousOn f (Ici T)) (hF : Monotone F) (hA : 0 ≤ A)
    (he : ∀ v, T ≤ v → |f v - A * F v| ≤ d)
    (hTa : T ≤ a) (hab : a ≤ b) (ha : A * F a + d < q) (hb : q < A * F b - d) :
    IsLeast {v | T ≤ v ∧ f v = q} (firstCrossing f T q) ∧
      a ≤ firstCrossing f T q ∧ firstCrossing f T q ≤ b := by
  have hlow (v : ℝ) (hv : T ≤ v) (hva : v ≤ a) : f v < q := by
    have hh := (abs_le.1 (he v hv)).2
    have hm := mul_le_mul_of_nonneg_left (hF hva) hA
    linarith only [hh, hm, ha]
  apply firstCrossing_of_bracket hc hTa hab (fun v hv hva => hlow v hv hva.le)
    (hlow a hTa le_rfl).le
  have hh := (abs_le.1 (he b (hTa.trans hab))).1
  linarith only [hh, hb]

theorem firstCrossing_uniform_terminal_levels {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] {D : ℕ → ℝ → C(K, ℝ)} {H : ℕ → C(K, ℝ)}
    {A : C(K, ℝ)} {T : ℝ} (hc : ∀ n, ContinuousOn (D n) (Ici T))
    (htime : ∀ n, Tendsto (D n) atTop (𝓝 (H n)))
    (hstart : Tendsto (fun n => D n T) atTop (𝓝 0))
    (hterminal : Tendsto H atTop (𝓝 A)) (hA : ∀ u, 0 < A u)
    {q₀ : ℝ} (hq₀ : 0 < q₀) :
    ∀ᶠ n in atTop, ∀ u, 0 < H n u ∧ ∀ q, q₀ ≤ q → q < 1 →
      IsLeast {v | T ≤ v ∧ D n v u = q * H n u}
        (firstCrossing (fun v => D n v u) T (q * H n u)) := by
  obtain ⟨u₀, _hu₀, hmin⟩ := isCompact_univ.exists_isMinOn
    (show (univ : Set K).Nonempty from ⟨Classical.arbitrary K, mem_univ _⟩) A.continuous.continuousOn
  have hpos := hA u₀
  have hs : Tendsto (fun n => ‖D n T‖) atTop (𝓝 0) := by simpa only [norm_zero] using hstart.norm
  filter_upwards [(Metric.tendsto_nhds (u := H)).1 hterminal (A u₀ / 2) (half_pos hpos),
    (tendsto_order.1 hs).2 (q₀ * (A u₀ / 2)) (mul_pos hq₀ (half_pos hpos))] with n hn hsmall
  intro u
  have hpoint : |H n u - A u| < A u₀ / 2 := by
    simpa only [Real.dist_eq] using (ContinuousMap.dist_apply_le_dist u).trans_lt hn
  have hfloor : A u₀ / 2 < H n u := by
    have hh : A u₀ ≤ A u := hmin (mem_univ u)
    have hl := (abs_lt.1 hpoint).1
    linarith only [hh, hl]
  have hHpos := (half_pos hpos).trans hfloor
  refine ⟨hHpos, ?_⟩
  intro q hq hq1
  have hstartq : D n T u < q * H n u := by
    have hv : D n T u ≤ ‖D n T‖ :=
      (le_abs_self _).trans ((D n T).norm_coe_le_norm u)
    have hm := mul_le_mul_of_nonneg_right hq hHpos.le
    have hl := mul_le_mul_of_nonneg_left hfloor.le hq₀.le
    linarith only [hv, hsmall, hm, hl]
  exact firstCrossing_of_limit ((continuous_eval_const u).comp_continuousOn (hc n)) hstartq
    ((continuous_eval_const u).tendsto (H n) |>.comp (htime n))
    (by simpa only [one_mul] using mul_lt_mul_of_pos_right hq1 hHpos)

end CauchyHorizon
