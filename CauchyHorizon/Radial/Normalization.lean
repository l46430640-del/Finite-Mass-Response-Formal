import CauchyHorizon.Radial.Coordinate

/-! Near the event root, radial-gap normalization fixes the background Jacobian and phase. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon.Background

theorem exists_outer_normalization_tolerance (B : Background) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ η < B.event - B.inner ∧
      ∀ (r u ν S : ℝ), 0 < u → 0 < S → |r - B.event| < η →
        |(-ν) / S - 1| < η → |(B.event - r) / (u * S) - 1| < η →
        r ∈ Ioo B.inner B.event ∧
          |u * ν / B.F r - 1 / B.outerRate| < ε ∧ |B.z r / (u * S) - 1| < ε := by
  let g := fun r : ℝ => -B.cosmological * (r - B.inner) * (r - B.cosmologicalRadius) *
    (r - B.negativeRoot) / (3 * r ^ 2)
  have hg : ContinuousAt g B.event := by
    dsimp only [g]
    fun_prop (disch := positivity [B.event_pos])
  have hg0 : g B.event = B.outerRate := rfl
  have hlog : ContinuousAt B.coordinateLog B.event := by
    unfold coordinateLog regularLog
    have hi := (sub_pos.2 B.inner_lt_event).ne'
    have hc := (sub_pos.2 B.event_lt_cosmological).ne'
    have hn := (sub_pos.2 (B.negativeRoot_neg.trans B.event_pos)).ne'
    fun_prop (disch := assumption)
  let J := fun q : ℝ × ℝ × ℝ => q.2.1 / (q.2.2 * g q.1)
  let Z := fun q : ℝ × ℝ × ℝ => Real.exp (B.coordinateLog q.1) * q.2.2
  let q₀ : ℝ × ℝ × ℝ := (B.event, 1, 1)
  have hJ : ContinuousAt J q₀ := by
    have hh := hg.comp_of_eq (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ × ℝ → ℝ) q₀) rfl
    dsimp only [J]
    fun_prop (disch := simpa only [q₀, one_mul, hg0] using B.outerRate_pos.ne')
  have hZ : ContinuousAt Z q₀ := by
    have hh := hlog.comp_of_eq (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ × ℝ → ℝ) q₀) rfl
    dsimp only [Z]
    fun_prop
  have hJ0 : J q₀ = 1 / B.outerRate := by simp only [J, q₀, one_mul, hg0]
  have hZ0 : Z q₀ = 1 := by simp only [Z, q₀, B.coordinateLog_event, Real.exp_zero, mul_one]
  have hnear : ∀ᶠ q in 𝓝 q₀, |J q - 1 / B.outerRate| < ε ∧ |Z q - 1| < ε := by
    apply (((hJ.tendsto.sub_const (1 / B.outerRate)).abs).eventually_lt_const
      (by simpa only [hJ0, sub_self, abs_zero] using hε)).and
    exact ((hZ.tendsto.sub_const 1).abs).eventually_lt_const
      (by simpa only [hZ0, sub_self, abs_zero] using hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnear
  let η := min (δ / 2) (min ((B.event - B.inner) / 2) (1 / 2))
  have hη : 0 < η := by dsimp only [η]; positivity [B.inner_lt_event]
  have hηδ : η < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hη1 : η ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hηr : η < B.event - B.inner :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self (sub_pos.2 B.inner_lt_event))
  refine ⟨η, hη, hη1, hηr, ?_⟩
  intro r u ν S hu hS hr hν hgap
  have hgap0 : 0 < B.event - r :=
    (div_pos_iff_of_pos_right (mul_pos hu hS)).1 (by linarith only [(abs_lt.1 hgap).1, hη1])
  have hrband : r ∈ Ioo B.inner B.event :=
    ⟨by linarith only [(abs_lt.1 hr).1, hηr], sub_pos.1 hgap0⟩
  have hbound := hball (show (r, (-ν) / S, (B.event - r) / (u * S)) ∈ Metric.ball q₀ δ from by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt (hr.trans hηδ) (max_lt (hν.trans hηδ) (hgap.trans hηδ)))
  have hF : B.F r = (r - B.event) * g r := by
    rw [B.factorization (B.inner_pos.trans hrband.1).ne']
    dsimp only [g]
    ring
  have hgr : g r ≠ 0 := by
    intro hz
    have hh := (B.F_neg hrband).ne
    rw [hF, hz, mul_zero] at hh
    exact hh rfl
  have hJr : J (r, (-ν) / S, (B.event - r) / (u * S)) = u * ν / B.F r := by
    dsimp only [J]
    rw [hF]
    field_simp [hu.ne', hS.ne', hgr, hgap0.ne', sub_ne_zero.2 hrband.2.ne]
    ring
  have hZr : Z (r, (-ν) / S, (B.event - r) / (u * S)) = B.z r / (u * S) := by
    dsimp only [Z, z]
    ring
  change |J (r, (-ν) / S, (B.event - r) / (u * S)) - 1 / B.outerRate| < ε ∧
    |Z (r, (-ν) / S, (B.event - r) / (u * S)) - 1| < ε at hbound
  rw [hJr, hZr] at hbound
  exact ⟨hrband, hbound⟩

end CauchyHorizon.Background
