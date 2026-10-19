import CauchyHorizon.Radial.Background
import Mathlib.Topology.Order.Compact

/-! A signed restoring factor on a fixed neighborhood of the inner root. -/

open Set

namespace CauchyHorizon.Background

theorem exists_inner_restoring_factor (B : Background) :
    ∃ d : ℝ → ℝ, ∃ d₀ : ℝ, 0 < d₀ ∧
      ContinuousOn d (Icc (B.inner / 2) ((B.inner + B.event) / 2)) ∧
      d B.inner = 2 * B.innerRate ∧
      ∀ r ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2),
        d₀ ≤ d r ∧ B.F r = -(r - B.inner) * d r := by
  let d := fun r => B.cosmological * (B.event - r) * (B.cosmologicalRadius - r) *
    (r - B.negativeRoot) / (3 * r ^ 2)
  have hrange (r : ℝ) (hr : r ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2)) :
      0 < r ∧ r < B.event := by
    constructor <;> linarith only [hr.1, hr.2, B.inner_pos, B.inner_lt_event]
  have hc : ContinuousOn d (Icc (B.inner / 2) ((B.inner + B.event) / 2)) := by
    intro r hr
    have hr0 := (hrange r hr).1.ne'
    unfold d
    fun_prop (disch := positivity)
  have hd (r : ℝ) (hr : r ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2)) : 0 < d r := by
    have hrr := hrange r hr
    exact div_pos (mul_pos (mul_pos (mul_pos B.cosmological_pos (sub_pos.2 hrr.2))
      (sub_pos.2 (hrr.2.trans B.event_lt_cosmological)))
      (sub_pos.2 (B.negativeRoot_neg.trans hrr.1)))
      (mul_pos (by norm_num) (sq_pos_of_pos hrr.1))
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 (by linarith only [B.event_pos])) hc
  refine ⟨d, d r, hd r hr, hc, ?_, ?_⟩
  · dsimp only [d, innerRate]
    ring
  · intro t ht
    refine ⟨hmin ht, ?_⟩
    rw [B.factorization (hrange t ht).1.ne']
    dsimp only [d]
    ring

end CauchyHorizon.Background
