import CauchyHorizon.Radial.Background
import Mathlib.Topology.Order.Compact

/-! A compact trapped band stays trapped under a one-sided mass error. -/

open Set

namespace CauchyHorizon.Background

theorem exists_band_margin (B : Background) {Y R : ℝ}
    (hY : B.inner < Y) (hYR : Y ≤ R) (hR : R < B.event) :
    ∃ ε q : ℝ, 0 < ε ∧ 0 < q ∧ ∀ r ∈ Icc Y R, ∀ m : ℝ,
      B.mass - ε ≤ m → horizonFunction r m B.charge B.cosmological ≤ -q := by
  have hY0 : 0 < Y := B.inner_pos.trans hY
  have hc : ContinuousOn B.F (Icc Y R) := by
    intro t ht
    have ht0 : t ≠ 0 := (hY0.trans_le ht.1).ne'
    unfold F horizonFunction
    fun_prop (disch := positivity)
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hYR) hc
  have hneg := B.F_neg ⟨hY.trans_le ht.1, ht.2.trans_lt hR⟩
  let q := -B.F t / 2
  have hq : 0 < q := by dsimp [q]; linarith only [hneg]
  refine ⟨q * Y / 2, q, by positivity, hq, ?_⟩
  intro r hr m hm
  have hr0 : 0 < r := hY0.trans_le hr.1
  have hd : horizonFunction r m B.charge B.cosmological = B.F r + 2 * (B.mass - m) / r := by
    unfold F horizonFunction
    ring
  have hm' : 2 * (B.mass - m) / r ≤ q := by
    apply (div_le_iff₀ hr0).2
    have hh := mul_le_mul_of_nonneg_left hr.1 hq.le
    linarith only [hm, hh]
  rw [hd]
  have hh : B.F r ≤ B.F t := hmax hr
  dsimp only [q] at hm' ⊢
  linarith only [hh, hm']

end CauchyHorizon.Background
