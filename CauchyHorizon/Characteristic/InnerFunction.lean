import CauchyHorizon.Characteristic.InnerMargin

/-! The simple inner root transfers radius and mass errors to the outgoing velocity. -/

open Set

namespace CauchyHorizon.Background

theorem exists_inner_F_bound (B : Background) :
    ∃ L : ℝ, 0 < L ∧ ∀ r ∈ Icc (B.inner / 2) (2 * B.inner), ∀ m κ : ℝ,
      κ ∈ Icc 0 1 → |κ * horizonFunction r m B.charge B.cosmological| ≤
        L * (|r - B.inner| + |m - B.mass|) := by
  have hρ : 0 < B.inner / 2 := half_pos B.inner_pos
  have hc : ContDiffOn ℝ 1 (fun r => horizonFunction r B.mass B.charge B.cosmological)
      (Icc (B.inner / 2) (2 * B.inner)) := by
    intro r hr
    have hr0 := (hρ.trans_le hr.1).ne'
    unfold horizonFunction
    fun_prop (disch := positivity)
  obtain ⟨L, hL⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C := max (L : ℝ) (4 / B.inner) + 1
  have hLC : (L : ℝ) ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hMC : 4 / B.inner ≤ C := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro r hr m κ hk
  have hcenter : B.inner ∈ Icc (B.inner / 2) (2 * B.inner) := by
    constructor <;> linarith only [B.inner_pos]
  have hb := hL.dist_le_mul r hr B.inner hcenter
  simp only [Real.dist_eq, B.root_inner, sub_zero] at hb
  have hm : |2 * (m - B.mass) / r| ≤ (4 / B.inner) * |m - B.mass| := by
    rw [abs_div, abs_mul, abs_of_pos (hρ.trans_le hr.1)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2 * |m - B.mass| / (B.inner / 2) :=
        div_le_div_of_nonneg_left (by positivity) hρ hr.1
      _ = _ := by ring
  calc
    _ = κ * |horizonFunction r m B.charge B.cosmological| := by rw [abs_mul, abs_of_nonneg hk.1]
    _ ≤ |horizonFunction r m B.charge B.cosmological| := mul_le_of_le_one_left (abs_nonneg _) hk.2
    _ ≤ |horizonFunction r B.mass B.charge B.cosmological| + |2 * (m - B.mass) / r| := by
      rw [horizonFunction_mass_difference r m B.mass]
      exact abs_sub _ _
    _ ≤ (L : ℝ) * |r - B.inner| + (4 / B.inner) * |m - B.mass| := add_le_add hb hm
    _ ≤ C * (|r - B.inner| + |m - B.mass|) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right hLC (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hMC (abs_nonneg _))

end CauchyHorizon.Background
