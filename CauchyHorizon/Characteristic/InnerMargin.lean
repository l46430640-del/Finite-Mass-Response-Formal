import CauchyHorizon.Characteristic.HorizonRates

/-! A fixed neighborhood of the inner root controls the actual radial rate. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon.Background

theorem exists_inner_K_lipschitz (B : Background) :
    ∃ L : ℝ, 0 < L ∧ ∀ r ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2), ∀ m : ℝ,
      |horizonK r m B.charge B.cosmological + B.innerRate| ≤
        L * (|r - B.inner| + |m - B.mass|) := by
  have hρ : 0 < B.inner / 2 := half_pos B.inner_pos
  have hK : horizonK B.inner B.mass B.charge B.cosmological = -B.innerRate := by
    have hd := horizonFunction_hasDerivAt (hasDerivAt_id B.inner)
      (hasDerivAt_const B.inner B.mass) B.inner_pos.ne' B.charge B.cosmological
    have he := hd.unique B.hasDerivAt_F_inner
    simp only [id_eq, mul_one, mul_zero, zero_div, sub_zero] at he
    linarith only [he]
  have hc : ContDiffOn ℝ 1 (fun r => horizonK r B.mass B.charge B.cosmological)
      (Icc (B.inner / 2) ((B.inner + B.event) / 2)) := by
    intro r hr
    have hr0 := (hρ.trans_le hr.1).ne'
    unfold horizonK
    fun_prop (disch := positivity)
  obtain ⟨L, hL⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C := max (L : ℝ) (4 / B.inner ^ 2) + 1
  have hLC : (L : ℝ) ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hMC : 4 / B.inner ^ 2 ≤ C := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r hr m
  have hcenter : B.inner ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2) := by
    constructor <;> linarith only [B.inner_pos, B.inner_lt_event]
  have hb := hL.dist_le_mul r hr B.inner hcenter
  simp only [Real.dist_eq, hK, sub_neg_eq_add] at hb
  have hm : |(m - B.mass) / r ^ 2| ≤ (4 / B.inner ^ 2) * |m - B.mass| := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos (hρ.trans_le hr.1))]
    calc
      _ ≤ |m - B.mass| / (B.inner / 2) ^ 2 := div_le_div_of_nonneg_left (abs_nonneg _)
        (sq_pos_of_pos hρ) (sq_le_sq₀ hρ.le (hρ.trans_le hr.1).le |>.2 hr.1)
      _ = _ := by ring
  calc
    _ = |(horizonK r B.mass B.charge B.cosmological + B.innerRate) + (m - B.mass) / r ^ 2| := by
      congr 1
      unfold horizonK
      ring
    _ ≤ |horizonK r B.mass B.charge B.cosmological + B.innerRate| + |(m - B.mass) / r ^ 2| := abs_add_le _ _
    _ ≤ (L : ℝ) * |r - B.inner| + (4 / B.inner ^ 2) * |m - B.mass| := add_le_add hb hm
    _ ≤ C * (|r - B.inner| + |m - B.mass|) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right hLC (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hMC (abs_nonneg _))

theorem exists_inner_K_margin (B : Background) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ B.inner / 4 ∧ δ ≤ (B.event - B.inner) / 2 ∧
      ∀ r m : ℝ, |r - B.inner| ≤ δ → |m - B.mass| ≤ δ →
        3 * B.inner / 4 ≤ r ∧ |horizonK r m B.charge B.cosmological + B.innerRate| ≤ ε / 2 := by
  obtain ⟨L, hL, hbound⟩ := B.exists_inner_K_lipschitz
  let δ := min (ε / (4 * L)) (min (B.inner / 4) ((B.event - B.inner) / 2))
  have hδ : 0 < δ := by dsimp only [δ]; positivity [B.inner_pos, sub_pos.2 B.inner_lt_event]
  have hδr : δ ≤ B.inner / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδe : δ ≤ (B.event - B.inner) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hδL : δ * (4 * L) ≤ ε := (le_div_iff₀ (by positivity)).1 (min_le_left _ _)
  refine ⟨δ, hδ, hδr, hδe, ?_⟩
  intro r m hr hm
  have hrlow : 3 * B.inner / 4 ≤ r := by linarith only [(abs_le.1 hr).1, hδr]
  have hrange : r ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2) := by
    constructor <;> linarith only [hrlow, (abs_le.1 hr).2, hδe, B.inner_pos]
  refine ⟨hrlow, (hbound r hrange m).trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left (add_le_add hr hm) hL.le
  nlinarith only [hh, hδL]

end CauchyHorizon.Background
