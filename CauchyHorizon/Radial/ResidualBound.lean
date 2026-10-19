import CauchyHorizon.Radial.ModeDerivative
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Compact-band normalization controls the exact radial-mode residual coefficients. -/

open Set

namespace CauchyHorizon.Background

theorem exists_compact_residual_tolerance (B : Background) (hb : B.criticalExponent < 1)
    {Y Z : ℝ} (hY : B.inner < Y) (hZ : Z < B.event) :
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).1 (B.event - y)
    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).2 (B.event - y)
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ y ∈ Icc Y Z, ∀ n l : ℝ, n < 0 →
        |Real.log (B.outerRate * n / B.F y)| + |l / n - B.outerRate| < η →
        l < 0 ∧
          |(l / (y * n) - B.outerRate / y) * B.criticalWeight y * W y| +
            |((n / (y * l) - 1 / (B.outerRate * y)) / B.criticalWeight y * X y +
              B.innerRate * (-1 / l - -1 / B.F y) * W y)| < ε ∧
          |(-1 / l) * W y| ≤ C := by
  intro X W
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let K : Set (ℝ × ℝ × ℝ) := Icc Y Z ×ˢ (Icc (-1) 1 ×ˢ Icc (a / 2) (a + 1))
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hyr (y : ℝ) (hy : y ∈ Icc Y Z) : y ∈ Ioo B.inner B.event :=
    ⟨hY.trans_le hy.1, hy.2.trans_lt hZ⟩
  have hy0 (q : ℝ × ℝ × ℝ) (hq : q ∈ K) : q.1 ≠ 0 := (B.inner_pos.trans (hyr q.1 hq.1).1).ne'
  have hs0 (q : ℝ × ℝ × ℝ) (hq : q ∈ K) : q.2.2 ≠ 0 := ((half_pos ha).trans_le hq.2.2.1).ne'
  have hF0 (q : ℝ × ℝ × ℝ) (hq : q ∈ K) : B.F q.1 ≠ 0 := (B.F_neg (hyr q.1 hq.1)).ne
  have hq0 (q : ℝ × ℝ × ℝ) (hq : q ∈ K) : B.criticalWeight q.1 ≠ 0 :=
    (B.criticalWeight_pos (hyr q.1 hq.1)).ne'
  have hXc : Continuous X := (continuous_extendCurve B.radialLength_pos.le _).comp (continuous_const.sub continuous_id)
  have hWc : Continuous W := (continuous_extendCurve B.radialLength_pos.le _).comp (continuous_const.sub continuous_id)
  have hqc : ContinuousOn (fun q : ℝ × ℝ × ℝ => B.criticalWeight q.1) K :=
    B.criticalWeight_continuousOn.comp continuousOn_fst (fun q hq => hyr q.1 hq.1)
  have hFc : ContinuousOn (fun q : ℝ × ℝ × ℝ => B.F q.1) K := by
    intro q hq
    have hn := hy0 q hq
    have hn2 := pow_ne_zero 2 hn
    apply ContinuousAt.continuousWithinAt
    dsimp [F, horizonFunction]
    fun_prop (disch := assumption)
  let c := fun q : ℝ × ℝ × ℝ => -a * Real.exp (-q.2.1) / (B.F q.1 * q.2.2)
  let R₁ := fun q : ℝ × ℝ × ℝ => (q.2.2 / q.1 - a / q.1) * B.criticalWeight q.1 * W q.1
  let R₂ := fun q : ℝ × ℝ × ℝ =>
    ((1 / (q.1 * q.2.2) - 1 / (a * q.1)) / B.criticalWeight q.1 * X q.1 +
      B.innerRate * (c q - -1 / B.F q.1) * W q.1)
  let R₃ := fun q : ℝ × ℝ × ℝ => c q * W q.1
  have hcc : ContinuousOn c K :=
    (show Continuous (fun q : ℝ × ℝ × ℝ => -a * Real.exp (-q.2.1)) by fun_prop).continuousOn.div
      (hFc.mul (by fun_prop)) (fun q hq => mul_ne_zero (hF0 q hq) (hs0 q hq))
  have h₁ : ContinuousOn R₁ K :=
    (((show ContinuousOn (fun q : ℝ × ℝ × ℝ => q.2.2) K by fun_prop).div continuousOn_fst hy0).sub
      (continuousOn_const.div continuousOn_fst hy0)).mul hqc |>.mul (hWc.comp continuous_fst).continuousOn
  have h₂ : ContinuousOn R₂ K := by
    apply ContinuousOn.add
    · apply ContinuousOn.mul
      · apply ContinuousOn.div _ hqc hq0
        exact (continuousOn_const.div (by fun_prop) (fun q hq => mul_ne_zero (hy0 q hq) (hs0 q hq))).sub
          (continuousOn_const.div (by fun_prop) (fun q hq => mul_ne_zero ha.ne' (hy0 q hq)))
      · exact (hXc.comp continuous_fst).continuousOn
    · exact (continuousOn_const.mul (hcc.sub (continuousOn_const.div hFc hF0))).mul
        (hWc.comp continuous_fst).continuousOn
  have h₃ : ContinuousOn R₃ K := hcc.mul (hWc.comp continuous_fst).continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn h₃
  refine ⟨max 1 C₀, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous (h₁.abs.add h₂.abs)) ε hε
  let η := min δ (min 1 (a / 2))
  have hη : 0 < η := lt_min hδ (lt_min zero_lt_one (half_pos ha))
  refine ⟨η, hη, ?_⟩
  intro y hy n l hn herr
  let q : ℝ × ℝ × ℝ := (y, Real.log (a * n / B.F y), l / n)
  have hl : |q.2.1| < η := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt herr
  have hs : |q.2.2 - a| < η := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt herr
  have hl1 := hl.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs1 := hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs2 := hs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hqK : q ∈ K := by
    refine ⟨hy, ⟨(abs_lt.1 hl1).1.le, (abs_lt.1 hl1).2.le⟩, ?_⟩
    constructor <;> linarith only [(abs_lt.1 hs1).2, (abs_lt.1 hs2).1]
  have hcenter : (y, (0 : ℝ), a) ∈ K :=
    ⟨hy, ⟨by norm_num, by norm_num⟩, ⟨half_le_self ha.le, le_add_of_nonneg_right zero_le_one⟩⟩
  have hdist : dist q (y, (0 : ℝ), a) < δ := by
    simpa only [Prod.dist_eq, Real.dist_eq, show q.1 = y from rfl, sub_self, abs_zero, sub_zero, max_lt_iff] using
      And.intro hδ (And.intro (hl.trans_le (min_le_left _ _)) (hs.trans_le (min_le_left _ _)))
  have hcenterC : c (y, 0, a) = -1 / B.F y := by
    dsimp only [c]
    rw [neg_zero, Real.exp_zero, mul_one]
    field_simp [ha.ne']
  have hzero : |R₁ (y, 0, a)| + |R₂ (y, 0, a)| = 0 := by
    simp only [R₁, R₂, hcenterC, mul_comm y a, sub_self, zero_div, zero_mul, mul_zero,
      add_zero, abs_zero]
  have he := hnear q hqK (y, 0, a) hcenter hdist
  have he' : |R₁ q| + |R₂ q| < ε := by
    simpa only [Real.dist_eq, Pi.add_apply, hzero, sub_zero,
      abs_of_nonneg (add_nonneg (abs_nonneg (R₁ q)) (abs_nonneg (R₂ q)))] using he
  have hlam : l < 0 := by
    have hpos : 0 < l / n := (half_pos ha).trans_le hqK.2.2.1
    by_contra hh
    exact not_lt_of_ge (div_nonpos_of_nonneg_of_nonpos (le_of_not_gt hh) hn.le) hpos
  have hnorm : 0 < a * n / B.F y := div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ha hn) (B.F_neg (hyr y hy))
  have hceq : c q = -1 / l := by
    dsimp only [c, q]
    rw [Real.exp_neg, Real.exp_log hnorm]
    field_simp [ha.ne', hn.ne, hlam.ne, (B.F_neg (hyr y hy)).ne]
  have hAeq : (l / n) / y = l / (y * n) := by ring
  have hBeq : 1 / (y * (l / n)) = n / (y * l) := by
    field_simp [hn.ne]
  refine ⟨hlam, ?_, ?_⟩
  · simpa only [R₁, R₂, hceq, q, hAeq, hBeq] using he'
  · have hh := hC₀ q hqK
    simpa only [Real.norm_eq_abs, R₃, hceq, q] using hh.trans (le_max_right _ _)

end CauchyHorizon.Background
