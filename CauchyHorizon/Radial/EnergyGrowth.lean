import CauchyHorizon.Radial.ResidualBound

/-! The integrable reference growth controls the actual normalized band coefficients. -/

open Set MeasureTheory

namespace CauchyHorizon.Background

noncomputable def energyGrowth (B : Background) (r : ℝ) : ℝ :=
  B.outerRate * B.criticalWeight r / r + 1 / (B.outerRate * r * B.criticalWeight r)

theorem energyGrowth_regular (B : Background) (hb : B.criticalExponent < 1) :
    ContinuousOn B.energyGrowth (Ioo B.inner B.event) ∧
      IntervalIntegrable B.energyGrowth volume B.inner B.event ∧
      ∀ r ∈ Icc B.inner B.event, 0 ≤ B.energyGrowth r := by
  have he (r : ℝ) : B.energyGrowth r = B.coefficientX (B.event - r) + B.coefficientV (B.event - r) := by
    simp only [energyGrowth, coefficientX, coefficientV, sub_sub_cancel]
  have hi := ((B.coefficients_integrable hb).1.add (B.coefficients_integrable hb).2).comp_sub_left B.event
  have heq : (fun r => B.coefficientX (B.event - r) + B.coefficientV (B.event - r)) = B.energyGrowth := funext (fun r => (he r).symm)
  have hbounds : B.event - B.radialLength = B.inner := by dsimp only [radialLength]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← heq]
    apply ((B.coefficients_continuousOn).1.add (B.coefficients_continuousOn).2).comp
      (continuousOn_const.sub continuousOn_id)
    intro r hr
    change B.event - r ∈ Ioo 0 (B.event - B.inner)
    constructor <;> linarith [hr.1, hr.2]
  · simpa only [heq, sub_zero, hbounds] using hi.symm
  · intro r hr
    rw [he]
    have hm : B.event - r ∈ Icc 0 B.radialLength := by
      dsimp only [radialLength]
      constructor <;> linarith [hr.1, hr.2]
    exact add_nonneg (B.coefficients_nonneg hm).1 (B.coefficients_nonneg hm).2

set_option maxHeartbeats 1000000 in
theorem exists_compact_energy_tolerance (B : Background) {Y Z ε : ℝ}
    (hY : B.inner < Y) (hZ : Z < B.event) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ y ∈ Icc Y Z, ∀ n l : ℝ, n < 0 →
      |Real.log (B.outerRate * n / B.F y)| + |l / n - B.outerRate| < η →
      |l / (y * n) * B.criticalWeight y + n / (y * l) / B.criticalWeight y| +
        |2 * B.innerRate * (-1 / l - -1 / B.F y)| < B.energyGrowth y + ε := by
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let K : Set (ℝ × ℝ × ℝ) := Icc Y Z ×ˢ (Icc (-1) 1 ×ˢ Icc (a / 2) (a + 1))
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hyr (y : ℝ) (hy : y ∈ Icc Y Z) : y ∈ Ioo B.inner B.event :=
    ⟨hY.trans_le hy.1, hy.2.trans_lt hZ⟩
  have hy0 (q : ℝ × ℝ × ℝ) (hq : q ∈ K) : q.1 ≠ 0 := (B.inner_pos.trans (hyr q.1 hq.1).1).ne'
  have hs0 (q : ℝ × ℝ × ℝ) (hq : q ∈ K) : q.2.2 ≠ 0 := ((half_pos ha).trans_le hq.2.2.1).ne'
  have hF0 (q : ℝ × ℝ × ℝ) (hq : q ∈ K) : B.F q.1 ≠ 0 := (B.F_neg (hyr q.1 hq.1)).ne
  have hq0 (q : ℝ × ℝ × ℝ) (hq : q ∈ K) : B.criticalWeight q.1 ≠ 0 := (B.criticalWeight_pos (hyr q.1 hq.1)).ne'
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
  let E := fun q : ℝ × ℝ × ℝ =>
    |q.2.2 / q.1 * B.criticalWeight q.1 + 1 / (q.1 * q.2.2) / B.criticalWeight q.1| +
      |2 * B.innerRate * (c q - -1 / B.F q.1)|
  have hcc : ContinuousOn c K :=
    (show Continuous (fun q : ℝ × ℝ × ℝ => -a * Real.exp (-q.2.1)) by fun_prop).continuousOn.div
      (hFc.mul (by fun_prop)) (fun q hq => mul_ne_zero (hF0 q hq) (hs0 q hq))
  have hEc : ContinuousOn E K := by
    have hA := ((show ContinuousOn (fun q : ℝ × ℝ × ℝ => q.2.2) K by fun_prop).div continuousOn_fst hy0).mul hqc
    have hB : ContinuousOn (fun q : ℝ × ℝ × ℝ => 1 / (q.1 * q.2.2) / B.criticalWeight q.1) K :=
      (continuousOn_const.div (continuousOn_fst.mul (by fun_prop))
      (fun q hq => mul_ne_zero (hy0 q hq) (hs0 q hq))).div hqc hq0
    exact (hA.add hB).abs.add ((continuousOn_const.mul (hcc.sub (continuousOn_const.div hFc hF0))).abs)
  obtain ⟨δ, hδ, hnear⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hEc) ε hε
  let η := min δ (min 1 (a / 2))
  refine ⟨η, lt_min hδ (lt_min zero_lt_one (half_pos ha)), ?_⟩
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
  have hcenterE : E (y, 0, a) = B.energyGrowth y := by
    have hbase : a / y * B.criticalWeight y + 1 / (y * a) / B.criticalWeight y = B.energyGrowth y := by
      dsimp only [energyGrowth, a]
      ring
    have hpos : 0 ≤ B.energyGrowth y := by
      dsimp only [energyGrowth]
      have hypos := B.inner_pos.trans (hyr y hy).1
      have hqpos := B.criticalWeight_pos (hyr y hy)
      positivity
    simp only [E, hcenterC, sub_self, mul_zero, abs_zero, add_zero, hbase, abs_of_nonneg hpos]
  have he : E q < B.energyGrowth y + ε := by
    have hh := (abs_lt.1 (show |E q - E (y, 0, a)| < ε by
      simpa only [Real.dist_eq] using hnear q hqK (y, 0, a) hcenter hdist)).2
    rw [hcenterE] at hh
    linarith only [hh]
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
  have hBeq : 1 / (y * (l / n)) = n / (y * l) := by field_simp [hn.ne]
  simpa only [E, hceq, q, hAeq, hBeq] using he

end CauchyHorizon.Background
