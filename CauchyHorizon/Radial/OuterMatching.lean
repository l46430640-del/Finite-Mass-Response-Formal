import CauchyHorizon.Radial.Mode

/-! Exact outer amplitudes and qualitative matching to the normalized radial mode. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon.Background

theorem outer_matching_coefficients (B : Background) {y c R : ℝ}
    (hy : y ∈ Ioo B.inner B.event) (hc : 0 < c) :
    let b := B.criticalExponent
    let Ch := R / (B.event * c ^ b)
    (B.outerRate / B.event) * R * c * b * (B.z y / c) ^ (b + 1) / (b + 1) =
      Ch * B.innerRate / (b + 1) * B.z y ^ (b + 1) ∧
      (b * R * (B.z y / c) ^ b) / B.criticalWeight y = Ch * B.event * b := by
  intro b Ch
  have hz := B.z_pos hy
  have hcb : 0 < c ^ b := Real.rpow_pos_of_pos hc _
  have hzb : 0 < B.z y ^ b := Real.rpow_pos_of_pos hz _
  have hcrit : B.outerRate * b = B.innerRate := by
    dsimp only [b, criticalExponent]
    field_simp [B.outerRate_pos.ne']
  constructor
  · dsimp only [Ch]
    rw [Real.div_rpow hz.le hc.le, Real.rpow_add hc, Real.rpow_one, ← hcrit]
    field_simp [hc.ne', hcb.ne', B.event_pos.ne']
  · rw [B.criticalWeight_eq_z_rpow hy, Real.div_rpow hz.le hc.le]
    dsimp only [Ch]
    field_simp [hcb.ne', hzb.ne', B.event_pos.ne']
    rfl

theorem exists_outer_mode_tolerance (B : Background) (hb : B.criticalExponent < 1)
    {c R ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    let b := B.criticalExponent
    let Ch := R / (B.event * c ^ b)
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).1 (B.event - y)
    let V := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).2 (B.event - y)
    ∃ Y₀ : ℝ, Y₀ ∈ Ioo B.inner B.event ∧ ∀ y ∈ Ioo Y₀ B.event,
      (B.event - y) ^ (2 * b) / (B.criticalWeight y) ^ 2 ≤ 4 ∧
        ((B.outerRate / B.event) * R * c * b * (B.z y / c) ^ (b + 1) / (b + 1) - Ch * X y) ^ 2 +
          ((b * R * (B.z y / c) ^ b) / B.criticalWeight y - Ch * V y) ^ 2 ≤ ε := by
  intro b Ch X V
  have hbpos : 0 < b := B.criticalExponent_pos
  have hbc : 0 < b + 1 := by linarith only [hbpos]
  have hXc : Continuous X := (continuous_extendCurve B.radialLength_pos.le _).comp (continuous_const.sub continuous_id)
  have hVc : Continuous V := (continuous_extendCurve B.radialLength_pos.le _).comp (continuous_const.sub continuous_id)
  have hX0 : X B.event = 0 := by
    simpa only [X, sub_self, extendCurve,
      projIcc_of_mem B.radialLength_pos.le (left_mem_Icc.2 B.radialLength_pos.le)] using (B.radialMode_initial hb).1
  have hV0 : V B.event = B.event * b := by
    simpa only [V, sub_self, extendCurve,
      projIcc_of_mem B.radialLength_pos.le (left_mem_Icc.2 B.radialLength_pos.le)] using (B.radialMode_initial hb).2
  have hzc : ContinuousAt B.z B.event := by
    have hi := (sub_pos.2 B.inner_lt_event).ne'
    have hlog : ContinuousAt B.coordinateLog B.event :=
      (((continuousAt_id.sub continuousAt_const).log hi).const_mul B.innerExponent).add
        (B.regularLog_continuousAt (B.negativeRoot_neg.trans B.event_pos) B.event_lt_cosmological)
    exact (continuousAt_const.sub continuousAt_id).mul (Real.continuous_exp.continuousAt.comp hlog)
  have hz0 : B.z B.event = 0 := by simp only [z, sub_self, zero_mul]
  let F := fun y => (Ch * B.innerRate / (b + 1) * B.z y ^ (b + 1) - Ch * X y) ^ 2 +
    (Ch * B.event * b - Ch * V y) ^ 2
  have hFc : ContinuousAt F B.event :=
    ((((hzc.rpow_const (Or.inr hbc.le)).const_mul (Ch * B.innerRate / (b + 1))).sub
      (hXc.continuousAt.const_mul Ch)).pow 2).add
      ((continuousAt_const.sub (hVc.continuousAt.const_mul Ch)).pow 2)
  have hF0 : F B.event = 0 := by
    simp only [F, hz0, Real.zero_rpow hbc.ne', hX0, hV0, mul_zero]
    ring
  have hsmall : ∀ᶠ y in 𝓝 B.event, F y < ε := hFc.tendsto.eventually_lt_const (by rwa [hF0])
  have hweight : ∀ᶠ y in 𝓝[<] B.event, (1 / 2 : ℝ) < B.criticalWeight y / (B.event - y) ^ b :=
    B.criticalWeight_outer_normalization.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨Y₁, hY₁, hnear⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1
    (hweight.and (hsmall.filter_mono inf_le_left))
  let Y₀ := max Y₁ ((B.inner + B.event) / 2)
  have hY₀ : Y₀ ∈ Ioo B.inner B.event :=
    ⟨(by linarith only [B.inner_lt_event] : B.inner < (B.inner + B.event) / 2).trans_le (le_max_right _ _),
      max_lt hY₁ (by linarith only [B.inner_lt_event])⟩
  refine ⟨Y₀, hY₀, ?_⟩
  intro y hy
  have hyr : y ∈ Ioo B.inner B.event := ⟨hY₀.1.trans hy.1, hy.2⟩
  have hh := hnear ⟨(le_max_left _ _).trans_lt hy.1, hy.2⟩
  have hgap : 0 < B.event - y := sub_pos.2 hy.2
  have hpow : 0 < (B.event - y) ^ b := Real.rpow_pos_of_pos hgap _
  have hq : 0 < B.criticalWeight y := B.criticalWeight_pos hyr
  refine ⟨?_, ?_⟩
  · have hlow := (lt_div_iff₀ hpow).1 hh.1
    have hsq := (sq_le_sq₀ hpow.le (mul_pos (by norm_num : (0 : ℝ) < 2) hq).le).2
      (show (B.event - y) ^ b ≤ 2 * B.criticalWeight y by linarith only [hlow])
    have heq : (B.event - y) ^ (2 * b) = ((B.event - y) ^ b) ^ (2 : ℕ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hgap.le]
      congr 1
      ring
    apply (div_le_iff₀ (sq_pos_of_pos hq)).2
    rw [heq]
    nlinarith only [hsq]
  · rw [(B.outer_matching_coefficients hyr hc (R := R)).1,
      (B.outer_matching_coefficients hyr hc (R := R)).2]
    exact hh.2.le

end CauchyHorizon.Background
