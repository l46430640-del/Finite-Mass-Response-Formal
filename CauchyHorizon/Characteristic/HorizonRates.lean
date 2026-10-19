import CauchyHorizon.Characteristic.HorizonRadius
import CauchyHorizon.Analysis.ExactRate
import CauchyHorizon.Analysis.ExponentialError

/-! Exact outgoing rates from the constructed mass and radius. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

theorem horizonK_continuous {r m : ℝ → ℝ} (hr : Continuous r) (hm : Continuous m)
    (hr0 : ∀ t, r t ≠ 0) (e Λ : ℝ) :
    Continuous (fun t => horizonK (r t) (m t) e Λ) :=
  ((hm.div (hr.pow 2) (fun t => pow_ne_zero 2 (hr0 t))).sub
    (continuous_const.div (hr.pow 3) (fun t => pow_ne_zero 3 (hr0 t)))).sub
    ((continuous_const.mul hr).div_const 3)

theorem horizonK_exponential_bound {R M δ ε d e Λ : ℝ} (hd : 0 < d)
    (hδ : 0 ≤ δ) (hδR : δ < R) (hε : 0 ≤ ε) {r m : ℝ → ℝ}
    (hr : ∀ t ∈ Ici (0 : ℝ), ‖r t - R‖ ≤ δ * Real.exp (-d * t))
    (hm : ∀ t ∈ Ici (0 : ℝ), ‖m t - M‖ ≤ ε * Real.exp (-d * t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ici (0 : ℝ),
      ‖horizonK (r t) (m t) e Λ - horizonK R M e Λ‖ ≤ C * Real.exp (-d * t) := by
  let S := Icc (R - δ) (R + δ) ×ˢ Icc (M - ε) (M + ε)
  have hc : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => horizonK p.1 p.2 e Λ) S := by
    intro p hp
    have hp0 : p.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le (sub_pos.2 hδR) hp.1.1)
    unfold horizonK
    fun_prop (disch := positivity)
  obtain ⟨L, hL⟩ := hc.exists_lipschitzOnWith (by norm_num)
    ((convex_Icc _ _).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  have hcenter : (R, M) ∈ S := ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  refine ⟨L * (δ + ε), by positivity, ?_⟩
  intro t ht
  have he : Real.exp (-d * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [show 0 ≤ t from ht])
  have hr' : ‖r t - R‖ ≤ δ := (hr t ht).trans (mul_le_of_le_one_right hδ he)
  have hm' : ‖m t - M‖ ≤ ε := (hm t ht).trans (mul_le_of_le_one_right hε he)
  have hp : (r t, m t) ∈ S := by
    rw [Real.norm_eq_abs, abs_le] at hr' hm'
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hl := hL.dist_le_mul (r t, m t) hp (R, M) hcenter
  simp only [Real.dist_eq, Prod.dist_eq] at hl
  calc
    _ ≤ L * max ‖r t - R‖ ‖m t - M‖ := hl
    _ ≤ L * ((δ + ε) * Real.exp (-d * t)) := by
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      apply max_le
      · exact (hr t ht).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
      · exact (hm t ht).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
    _ = _ := by ring

theorem exponentialFuture_integrable {d C : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hc : Continuous f) (hb : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ C * Real.exp (-d * t)) :
    IntegrableOn f (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hd) 0).const_mul C).mono'
    hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hb t (show (0 : ℝ) ≤ t from le_of_lt ht)

theorem horizonNu_exact_amplitude {K : ℝ → ℝ} {a : ℝ} (hK : Continuous K)
    (hi : IntegrableOn (fun t => 2 * K t - a) (Ioi 0)) :
    Tendsto (fun t => Real.exp (-a * t) * (-horizonNu K t)) atTop
      (𝓝 (Real.exp (∫ t in Ioi 0, 2 * K t - a))) := by
  have h := exact_rate_of_hasDerivAt (rate := -a) hi
    (ell := fun t => ∫ w in 0..t, 2 * K w) (fun t _ => by
      have hc : Continuous (fun w => 2 * K w) := continuous_const.mul hK
      exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
        (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt).congr_deriv (by ring))
  simpa only [horizonNu, neg_neg, sub_zero, intervalIntegral.integral_same, zero_add] using h

theorem horizonNu_exponential_bounds {K : ℝ → ℝ} {a d C : ℝ} (hK : Continuous K)
    (hd : 0 < d) (hC : 0 ≤ C)
    (hb : ∀ t ∈ Ici (0 : ℝ), |2 * K t - a| ≤ C * Real.exp (-d * t))
    {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-C / d) * Real.exp (a * t) ≤ -horizonNu K t ∧
      -horizonNu K t ≤ Real.exp (C / d) * Real.exp (a * t) := by
  have hbound := exponential_error_integral_bound (u := 0) (D := 0) (δ := 0) hd le_rfl ht hC le_rfl
    (fun w hw => by simpa only [zero_mul, zero_add, add_zero] using hb w hw.1)
    (by simp only [zero_mul, le_refl])
  simp only [zero_mul, add_zero] at hbound
  have herr := (intervalIntegral.abs_integral_le_integral_abs
    (f := fun w => 2 * K w - a) ht).trans hbound
  have h2 : Continuous (fun w => 2 * K w) := continuous_const.mul hK
  have hconst : Continuous (fun _ : ℝ => a) := continuous_const
  have heq : (∫ w in (0 : ℝ)..t, 2 * K w) = a * t + ∫ w in (0 : ℝ)..t, 2 * K w - a := by
    rw [intervalIntegral.integral_sub (h2.intervalIntegrable _ _)
      (hconst.intervalIntegrable _ _), intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hre : -horizonNu K t = Real.exp (∫ w in (0 : ℝ)..t, 2 * K w - a) * Real.exp (a * t) := by
    rw [horizonNu, neg_neg, heq, Real.exp_add, mul_comm]
  rw [hre]
  constructor
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by simpa only [neg_div] using (abs_le.1 herr).1))
      (Real.exp_pos _).le
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (abs_le.1 herr).2) (Real.exp_pos _).le

theorem horizonMass_tendsto {s H : ℝ} (hs : 0 < s) (hH : 0 ≤ H) {h : ℝ → ℝ}
    (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t)) (M : ℝ) :
    Tendsto (horizonMass M h) atTop (𝓝 M) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-(2 * s) * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have hm : Tendsto (fun t => horizonMass M h t - M) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun t => ?_) (by simpa using he.const_mul (H ^ 2 / (4 * s)))
    obtain ⟨hp, hb⟩ := horizonMass_bounds hs hH hb M t
    simpa only [norm_sub_rev, Real.norm_of_nonneg hp, neg_mul] using hb
  simpa only [sub_add_cancel, zero_add] using hm.add_const M

theorem horizon_inverse_factor_tendsto {K : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hK : Continuous K) (hi : IntegrableOn (fun t => 2 * K t - a) (Ioi 0)) :
    Tendsto (fun t => Real.exp (-(∫ w in 0..t, 2 * K w))) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha))
  have h := he.div (horizonNu_exact_amplitude hK hi) (Real.exp_ne_zero _)
  simp only [zero_div] at h
  apply h.congr' (Eventually.of_forall (fun t => ?_))
  simp [horizonNu, Real.exp_neg, div_mul_eq_div_div]

theorem terminal_linear_representation {K y f : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hK : Continuous K)
    (hi : IntegrableOn (fun t => 2 * K t - a) (Ioi 0))
    (hy : Continuous y) (hyend : Tendsto y atTop (𝓝 0))
    (hdy : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt y (2 * K t * y t - f t) t)
    (hf : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun w => Real.exp (-(∫ x in 0..w, 2 * K x)) * f w) (Ioi t) ∧
      y t = ∫ w in Ioi t, Real.exp (-(∫ x in t..w, 2 * K x)) * f w := by
  let A := fun w => ∫ x in 0..w, 2 * K x
  have hc : Continuous (fun w => 2 * K w) := continuous_const.mul hK
  have hA (w : ℝ) : HasDerivAt A (2 * K w) w :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 w)
      (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt
  have hAc : Continuous A := continuous_iff_continuousAt.2 (fun w => (hA w).continuousAt)
  have hd (w : ℝ) (hw : w ∈ Ioi t) :
      HasDerivAt (fun x => -(Real.exp (-A x) * y x)) (Real.exp (-A w) * f w) w := by
    have hw0 : 0 < w := lt_of_le_of_lt ht hw
    exact ((((hA w).neg.exp).mul (hdy w hw0)).neg).congr_deriv (by
      simp only [Pi.neg_apply]
      ring)
  have hp (w : ℝ) (hw : w ∈ Ioi t) : 0 ≤ Real.exp (-A w) * f w :=
    mul_nonneg (Real.exp_pos _).le (hf w (le_of_lt (lt_of_le_of_lt ht hw)))
  have hend : Tendsto (fun x => -(Real.exp (-A x) * y x)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_zero] using ((horizon_inverse_factor_tendsto ha hK hi).mul hyend).neg
  have hcont := ((Real.continuous_exp.comp hAc.neg).mul hy).neg.continuousWithinAt (s := Ici t) (x := t)
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hd hp hend
  have hftc := integral_Ioi_of_hasDerivAt_of_nonneg hcont hd hp hend
  change (∫ w in Ioi t, Real.exp (-A w) * f w) = 0 - -(Real.exp (-A t) * y t) at hftc
  refine ⟨hint, ?_⟩
  have hcancel : Real.exp (A t) * Real.exp (-A t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    y t = Real.exp (A t) * ∫ w in Ioi t, Real.exp (-A w) * f w := by
      rw [hftc]
      simp only [sub_neg_eq_add, zero_add, ← mul_assoc, hcancel, one_mul]
    _ = ∫ w in Ioi t, Real.exp (A t) * (Real.exp (-A w) * f w) := (integral_const_mul _ _).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _
      dsimp only
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      have he := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 t)
        (hc.intervalIntegrable t w)
      change A t + (∫ x in t..w, 2 * K x) = A w at he
      linarith

theorem terminal_linear_pos {K y f : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hK : Continuous K)
    (hi : IntegrableOn (fun t => 2 * K t - a) (Ioi 0))
    (hy : Continuous y) (hyend : Tendsto y atTop (𝓝 0))
    (hdy : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt y (2 * K t * y t - f t) t)
    (hf : ∀ t ∈ Ici (0 : ℝ), 0 < f t) {t : ℝ} (ht : 0 ≤ t) : 0 < y t := by
  obtain ⟨hint, heq⟩ := terminal_linear_representation ha hK hi hy hyend hdy
    (fun w hw => (hf w hw).le) ht
  rw [heq]
  have hc : Continuous (fun w => 2 * K w) := continuous_const.mul hK
  have hker (w : ℝ) : Real.exp (-(∫ x in t..w, 2 * K x)) * f w =
      Real.exp (∫ x in 0..t, 2 * K x) * (Real.exp (-(∫ x in 0..w, 2 * K x)) * f w) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    have he := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 t)
      (hc.intervalIntegrable t w)
    linarith
  have hki : IntegrableOn (fun w => Real.exp (-(∫ x in t..w, 2 * K x)) * f w) (Ioi t) := by
    simp_rw [hker]
    exact hint.const_mul _
  have hp (w : ℝ) (hw : w ∈ Ioi t) : 0 < Real.exp (-(∫ x in t..w, 2 * K x)) * f w :=
    mul_pos (Real.exp_pos _) (hf w (le_of_lt (lt_of_le_of_lt ht hw)))
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hki).2
  · have hsub : Ioi t ⊆ Function.support (fun w => Real.exp (-(∫ x in t..w, 2 * K x)) * f w) :=
      fun w hw => (hp w hw).ne'
    rw [inter_eq_self_of_subset_right hsub]
    simp only [Real.volume_Ioi, ENNReal.zero_lt_top]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw using (hp w hw).le

namespace Background

variable (B : Background)

theorem horizonK_event : horizonK B.event B.mass B.charge B.cosmological = B.outerRate / 2 := by
  have h := horizonFunction_hasDerivAt (hasDerivAt_id B.event)
    (hasDerivAt_const B.event B.mass) B.event_pos.ne' B.charge B.cosmological
  have he := h.unique B.hasDerivAt_F_event
  simp only [id_eq, mul_one, mul_zero, zero_div, sub_zero] at he
  linarith

theorem horizonK_remainder {s H δ : ℝ} (hs : 0 < s) (hH : 0 ≤ H)
    (hδ : 0 ≤ δ) (hδR : δ < B.event) {h r : ℝ → ℝ} (hc : Continuous h)
    (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t)) (hrc : Continuous r)
    (hrb : ∀ t, B.event - δ ≤ r t)
    (hr : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ δ * Real.exp (-(2 * s) * t)) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ici (0 : ℝ),
      ‖horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate / 2‖ ≤
        C * Real.exp (-(2 * s) * t)) ∧
    IntegrableOn (fun t =>
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate) (Ioi 0) := by
  have hm (t : ℝ) (_ht : t ∈ Ici (0 : ℝ)) :
      ‖horizonMass B.mass h t - B.mass‖ ≤ H ^ 2 / (4 * s) * Real.exp (-(2 * s) * t) := by
    obtain ⟨hp, hb⟩ := horizonMass_bounds hs hH hb B.mass t
    simpa only [norm_sub_rev, Real.norm_of_nonneg hp] using hb
  obtain ⟨C, hC, hbound⟩ := horizonK_exponential_bound (by positivity : 0 < 2 * s)
    hδ hδR (by positivity : 0 ≤ H ^ 2 / (4 * s)) hr hm (e := B.charge) (Λ := B.cosmological)
  rw [B.horizonK_event] at hbound
  refine ⟨⟨C, hC, hbound⟩, ?_⟩
  have hmc : Continuous (horizonMass B.mass h) := continuous_iff_continuousAt.2
    (fun t => (horizonMass_hasDerivAt hc (horizon_mass_integrable hs hH hc hb) B.mass t).continuousAt)
  have hK := horizonK_continuous hrc hmc
    (fun t => (lt_of_lt_of_le (sub_pos.2 hδR) (hrb t)).ne') B.charge B.cosmological
  apply exponentialFuture_integrable (C := 2 * C) (by positivity : 0 < 2 * s)
    ((continuous_const.mul hK).sub continuous_const)
  intro t ht
  change ‖2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate‖ ≤ _
  rw [show 2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate =
    2 * (horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate / 2) by ring,
    norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact (mul_le_mul_of_nonneg_left (hbound t ht) (by norm_num)).trans_eq (by ring)

end Background
end CauchyHorizon
