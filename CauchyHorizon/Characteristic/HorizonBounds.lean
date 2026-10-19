import CauchyHorizon.Characteristic.HorizonData
import CauchyHorizon.Reduced.RadialFlux

/-! Radius and lambda budgets, and the negative potential near the event root. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

theorem horizonFunction_exponential_bound {R M δ ε d e Λ : ℝ} (hd : 0 < d)
    (hδ : 0 ≤ δ) (hδR : δ < R) (hε : 0 ≤ ε) {r m : ℝ → ℝ}
    (hr : ∀ t ∈ Ici (0 : ℝ), ‖r t - R‖ ≤ δ * Real.exp (-d * t))
    (hm : ∀ t ∈ Ici (0 : ℝ), ‖m t - M‖ ≤ ε * Real.exp (-d * t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ici (0 : ℝ),
      ‖horizonFunction (r t) (m t) e Λ - horizonFunction R M e Λ‖ ≤ C * Real.exp (-d * t) := by
  let S := Icc (R - δ) (R + δ) ×ˢ Icc (M - ε) (M + ε)
  have hc : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => horizonFunction p.1 p.2 e Λ) S := by
    intro p hp
    have hp0 : p.1 ≠ 0 := ((sub_pos.2 hδR).trans_le hp.1.1).ne'
    unfold horizonFunction
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
  apply hl.trans
  have hmax : max ‖r t - R‖ ‖m t - M‖ ≤ (δ + ε) * Real.exp (-d * t) := by
    apply max_le
    · exact (hr t ht).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
    · exact (hm t ht).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  exact (mul_le_mul_of_nonneg_left hmax L.coe_nonneg).trans_eq (by ring)

namespace Background

variable (B : Background)

theorem horizon_radius_lambda_bounds {s H δ : ℝ} (hs : 0 < s) (hH : 0 ≤ H)
    (hδ : 0 ≤ δ) (hδR : δ < B.event) {h r : ℝ → ℝ}
    (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hr : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ δ * Real.exp (-(2 * s) * t)) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (B.event - δ) (B.event + δ) ∧
      |horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological| ≤ W * Real.exp (-(2 * s) * t) := by
  have hm (t : ℝ) (_ht : t ∈ Ici (0 : ℝ)) :
      ‖horizonMass B.mass h t - B.mass‖ ≤ H ^ 2 / (4 * s) * Real.exp (-(2 * s) * t) := by
    obtain ⟨hp, hbound⟩ := horizonMass_bounds hs hH hb B.mass t
    simpa only [norm_sub_rev, Real.norm_of_nonneg hp] using hbound
  obtain ⟨W, hW, hw⟩ := horizonFunction_exponential_bound (by positivity : 0 < 2 * s)
    hδ hδR (by positivity : 0 ≤ H ^ 2 / (4 * s)) hr hm (e := B.charge) (Λ := B.cosmological)
  refine ⟨W, hW, ?_⟩
  intro t ht
  have he : Real.exp (-(2 * s) * t) ≤ 1 := Real.exp_le_one_iff.2
    (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) ht)
  have hr' := abs_le.1 ((hr t ht).trans (mul_le_of_le_one_right hδ he))
  exact ⟨⟨by linarith only [hr'.1], by linarith only [hr'.2]⟩,
    by simpa only [B.root_event, sub_zero, Real.norm_eq_abs] using hw t ht⟩

theorem radialPotential_event : radialPotential B.event B.charge B.cosmological = -B.outerRate / 4 := by
  have he : -4 * radialPotential B.event B.charge B.cosmological =
      horizonFunction B.event B.mass B.charge B.cosmological / B.event +
        2 * horizonK B.event B.mass B.charge B.cosmological := by
    unfold radialPotential horizonFunction horizonK
    field_simp [B.event_pos.ne']
    ring
  rw [B.root_event, zero_div, zero_add, B.horizonK_event] at he
  linarith only [he]

theorem exists_negative_radial_potential : ∃ η : ℝ, 0 < η ∧ η < B.event ∧
    ∀ r ∈ Icc (B.event - η) (B.event + η), radialPotential r B.charge B.cosmological ≤ -B.outerRate / 8 := by
  have hp : ContinuousAt (fun r => radialPotential r B.charge B.cosmological) B.event := by
    unfold radialPotential
    fun_prop (disch := positivity [B.event_pos])
  have he : ∀ᶠ r in 𝓝 B.event, radialPotential r B.charge B.cosmological < -B.outerRate / 8 :=
    hp.tendsto.eventually_lt_const (by rw [B.radialPotential_event]; linarith only [B.outerRate_pos])
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 he
  let η := min (ε / 2) (B.event / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity [B.event_pos])
  refine ⟨η, hη, (min_le_right _ _).trans_lt (half_lt_self B.event_pos), ?_⟩
  intro r hr
  have hball : r ∈ Metric.ball B.event ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hh : η < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    constructor <;> linarith only [hr.1, hr.2, hh]
  exact (hb hball).le

end Background
end CauchyHorizon
