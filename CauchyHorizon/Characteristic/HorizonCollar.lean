import CauchyHorizon.Radial.Background
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The actual RN-dS terminal nonlinearity has a small Lipschitz constant near the event root. -/

open Set Filter
open scoped Topology NNReal

namespace CauchyHorizon.Background

variable (B : CauchyHorizon.Background)

noncomputable def horizonRemainder (y : ℝ) : ℝ := B.outerRate * y + B.F (B.event - y)

noncomputable def horizonCoupling (y : ℝ) : ℝ := 2 / (B.event - y)

theorem horizonRemainder_zero : B.horizonRemainder 0 = 0 := by
  simpa [horizonRemainder, F] using B.root_event

theorem horizonRemainder_strictDeriv : HasStrictDerivAt B.horizonRemainder 0 0 := by
  have hR := B.event_pos
  have hc : ContDiffAt ℝ 1 B.F B.event := by
    unfold F CauchyHorizon.horizonFunction
    fun_prop (disch := positivity)
  have hs := hc.hasStrictDerivAt' B.hasDerivAt_F_event (by norm_num)
  have hs' : HasStrictDerivAt B.F B.outerRate (B.event - id (0 : ℝ)) := by simpa using hs
  have hh := ((hasStrictDerivAt_id (0 : ℝ)).const_mul B.outerRate).add
    (hs'.comp 0 ((hasStrictDerivAt_id (0 : ℝ)).const_sub B.event))
  change HasStrictDerivAt B.horizonRemainder (B.outerRate * 1 + B.outerRate * (-1)) 0 at hh
  exact hh.congr_deriv (by ring)

theorem horizonCoupling_contDiff : ContDiffAt ℝ 1 B.horizonCoupling 0 := by
  have hR := B.event_pos
  unfold horizonCoupling
  fun_prop (disch := simpa using hR.ne')

theorem exists_horizon_collar {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ < B.event ∧ ∃ J : ℝ≥0,
      LipschitzOnWith ⟨c / 4, by positivity⟩ B.horizonRemainder (Icc (-δ) δ) ∧
      LipschitzOnWith J B.horizonCoupling (Icc (-δ) δ) := by
  have hgd : HasStrictFDerivAt B.horizonRemainder (0 : ℝ →L[ℝ] ℝ) 0 := by
    simpa using B.horizonRemainder_strictDeriv.hasStrictFDerivAt
  obtain ⟨s, hs, hgs⟩ := hgd.exists_lipschitzOnWith_of_nnnorm_lt
    ⟨c / 4, by positivity⟩ (by
      rw [nnnorm_zero]
      change (0 : ℝ) < c / 4
      positivity)
  obtain ⟨J, t, ht, hjt⟩ :=
    (B.horizonCoupling_contDiff.hasStrictFDerivAt (by norm_num)).exists_lipschitzOnWith
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.1 (inter_mem hs ht)
  let δ := min (ε / 2) (B.event / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity [B.event_pos])
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδR : δ < B.event := (min_le_right _ _).trans_lt (by linarith [B.event_pos])
  have hsub : Icc (-δ) δ ⊆ s ∩ t := by
    intro x hx
    apply he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact ⟨δ, hδ, hδR, J, hgs.mono (fun _ hx => (hsub hx).1),
    hjt.mono (fun _ hx => (hsub hx).2)⟩

end CauchyHorizon.Background
