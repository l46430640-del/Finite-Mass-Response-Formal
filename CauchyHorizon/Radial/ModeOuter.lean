import CauchyHorizon.Radial.Mode
import CauchyHorizon.Analysis.PowerRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Outer-endpoint expansions from the same radial integral equations. -/

open Set Filter MeasureTheory Asymptotics
open scoped Topology

namespace CauchyHorizon.Background

variable (B : CauchyHorizon.Background)

theorem radialCoefficients_outer_asymptotics :
    B.coefficientX =O[𝓝[>] 0] (fun x => x ^ B.criticalExponent) ∧
    B.coefficientV =O[𝓝[>] 0] (fun x => x ^ (-B.criticalExponent)) ∧
    (fun x => B.criticalWeight (B.event - x)) =O[𝓝[>] 0]
      (fun x => x ^ B.criticalExponent) ∧
    (fun x => B.criticalWeight (B.event - x) - x ^ B.criticalExponent) =O[𝓝[>] 0]
      (fun x => x ^ (B.criticalExponent + 1)) ∧
    (fun x => B.coefficientX x - B.outerRate / B.event * x ^ B.criticalExponent) =O[𝓝[>] 0]
      (fun x => x ^ (B.criticalExponent + 1)) := by
  let g : ℝ → ℝ := fun x => (B.event - x - B.inner) ^ (-1 / 2 : ℝ) *
    Real.exp (B.criticalExponent * B.regularLog (B.event - x))
  let A : ℝ → ℝ := fun x => B.outerRate * g x / (B.event - x)
  let D : ℝ → ℝ := fun x => 1 / (B.outerRate * (B.event - x) * g x)
  have hg : DifferentiableAt ℝ g 0 := by
    have hi : B.event - (0 : ℝ) - B.inner ≠ 0 := by
      simpa only [sub_zero] using (sub_pos.2 B.inner_lt_event).ne'
    have hc : B.cosmologicalRadius - (B.event - (0 : ℝ)) ≠ 0 := by
      simpa only [sub_zero] using (sub_pos.2 B.event_lt_cosmological).ne'
    have hn : B.event - (0 : ℝ) - B.negativeRoot ≠ 0 := by
      simpa only [sub_zero] using (sub_pos.2 (B.negativeRoot_neg.trans B.event_pos)).ne'
    dsimp [g, regularLog]
    fun_prop (disch := assumption)
  have hg0 : g 0 = 1 := by
    have hz := congrArg (fun y => B.criticalExponent * y) B.coordinateLog_event
    dsimp [coordinateLog] at hz
    rw [mul_add, ← mul_assoc, mul_comm B.criticalExponent B.innerExponent,
      B.inner_exponent_critical, mul_zero] at hz
    dsimp [g]
    rw [sub_zero, Real.rpow_def_of_pos (sub_pos.2 B.inner_lt_event), ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    linarith only [hz]
  have hA : DifferentiableAt ℝ A 0 :=
    ((differentiableAt_const B.outerRate).mul hg).div
      ((differentiableAt_const B.event).sub differentiableAt_id)
      (by simpa only [sub_zero] using B.event_pos.ne')
  have hD : DifferentiableAt ℝ D 0 :=
    (differentiableAt_const (1 : ℝ)).div
      (((differentiableAt_const B.outerRate).mul
        ((differentiableAt_const B.event).sub differentiableAt_id)).mul hg)
      (by simpa only [sub_zero, hg0, mul_one] using mul_ne_zero B.outerRate_pos.ne' B.event_pos.ne')
  have hAb : A =O[𝓝[>] 0] (fun _ => (1 : ℝ)) :=
    (hA.continuousAt.tendsto.isBigO_one ℝ).mono inf_le_left
  have hDb : D =O[𝓝[>] 0] (fun _ => (1 : ℝ)) :=
    (hD.continuousAt.tendsto.isBigO_one ℝ).mono inf_le_left
  have hgb : g =O[𝓝[>] 0] (fun _ => (1 : ℝ)) :=
    (hg.continuousAt.tendsto.isBigO_one ℝ).mono inf_le_left
  have hgr : (fun x => g x - 1) =O[𝓝[>] 0] (fun x => x) := by
    have hh : (fun x => g x - g 0) =O[𝓝[>] 0] (fun x : ℝ => x - 0) :=
      hg.isBigO_sub.mono nhdsWithin_le_nhds
    simpa only [hg0, sub_zero] using hh
  have hAr : (fun x => A x - B.outerRate / B.event) =O[𝓝[>] 0] (fun x => x) := by
    have hh : (fun x => A x - A 0) =O[𝓝[>] 0] (fun x : ℝ => x - 0) :=
      hA.isBigO_sub.mono nhdsWithin_le_nhds
    simpa only [A, sub_zero, hg0, mul_one] using hh
  have heq : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      B.criticalWeight (B.event - x) = x ^ B.criticalExponent * g x ∧
      B.coefficientX x = x ^ B.criticalExponent * A x ∧
      B.coefficientV x = x ^ (-B.criticalExponent) * D x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hq : B.criticalWeight (B.event - x) = x ^ B.criticalExponent * g x := by
      dsimp [criticalWeight, g]
      rw [sub_sub_cancel]
      ring
    refine ⟨hq, ?_, ?_⟩
    · dsimp [coefficientX, A]
      rw [hq]
      ring
    · dsimp [coefficientV, D]
      rw [hq, Real.rpow_neg (le_of_lt hx)]
      field_simp
  have hp := isBigO_refl (fun x : ℝ => x ^ B.criticalExponent) (𝓝[>] 0)
  have hn := isBigO_refl (fun x : ℝ => x ^ (-B.criticalExponent)) (𝓝[>] 0)
  have hpow : (fun x : ℝ => x ^ B.criticalExponent * x) =ᶠ[𝓝[>] 0]
      (fun x => x ^ (B.criticalExponent + 1)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.rpow_add hx, Real.rpow_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (hp.mul hAb).congr'
    · exact heq.mono (fun _ h => h.2.1.symm)
    · exact Eventually.of_forall (fun _ => mul_one _)
  · apply (hn.mul hDb).congr'
    · exact heq.mono (fun _ h => h.2.2.symm)
    · exact Eventually.of_forall (fun _ => mul_one _)
  · apply (hp.mul hgb).congr'
    · exact heq.mono (fun _ h => h.1.symm)
    · exact Eventually.of_forall (fun _ => mul_one _)
  · apply (hp.mul hgr).congr' _ hpow
    filter_upwards [heq] with x hx
    rw [hx.1]
    ring
  · apply (hp.mul hAr).congr' _ hpow
    filter_upwards [heq] with x hx
    rw [hx.2.1]
    ring

theorem radialMode_outer_expansions (hb : B.criticalExponent < 1) :
    (fun x => extendCurve B.radialLength_pos.le (B.radialMode hb).2 x -
      B.event * B.criticalExponent) =O[𝓝[>] 0] (fun x => x ^ (2 : ℝ)) ∧
    (fun x => extendCurve B.radialLength_pos.le (B.radialMode hb).1 x -
      B.innerRate / (B.criticalExponent + 1) * x ^ (B.criticalExponent + 1)) =O[𝓝[>] 0]
      (fun x => x ^ (B.criticalExponent + 2)) ∧
    (fun x => B.criticalWeight (B.event - x) *
      extendCurve B.radialLength_pos.le (B.radialMode hb).2 x -
      (B.event * B.criticalExponent) * x ^ B.criticalExponent) =O[𝓝[>] 0]
      (fun x => x ^ (B.criticalExponent + 1)) := by
  let X := extendCurve B.radialLength_pos.le (B.radialMode hb).1
  let V := extendCurve B.radialLength_pos.le (B.radialMode hb).2
  let V₀ := B.event * B.criticalExponent
  have hdom : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 B.radialLength := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds B.radialLength_pos)] with x hx hL
    exact ⟨hx, hL⟩
  have hXint : X =ᶠ[𝓝[>] 0] (fun x => ∫ t in (0 : ℝ)..x, B.coefficientX t * V t) := by
    filter_upwards [hdom] with x hx
    simpa only [X, V, extendCurve, projIcc_of_mem _ ⟨hx.1.le, hx.2.le⟩, zero_add]
      using (B.radialMode_spec hb ⟨x, ⟨hx.1.le, hx.2.le⟩⟩).1
  have hVint : (fun x => V x - V₀) =ᶠ[𝓝[>] 0]
      (fun x => ∫ t in (0 : ℝ)..x, B.coefficientV t * X t) := by
    filter_upwards [hdom] with x hx
    have hh := (B.radialMode_spec hb ⟨x, ⟨hx.1.le, hx.2.le⟩⟩).2
    change (B.radialMode hb).2 _ = V₀ + ∫ t in (0 : ℝ)..x, B.coefficientV t * X t at hh
    simpa only [V, extendCurve, projIcc_of_mem _ ⟨hx.1.le, hx.2.le⟩] using
      (sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hh))
  obtain ⟨hc, hd, hq, hqr, hcr⟩ := B.radialCoefficients_outer_asymptotics
  have hVb : V =O[𝓝[>] 0] (fun _ => (1 : ℝ)) :=
    ((continuous_extendCurve B.radialLength_pos.le (B.radialMode hb).2).continuousAt.tendsto.isBigO_one
      ℝ).mono inf_le_left
  have hXb : X =O[𝓝[>] 0] (fun x => x ^ (B.criticalExponent + 1)) := by
    have hh : (fun x => B.coefficientX x * V x) =O[𝓝[>] 0]
        (fun x => x ^ B.criticalExponent) := by
      simpa only [mul_one] using hc.mul hVb
    exact (integral_isBigO_rpow (by linarith [B.criticalExponent_pos]) hh).congr'
      hXint.symm (Eventually.of_forall (fun _ => rfl))
  have hVr : (fun x => V x - V₀) =O[𝓝[>] 0] (fun x => x ^ (2 : ℝ)) := by
    have hh : (fun x => B.coefficientV x * X x) =O[𝓝[>] 0] (fun x => x ^ (1 : ℝ)) := by
      apply (hd.mul hXb).congr' (Eventually.of_forall (fun _ => rfl))
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
    have hi := integral_isBigO_rpow (by norm_num : (-1 : ℝ) < 1) hh
    norm_num only at hi
    exact hi.congr' hVint.symm (Eventually.of_forall (fun _ => rfl))
  have hVr₁ : (fun x => V x - V₀) =O[𝓝[>] 0] (fun x => x) := by
    apply hVr.trans
    apply IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hx1
    rw [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x),
      Real.norm_eq_abs, abs_of_pos hx, one_mul]
    have h0 : 0 < x := hx
    have h1 : x < 1 := hx1
    nlinarith only [h0, h1]
  have hpow : (fun x : ℝ => x ^ B.criticalExponent * x) =ᶠ[𝓝[>] 0]
      (fun x => x ^ (B.criticalExponent + 1)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.rpow_add hx, Real.rpow_one]
  have hforcing : (fun x => B.coefficientX x * V x - B.innerRate * x ^ B.criticalExponent)
      =O[𝓝[>] 0] (fun x => x ^ (B.criticalExponent + 1)) := by
    have h₁ : (fun x => (B.coefficientX x - B.outerRate / B.event * x ^ B.criticalExponent) * V x)
        =O[𝓝[>] 0] (fun x => x ^ (B.criticalExponent + 1)) := by
      simpa only [mul_one] using hcr.mul hVb
    have h₂ := ((isBigO_refl (fun x : ℝ => x ^ B.criticalExponent) (𝓝[>] 0)).mul hVr₁)
      |>.trans_eventuallyEq hpow |>.const_mul_left (B.outerRate / B.event)
    apply (h₁.add h₂).congr_left
    intro x
    dsimp [V₀, criticalExponent]
    field_simp [B.event_pos.ne', B.outerRate_pos.ne']
    ring
  have hXr : (fun x => X x - B.innerRate / (B.criticalExponent + 1) *
      x ^ (B.criticalExponent + 1)) =O[𝓝[>] 0] (fun x => x ^ (B.criticalExponent + 2)) := by
    have hh := integral_isBigO_rpow (by linarith [B.criticalExponent_pos]) hforcing
    apply hh.congr'
    · filter_upwards [hdom, hXint] with x hx hXi
      have hcint := ((B.coefficients_integrable hb).1.mul_continuousOn
        (continuous_extendCurve B.radialLength_pos.le (B.radialMode hb).2).continuousOn).mono_set
        (by rw [uIcc_of_le hx.1.le, uIcc_of_le B.radialLength_pos.le]
            exact Icc_subset_Icc le_rfl hx.2.le)
      have hpint := (intervalIntegral.intervalIntegrable_rpow'
        (a := (0 : ℝ)) (b := x) (by linarith [B.criticalExponent_pos] : -1 < B.criticalExponent))
        |>.const_mul B.innerRate
      rw [intervalIntegral.integral_sub hcint hpint, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith [B.criticalExponent_pos] : -1 < B.criticalExponent)),
        Real.zero_rpow (by linarith [B.criticalExponent_pos] : B.criticalExponent + 1 ≠ 0),
        sub_zero, ← hXi]
      ring
    · exact Eventually.of_forall (fun x => by rw [show B.criticalExponent + 1 + 1 =
        B.criticalExponent + 2 by ring])
  refine ⟨hVr, hXr, ?_⟩
  have h₁ := (hq.mul hVr₁).trans_eventuallyEq hpow
  have h₂ := hqr.const_mul_left V₀
  apply (h₁.add h₂).congr_left
  intro x
  dsimp [V₀, V]
  ring

end CauchyHorizon.Background
