import CauchyHorizon.Radial.Coordinate
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! The critical power has one integrable singularity; its reciprocal has the other. -/

open Set MeasureTheory Filter
open scoped Topology

namespace CauchyHorizon.Background

variable (B : CauchyHorizon.Background)

noncomputable def criticalExponent : ℝ := B.innerRate / B.outerRate

theorem criticalExponent_pos : 0 < B.criticalExponent :=
  div_pos B.innerRate_pos B.outerRate_pos

theorem inner_exponent_critical : B.innerExponent * B.criticalExponent = -1 / 2 := by
  rw [B.inner_exponent_eq, criticalExponent]
  have ha := B.outerRate_pos.ne'
  have hk := B.innerRate_pos.ne'
  field_simp

noncomputable def criticalWeight (r : ℝ) : ℝ :=
  (B.event - r) ^ B.criticalExponent * (r - B.inner) ^ (-1 / 2 : ℝ) *
    Real.exp (B.criticalExponent * B.regularLog r)

theorem criticalWeight_eq_z_rpow {r : ℝ} (hr : r ∈ Ioo B.inner B.event) :
    B.criticalWeight r = B.z r ^ B.criticalExponent := by
  rw [B.z_power_form hr.1]
  rw [Real.mul_rpow (mul_nonneg (sub_nonneg.2 hr.2.le)
    (Real.rpow_pos_of_pos (sub_pos.2 hr.1) _).le) (Real.exp_pos _).le,
    Real.mul_rpow (sub_nonneg.2 hr.2.le) (Real.rpow_pos_of_pos (sub_pos.2 hr.1) _).le,
    ← Real.rpow_mul (sub_nonneg.2 hr.1.le), B.inner_exponent_critical, ← Real.exp_mul]
  unfold criticalWeight
  rw [mul_comm (B.regularLog r) B.criticalExponent]

theorem criticalWeight_nonneg {r : ℝ} (hr : r ∈ Icc B.inner B.event) :
    0 ≤ B.criticalWeight r :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (sub_nonneg.2 hr.2) _)
    (Real.rpow_nonneg (sub_nonneg.2 hr.1) _)) (Real.exp_pos _).le

theorem criticalWeight_pos {r : ℝ} (hr : r ∈ Ioo B.inner B.event) :
    0 < B.criticalWeight r :=
  mul_pos (mul_pos (Real.rpow_pos_of_pos (sub_pos.2 hr.2) _)
    (Real.rpow_pos_of_pos (sub_pos.2 hr.1) _)) (Real.exp_pos _)

theorem criticalWeight_continuousOn : ContinuousOn B.criticalWeight (Ioo B.inner B.event) := by
  apply ((continuousOn_const.sub continuousOn_id).rpow_const
    (fun r hr => Or.inl (sub_pos.2 hr.2).ne')).mul
    ((continuousOn_id.sub continuousOn_const).rpow_const
      (fun r hr => Or.inl (sub_pos.2 hr.1).ne')) |>.mul
    (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (B.regularLog_continuousOn.mono Ioo_subset_Icc_self)))

theorem criticalWeight_integrable : IntervalIntegrable B.criticalWeight volume B.inner B.event := by
  have hi : IntervalIntegrable (fun r => (r - B.inner) ^ (-1 / 2 : ℝ)) volume B.inner B.event := by
    simpa using (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ))
      (b := B.event - B.inner) (by norm_num : (-1 : ℝ) < -1 / 2)).comp_sub_right B.inner
  have ho : ContinuousOn (fun r => (B.event - r) ^ B.criticalExponent) (uIcc B.inner B.event) :=
    (continuousOn_const.sub continuousOn_id).rpow_const (fun _ _ => Or.inr B.criticalExponent_pos.le)
  have he : ContinuousOn (fun r => Real.exp (B.criticalExponent * B.regularLog r)) (uIcc B.inner B.event) := by
    rw [uIcc_of_le B.inner_lt_event.le]
    exact Real.continuous_exp.comp_continuousOn (continuousOn_const.mul B.regularLog_continuousOn)
  exact (hi.continuousOn_mul ho).mul_continuousOn he

theorem criticalWeight_inv {r : ℝ} (hr : r ∈ Icc B.inner B.event) :
    (B.criticalWeight r)⁻¹ = (B.event - r) ^ (-B.criticalExponent) *
      (r - B.inner) ^ (1 / 2 : ℝ) * Real.exp (-B.criticalExponent * B.regularLog r) := by
  unfold criticalWeight
  simp only [mul_inv_rev, ← Real.rpow_neg (sub_nonneg.2 hr.2),
    ← Real.rpow_neg (sub_nonneg.2 hr.1), ← Real.exp_neg]
  norm_num
  ring

theorem criticalWeight_inv_integrable (hb : B.criticalExponent < 1) :
    IntervalIntegrable (fun r => (B.criticalWeight r)⁻¹) volume B.inner B.event := by
  have ho : IntervalIntegrable (fun r => (B.event - r) ^ (-B.criticalExponent)) volume B.inner B.event := by
    simpa using ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ))
      (b := B.event - B.inner) (by linarith : (-1 : ℝ) < -B.criticalExponent)).comp_sub_left B.event).symm
  have hi : ContinuousOn (fun r => (r - B.inner) ^ (1 / 2 : ℝ)) (uIcc B.inner B.event) :=
    (continuousOn_id.sub continuousOn_const).rpow_const (fun _ _ => Or.inr (by norm_num))
  have he : ContinuousOn (fun r => Real.exp (-B.criticalExponent * B.regularLog r)) (uIcc B.inner B.event) := by
    rw [uIcc_of_le B.inner_lt_event.le]
    exact Real.continuous_exp.comp_continuousOn (continuousOn_const.mul B.regularLog_continuousOn)
  apply ((ho.mul_continuousOn hi).mul_continuousOn he).congr
  intro r hr
  exact (B.criticalWeight_inv (by
    rw [uIoc_of_le B.inner_lt_event.le] at hr
    exact ⟨hr.1.le, hr.2⟩)).symm

theorem criticalWeight_outer_normalization :
    Tendsto (fun r => B.criticalWeight r / (B.event - r) ^ B.criticalExponent)
      (𝓝[<] B.event) (𝓝 1) := by
  have hlim : Tendsto (fun r => (B.z r / (B.event - r)) ^ B.criticalExponent)
      (𝓝[<] B.event) (𝓝 1) := by
    simpa only [Function.comp_def, Real.one_rpow] using Filter.Tendsto.comp
      (Real.continuousAt_rpow_const 1 B.criticalExponent (Or.inl one_ne_zero)) B.z_outer_normalization
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds B.inner_lt_event)] with r hr hi
  have hmem : r ∈ Ioo B.inner B.event := ⟨hi, hr⟩
  rw [Real.div_rpow (B.z_pos hmem).le (sub_pos.2 hr).le, ← B.criticalWeight_eq_z_rpow hmem]

theorem criticalWeight_inner_normalization :
    Tendsto (fun r => B.criticalWeight r / (r - B.inner) ^ (-1 / 2 : ℝ)) (𝓝[>] B.inner)
      (𝓝 ((B.event - B.inner) ^ B.criticalExponent *
        Real.exp (B.criticalExponent * B.regularLog B.inner))) := by
  have hc := B.regularLog_continuousAt (B.negativeRoot_neg.trans B.inner_pos)
    (B.inner_lt_event.trans B.event_lt_cosmological)
  have hp : ContinuousAt (fun r => (B.event - r) ^ B.criticalExponent) B.inner :=
    (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (sub_pos.2 B.inner_lt_event).ne')
  have hlim : Tendsto (fun r => (B.event - r) ^ B.criticalExponent *
      Real.exp (B.criticalExponent * B.regularLog r)) (𝓝[>] B.inner)
      (𝓝 ((B.event - B.inner) ^ B.criticalExponent *
        Real.exp (B.criticalExponent * B.regularLog B.inner))) :=
    (hp.mul (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hc))).mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  unfold criticalWeight
  have hpow := (Real.rpow_pos_of_pos (sub_pos.2 hr) (-1 / 2 : ℝ)).ne'
  rw [mul_right_comm, mul_div_cancel_right₀ _ hpow]

theorem criticalWeight_inner_coefficient_pos :
    0 < (B.event - B.inner) ^ B.criticalExponent * Real.exp (B.criticalExponent * B.regularLog B.inner) :=
  mul_pos (Real.rpow_pos_of_pos (sub_pos.2 B.inner_lt_event) _) (Real.exp_pos _)

end CauchyHorizon.Background
