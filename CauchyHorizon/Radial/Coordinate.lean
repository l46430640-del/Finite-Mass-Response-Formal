import CauchyHorizon.Radial.PartialFractions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! An explicit positive solution of z'/z = a/F, normalized at the event horizon. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon.Background

variable (B : CauchyHorizon.Background)

noncomputable def regularLog (r : ℝ) : ℝ :=
  -B.innerExponent * Real.log (B.event - B.inner) +
    B.cosmologicalExponent * (Real.log (B.cosmologicalRadius - r) -
      Real.log (B.cosmologicalRadius - B.event)) +
    B.negativeExponent * (Real.log (r - B.negativeRoot) - Real.log (B.event - B.negativeRoot))

noncomputable def coordinateLog (r : ℝ) : ℝ :=
  B.innerExponent * Real.log (r - B.inner) + B.regularLog r

noncomputable def z (r : ℝ) : ℝ := (B.event - r) * Real.exp (B.coordinateLog r)

theorem regularLog_continuousAt {r : ℝ} (hn : B.negativeRoot < r) (hc : r < B.cosmologicalRadius) :
    ContinuousAt B.regularLog r := by
  unfold regularLog
  have hc₀ := (sub_pos.2 hc).ne'
  have hn₀ := (sub_pos.2 hn).ne'
  fun_prop (disch := assumption)

theorem regularLog_continuousOn : ContinuousOn B.regularLog (Icc B.inner B.event) := by
  intro r hr
  exact (B.regularLog_continuousAt (B.negativeRoot_neg.trans_le (B.inner_pos.le.trans hr.1))
    (hr.2.trans_lt B.event_lt_cosmological)).continuousWithinAt

theorem coordinateLog_hasDerivAt {r : ℝ} (hr : r ∈ Ioo B.inner B.event) :
    HasDerivAt B.coordinateLog (B.innerExponent / (r - B.inner) +
      B.cosmologicalExponent / (r - B.cosmologicalRadius) + B.negativeExponent / (r - B.negativeRoot)) r := by
  have hi := (sub_pos.2 hr.1).ne'
  have hc := (sub_pos.2 (hr.2.trans B.event_lt_cosmological)).ne'
  have hc₀ := sub_ne_zero.2 (hr.2.trans B.event_lt_cosmological).ne
  have hn := (sub_pos.2 (B.negativeRoot_neg.trans (B.inner_pos.trans hr.1))).ne'
  have hd := (((hasDerivAt_id r).sub_const B.inner).log hi).const_mul B.innerExponent
  have hc' := ((((hasDerivAt_id r).const_sub B.cosmologicalRadius).log hc).sub_const
    (Real.log (B.cosmologicalRadius - B.event))).const_mul B.cosmologicalExponent
  have hn' := ((((hasDerivAt_id r).sub_const B.negativeRoot).log hn).sub_const
    (Real.log (B.event - B.negativeRoot))).const_mul B.negativeExponent
  apply (hd.add (((hasDerivAt_const r (-B.innerExponent * Real.log (B.event - B.inner))).add hc').add hn')).congr_deriv
  dsimp
  field_simp
  ring

theorem z_pos {r : ℝ} (hr : r ∈ Ioo B.inner B.event) : 0 < B.z r :=
  mul_pos (sub_pos.2 hr.2) (Real.exp_pos _)

theorem z_hasDerivAt {r : ℝ} (hr : r ∈ Ioo B.inner B.event) :
    HasDerivAt B.z ((B.outerRate / B.F r) * B.z r) r := by
  have h := ((hasDerivAt_id r).const_sub B.event).mul (B.coordinateLog_hasDerivAt hr).exp
  apply h.congr_deriv
  rw [B.logarithmic_partial_fractions hr]
  dsimp [z]
  have hne := sub_ne_zero.2 hr.2.ne
  field_simp
  ring

theorem z_logarithmic_derivative {r : ℝ} (hr : r ∈ Ioo B.inner B.event) :
    deriv B.z r / B.z r = B.outerRate / B.F r := by
  rw [(B.z_hasDerivAt hr).deriv, mul_div_cancel_right₀ _ (B.z_pos hr).ne']

theorem z_power_form {r : ℝ} (hr : B.inner < r) :
    B.z r = (B.event - r) * (r - B.inner) ^ B.innerExponent * Real.exp (B.regularLog r) := by
  rw [z, coordinateLog, Real.exp_add, Real.rpow_def_of_pos (sub_pos.2 hr)]
  rw [mul_comm (Real.log _) B.innerExponent]
  ring

theorem coordinateLog_event : B.coordinateLog B.event = 0 := by
  simp [coordinateLog, regularLog]

theorem z_outer_normalization :
    Tendsto (fun r => B.z r / (B.event - r)) (𝓝[<] B.event) (𝓝 1) := by
  have hc : ContinuousAt B.coordinateLog B.event := by
    unfold coordinateLog regularLog
    have hi := (sub_pos.2 B.inner_lt_event).ne'
    have hc := (sub_pos.2 B.event_lt_cosmological).ne'
    have hn := (sub_pos.2 (B.negativeRoot_neg.trans B.event_pos)).ne'
    fun_prop (disch := assumption)
  have hlim : Tendsto (fun r => Real.exp (B.coordinateLog r)) (𝓝[<] B.event)
      (𝓝 (Real.exp (B.coordinateLog B.event))) :=
    (Real.continuous_exp.continuousAt.comp hc).mono_left inf_le_left
  rw [B.coordinateLog_event, Real.exp_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.2 hr.ne')).symm

theorem z_inner_normalization :
    Tendsto (fun r => B.z r / (r - B.inner) ^ B.innerExponent) (𝓝[>] B.inner)
      (𝓝 ((B.event - B.inner) * Real.exp (B.regularLog B.inner))) := by
  have hc := B.regularLog_continuousAt (B.negativeRoot_neg.trans B.inner_pos)
    (B.inner_lt_event.trans B.event_lt_cosmological)
  have hlim : Tendsto (fun r => (B.event - r) * Real.exp (B.regularLog r)) (𝓝[>] B.inner)
      (𝓝 ((B.event - B.inner) * Real.exp (B.regularLog B.inner))) :=
    ((continuousAt_const.sub continuousAt_id).mul
      (Real.continuous_exp.continuousAt.comp hc)).mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [B.z_power_form hr]
  have hpow := (Real.rpow_pos_of_pos (sub_pos.2 hr) B.innerExponent).ne'
  field_simp

end CauchyHorizon.Background
