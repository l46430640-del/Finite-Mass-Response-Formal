import CauchyHorizon.Characteristic.HorizonData

/-! One translated tail and terminal radius supply all outgoing premises of the mass theorem. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

structure AdmissibleOutgoingData (B : Background) (s l : ℝ) where
  tail : ℝ → ℝ
  radius : ℝ → ℝ
  upper : ℝ
  lower : ℝ
  deviation : ℝ
  rate_pos : 0 < s
  upper_nonneg : 0 ≤ upper
  lower_pos : 0 < lower
  deviation_nonneg : 0 ≤ deviation
  deviation_lt : deviation < B.event
  tail_continuous : Continuous tail
  tail_bound : ∀ v, ‖tail v‖ ≤ upper * Real.exp (-s * v)
  tail_lower : ∀ v ∈ Ici (0 : ℝ), lower * Real.exp (-l * v) ≤ tail v
  radius_continuous : Continuous radius
  radius_lower : ∀ v, B.event - deviation ≤ radius v
  radius_initial : B.inner < radius 0
  radius_derivative : ∀ v ∈ Ici (0 : ℝ), HasDerivWithinAt radius
    (horizonFunction (radius v) (horizonMass B.mass tail v) B.charge B.cosmological) (Ici 0) v
  radius_decay : ∀ v ∈ Ici (0 : ℝ), ‖radius v - B.event‖ ≤ deviation * Real.exp (-(2 * s) * v)

theorem horizonMass_translate (M : ℝ) (h : ℝ → ℝ) (S t : ℝ) :
    horizonMass M (fun w => h (w + S)) t = horizonMass M h (t + S) := by
  have he (w : ℝ) : (Ioi t).indicator (fun w => h (w + S) ^ 2) w =
      (Ioi (t + S)).indicator (fun w => h w ^ 2) (w + S) := by
    simp only [indicator, mem_Ioi, add_lt_add_iff_right]
  unfold horizonMass
  congr 1
  rw [← integral_indicator measurableSet_Ioi]
  simp_rw [he]
  rw [integral_add_right_eq_self, integral_indicator measurableSet_Ioi]

namespace Background

theorem exists_admissible_late_data (B : Background) {s l H Hlo : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hHlo : 0 < Hlo) {h : ℝ → ℝ}
    (hc : ContinuousOn h (Ici 0))
    (hb : ∀ v ∈ Ici (0 : ℝ), ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ D : AdmissibleOutgoingData B s l,
      (∀ v ∈ Ici (0 : ℝ), D.tail v = h (v + T)) ∧
      D.upper = H * Real.exp (-s * T) ∧ D.lower = Hlo * Real.exp (-l * T) := by
  obtain ⟨T₀, δ, hT₀, hδ, _hδR, g, r, _hgc, hgeq, hrc, _hrb, hrd, hrdec, _hrend, _hOut⟩ :=
    B.exists_late_outgoing_data hs hH hc hb
      (fun v hv => (mul_pos hHlo (Real.exp_pos _)).trans_le (hlo v hv))
  have hδlim : Tendsto (fun S : ℝ => δ * Real.exp (-(2 * s) * S)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith only [hs] : -(2 * s) < 0))).const_mul δ
  obtain ⟨S, hS, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hδlim.eventually (Iio_mem_nhds (sub_pos.2 B.inner_lt_event)))).exists
  let T := T₀ + S
  let d := δ * Real.exp (-(2 * s) * S)
  let h' := fun v => futureExtension h (v + T)
  let r' := futureExtension (fun v => r (v + S))
  have hd : 0 < d := mul_pos hδ (Real.exp_pos _)
  have hdR : d < B.event := by have := B.inner_pos; dsimp only [d] at *; linarith only [hsmall, this]
  have hT : 0 ≤ T := add_nonneg hT₀ hS
  have heq (v : ℝ) (hv : 0 ≤ v) : h' v = h (v + T) := futureExtension_eq (add_nonneg hv hT)
  have hr'eq (v : ℝ) (hv : 0 ≤ v) : r' v = r (v + S) := futureExtension_eq hv
  have hbound (v : ℝ) : ‖h' v‖ ≤ (H * Real.exp (-s * T)) * Real.exp (-s * v) := by
    apply (futureExtension_exponential_bound hs hH hb (v + T)).trans_eq
    rw [show -s * (v + T) = -s * T + -s * v by ring, Real.exp_add]
    ring
  have hlower (v : ℝ) (hv : v ∈ Ici (0 : ℝ)) :
      (Hlo * Real.exp (-l * T)) * Real.exp (-l * v) ≤ h' v := by
    rw [heq v hv]
    convert hlo (v + T) (add_nonneg hv hT) using 1
    rw [show -l * (v + T) = -l * T + -l * v by ring, Real.exp_add]
    ring
  have hdec (v : ℝ) (hv : v ∈ Ici (0 : ℝ)) : ‖r' v - B.event‖ ≤ d * Real.exp (-(2 * s) * v) := by
    rw [hr'eq v hv]
    apply (hrdec (v + S) (add_nonneg hv hS)).trans_eq
    rw [show -(2 * s) * (v + S) = -(2 * s) * S + -(2 * s) * v by ring, Real.exp_add]
    ring
  have hrlo (v : ℝ) : B.event - d ≤ r' v := by
    have hh := hdec (max v 0) (le_max_right v (0 : ℝ))
    have hle : Real.exp (-(2 * s) * max v 0) ≤ 1 := Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) (le_max_right _ _))
    have he : r' (max v 0) = r' v := by simp [r', futureExtension]
    rw [he, Real.norm_eq_abs] at hh
    have ha := (abs_le.1 (hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hle hd.le))).1
    linarith only [ha]
  have hinit : B.inner < r' 0 := by have := hrlo 0; change d < B.event - B.inner at hsmall; linarith
  have hmass (v : ℝ) (hv : 0 ≤ v) : horizonMass B.mass h' v = horizonMass B.mass g (v + S) := by
    rw [← horizonMass_translate]
    apply horizonMass_congr_future (fun w hw => ?_) hv B.mass
    rw [heq w hw, hgeq (w + S) (add_nonneg hw hS)]
    congr 1
    dsimp only [T]
    ring
  have hdr (v : ℝ) (hv : v ∈ Ici (0 : ℝ)) : HasDerivWithinAt r'
      (horizonFunction (r' v) (horizonMass B.mass h' v) B.charge B.cosmological) (Ici 0) v := by
    rw [hr'eq v hv, hmass v hv]
    have hh := (hrd (v + S) (add_nonneg hv hS)).comp v
      ((hasDerivWithinAt_id v (Ici 0)).add_const S) (fun w hw => add_nonneg hw hS)
    simp only [mul_one] at hh
    exact hh.congr (fun w hw => hr'eq w hw) (hr'eq v hv)
  refine ⟨T, hT, {
    tail := h', radius := r', upper := H * Real.exp (-s * T), lower := Hlo * Real.exp (-l * T),
    deviation := d, rate_pos := hs, upper_nonneg := by positivity,
    lower_pos := mul_pos hHlo (Real.exp_pos _), deviation_nonneg := hd.le, deviation_lt := hdR,
    tail_continuous := (futureExtension_continuous hc).comp (continuous_id.add continuous_const),
    tail_bound := hbound, tail_lower := hlower,
    radius_continuous := futureExtension_continuous (hrc.comp (continuous_id.add continuous_const)).continuousOn,
    radius_lower := hrlo, radius_initial := hinit, radius_derivative := hdr, radius_decay := hdec },
    heq, rfl, rfl⟩

end Background
end CauchyHorizon
