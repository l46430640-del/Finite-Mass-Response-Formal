import CauchyHorizon.Characteristic.HorizonBounds
import CauchyHorizon.Characteristic.OuterClosure
import CauchyHorizon.Characteristic.OuterConstraint
import CauchyHorizon.Characteristic.MassFlux

/-! A uniform late mass lower bound from one finite outer slice and monotonicity. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_late_mass_lower (B : Background) {s H dH A ε : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hε : 0 < ε)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ T : ℝ, 0 < U₀ ∧ U₀ ≤ r 0 / 4 ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ U₀ →
        ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
          let N := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          B.mass - ε ≤ massField B.charge B.cosmological x.1 x.2.1 N hx.choose u v := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let ρ := (B.event - dH) / 2
  let R := B.event + dH
  have hρ : 0 < ρ := half_pos (sub_pos.2 hdHR)
  have hR : 0 < R := add_pos_of_pos_of_nonneg B.event_pos hdH
  obtain ⟨W, hW, hrlam⟩ := B.horizon_radius_lambda_bounds hs hH hdH hdHR hb hrdec
  have haxis (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : r t ∈ Icc (2 * ρ) R := by
    have hh := (hrlam t ht).1
    exact ⟨by dsimp only [ρ]; linarith only [hh.1], hh.2⟩
  have hlout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      |horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological| ≤ W :=
    (hrlam t ht).2.trans (mul_le_of_le_one_right hW (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) ht)))
  have hout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : Real.exp (0 * t) * |h t| ≤ H := by
    simp only [zero_mul, Real.exp_zero, one_mul]
    have hh : |h t| ≤ H * Real.exp (-s * t) := by simpa only [Real.norm_eq_abs] using hb t
    exact hh.trans
      (mul_le_of_le_one_right hH (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hs.le) ht)))
  obtain ⟨nH, NH, hnH, _hnH1, hNH, hνaxis⟩ := hOut.nu_bounds hs hc hi hrc hr0
  obtain ⟨δ₀, L, hδ₀, _hδ₀1, hδ₀r, hL, hgeom⟩ := exists_horizon_outer_bounds
    hc hi hrc hr0 hφ hrd ha le_rfl ha hρ hnH (zero_lt_one.trans_le hNH) hH hW hA haxis hνaxis hout hlout
  let n := (9 / 16) * nH
  let N := (5 / 3) * NH
  have hn : 0 < n := by dsimp only [n]; positivity
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  let E₀ := 2 * (H + L * (r 0 / ρ) * A) / ρ
  let C := (2 * R / n) * (r 0 / ρ) ^ 2 * A ^ 2
  let D := (2 * R / n) * (N / (ρ * a) * E₀) ^ 2
  let η := Real.log (1 + ε / (R * L + 1))
  have hden : 0 < R * L + 1 := by positivity
  have hη : 0 < η := Real.log_pos (by linarith only [div_pos hε hden])
  obtain ⟨δ, hδ, hδ1, hδδ, _hgap, hsmall, herror⟩ := exists_small_outer_width
    (by positivity : 0 < 4 * δ₀) zero_lt_one hη 0 (L * N / (ρ ^ 2 * a)) C D
  have hδbase : δ ≤ δ₀ := by linarith only [hδδ]
  have hsmall' : L * N * δ / (ρ ^ 2 * (a - 0)) ≤ 1 / 2 := by
    simpa only [div_mul_eq_mul_div, sub_zero] using hsmall
  have hmasserror : (R * L / 2) * (Real.exp η - 1) ≤ ε / 2 := by
    have hpos : 0 < 1 + ε / (R * L + 1) := by positivity
    rw [show Real.exp η = 1 + ε / (R * L + 1) from Real.exp_log hpos]
    have hh : R * L * ε / (R * L + 1) ≤ ε := by
      apply (div_le_iff₀ hden).2
      nlinarith only [hε]
    calc
      _ = (R * L * ε / (R * L + 1)) / 2 := by ring
      _ ≤ ε / 2 := div_le_div_of_nonneg_right hh (by norm_num)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((horizonMass_tendsto hs hH hb B.mass).eventually_const_lt
    (by linarith only [hε] : B.mass - ε / 2 < B.mass))
  let T := max 0 T₀
  have hT : 0 ≤ T := le_max_left _ _
  have hHmass : B.mass - ε / 2 ≤ horizonMass B.mass h T := (hT₀ T (le_max_right _ _)).le
  let U₀ := δ / Real.exp (a * T)
  have hU₀ : 0 < U₀ := div_pos hδ (Real.exp_pos _)
  have hU₀δ : U₀ ≤ δ := div_le_self hδ.le (Real.one_le_exp_iff.2 (mul_nonneg ha.le hT))
  refine ⟨U₀, T, hU₀, hU₀δ.trans (hδbase.trans hδ₀r), hT, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hUU u v hTv
  have hTV : T ≤ V := hTv.trans v.property.2
  let y := waveTranslate (a := 0) (U := U) (b := 0) (V := T) le_rfl (by simp)
    le_rfl (by linarith only [hTV]) x
  have hy : IsWaveIntegral hU hT B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
      (incomingWaveVelocity hUR hp hf) y :=
    hx.horizon_prefix hU hV hUR hU hT le_rfl hTV hc hi hrc hr0 hp hf
  let νy := radialNuField hT B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) y.1 hy.choose
  let νx := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hwidth : U * Real.exp (a * T) ≤ δ := by
    calc
      _ ≤ U₀ * Real.exp (a * T) := mul_le_mul_of_nonneg_right hUU (Real.exp_pos _).le
      _ = δ := div_mul_cancel₀ δ (Real.exp_ne_zero _)
  have hcb : 0 ≤ a * (1 - 1 / p.toReal) :=
    mul_nonneg ha.le (by linarith only [(incoming_exponent_bounds hp).1])
  have hg := hgeom U T hU hT hUR p hp f hf y hy hfn hcb (hwidth.trans hδbase)
  have hlo (q : Icc 0 U) (w : Icc 0 T) : ρ ≤ y.1 q w 0 := by linarith only [(hg q w).1, hρ]
  have hnhi (q : Icc 0 U) (w : Icc 0 T) : |νy q w| ≤ N * Real.exp (a * w) := by
    rw [abs_of_neg (hy.interior_gauge hU hT hUR hc hi hrc hr0 hφ hrd hp hf q w).2.2.1]
    exact (hg q w).2.2.2.2
  let w : Icc 0 T := ⟨T, hT, le_rfl⟩
  have hfb := hy.horizon_outer_feedback hU hT hUR hc hi hrc hr0 hφ hrd hp hf hA hfn
    le_rfl ha hcb hρ hR.le hn hN hL hH hδ.le hlo (fun q w => (hg q w).2.1)
    (fun q w => (hg q w).2.2.2.1) hnhi (fun q w => (hg q w).2.2.1)
    (fun w => hout w w.property.1) hwidth hsmall' u w
  have hw : (u : ℝ) * Real.exp (a * w) ≤ δ :=
    (mul_le_mul_of_nonneg_right u.property.2 (Real.exp_pos _).le).trans hwidth
  have he := outer_constraint_envelope hp ha.le le_rfl ha hρ hR.le hrp.le hn hN hL hH hA
    hδ.le hδ1 u.property.1 w.property.1 hw
  have he' := Real.exp_le_exp.2 (he.trans (by simpa only [C, D, E₀, sub_zero] using herror))
  have hmass : |massField B.charge B.cosmological y.1 y.2.1 νy hy.choose u w - horizonMass B.mass h T| ≤ ε / 2 :=
    hfb.2.2.trans ((mul_le_mul_of_nonneg_left (sub_le_sub_right he' 1) (by positivity)).trans hmasserror)
  have hye (q : Icc 0 U) (t : Icc 0 T) : y.1 q t = x.1 q ⟨t, t.property.1, t.property.2.trans hTV⟩ := by
    change x.1 (intervalTranslate (a := 0) (U := U) le_rfl (by simp) q)
      (intervalTranslate (a := 0) (U := T) le_rfl (by linarith only [hTV]) t) = _
    rw [intervalTranslate_zero]
    congr 1
    exact Subtype.ext (zero_add _)
  have hwe (q : Icc 0 U) (t : Icc 0 T) : y.2.1 q t = x.2.1 q ⟨t, t.property.1, t.property.2.trans hTV⟩ := by
    change x.2.1 (intervalTranslate (a := 0) (U := U) le_rfl (by simp) q)
      (intervalTranslate (a := 0) (U := T) le_rfl (by linarith only [hTV]) t) = _
    rw [intervalTranslate_zero]
    congr 1
    exact Subtype.ext (zero_add _)
  have hne := radialNuField_prefix_eq hT hV hTV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 y.1 hx.choose hy.choose hye u w
  change νy u w = νx u ⟨T, hT, hTV⟩ at hne
  have hme : massField B.charge B.cosmological y.1 y.2.1 νy hy.choose u w =
      massField B.charge B.cosmological x.1 x.2.1 νx hx.choose u ⟨T, hT, hTV⟩ := by
    simp only [massField_apply, hye, hwe, hne]
    rfl
  rw [hme] at hmass
  have hm0 : B.mass - ε ≤ massField B.charge B.cosmological x.1 x.2.1 νx hx.choose u ⟨T, hT, hTV⟩ := by
    linarith only [(abs_le.1 hmass).1, hHmass]
  exact hm0.trans (hx.mass_monotone hU hV hUR hc hi hrc hr0 hφ hrd hp hf u hTv)

end CauchyHorizon.Background
