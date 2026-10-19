import CauchyHorizon.Characteristic.OuterNormalization
import CauchyHorizon.Characteristic.HorizonBounds
import CauchyHorizon.Characteristic.PhysicalOverlapNu
import CauchyHorizon.Radial.Normalization

/-! Actual background normalization on arbitrarily small, fixed outer sections. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1000000 in
theorem exists_outer_section_normalization (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∀ cap ε : ℝ, 0 < cap → 0 < ε → ∃ δ T : ℝ,
      0 < δ ∧ δ < cap ∧ 0 ≤ T ∧ 2 * cν * δ < B.event - B.inner ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
          δ / 2 ≤ (u : ℝ) * Real.exp (B.outerRate * v) →
          (u : ℝ) * Real.exp (B.outerRate * v) ≤ δ →
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          B.event - x.1 u v 0 ∈ Ioo (cν * δ / 4) (2 * cν * δ) ∧
            |(u : ℝ) * ν u v / B.F (x.1 u v 0) - 1 / B.outerRate| < ε ∧
            |B.z (x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (B.outerRate * v))) - 1| < ε := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  let a := B.outerRate
  let cν := Real.exp (∫ t in Ioi 0,
    2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - a)
  let S := fun t => -horizonNu
    (fun w => horizonK (r w) (horizonMass B.mass h w) B.charge B.cosmological) t
  have ha : 0 < a := B.outerRate_pos
  have hcν : 0 < cν := Real.exp_pos _
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let ρ := (B.event - dH) / 2
  have hρ : 0 < ρ := half_pos (sub_pos.2 hdHR)
  obtain ⟨W, hW, hrlam⟩ := B.horizon_radius_lambda_bounds hs hH hdH hdHR hb hrdec
  have haxis (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : r t ∈ Icc (2 * ρ) (B.event + dH) := by
    have hh := (hrlam t ht).1
    exact ⟨by dsimp only [ρ]; linarith only [hh.1], hh.2⟩
  have hlout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      |horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological| ≤ W :=
    (hrlam t ht).2.trans (mul_le_of_le_one_right hW (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) ht)))
  have hout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : Real.exp (0 * t) * |h t| ≤ H := by
    simp only [zero_mul, Real.exp_zero, one_mul]
    exact (hb t).trans (mul_le_of_le_one_right hH (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hs.le) ht)))
  obtain ⟨nH, NH, hnH, _, hNH, hνaxis⟩ := hOut.nu_bounds hs hc hi hrc hr0
  obtain ⟨δ₀, C, hδ₀, _, hC, houter⟩ := exists_horizon_outer_normalization
    hc hi hrc hr0 hφ hrd ha le_rfl ha hρ hnH (zero_lt_one.trans_le hNH) hH hW hA haxis hνaxis hout hlout
  dsimp only
  intro cap ε hcap hε
  obtain ⟨η, hη, hη1, hηr, hconvert⟩ := B.exists_outer_normalization_tolerance hε
  let L := fun d : ℝ => (1 + C * d) * Real.exp (C * d) - Real.exp (-(C * d))
  have hLc : Continuous L := by dsimp only [L]; fun_prop
  have hL0 : L 0 = 0 := by simp only [L, mul_zero, add_zero, neg_zero, Real.exp_zero, mul_one, sub_self]
  have hLsmall : ∀ᶠ d in 𝓝 (0 : ℝ), L d < η / 4 :=
    hLc.continuousAt.tendsto.eventually_lt_const (by rw [hL0]; positivity)
  have hsize : ∀ᶠ d : ℝ in 𝓝 0, cν * d < η / 4 :=
    (continuous_id.const_mul cν).continuousAt.tendsto.eventually_lt_const
      (by simpa only [id_eq, mul_zero] using div_pos hη (by norm_num : (0 : ℝ) < 4))
  obtain ⟨δ, hδ, hsmall⟩ := (hLsmall.and (hsize.and
    ((eventually_lt_nhds hδ₀).and (eventually_lt_nhds hcap)))).exists_gt
  have hδr : 2 * cν * δ < B.event - B.inner := by nlinarith only [hsmall.2.1, hηr, hη]
  let Q := fun t : ℝ => δ * Real.exp (-a * t)
  let e := fun t => C * (Q t ^ (1 / 2 : ℝ) + δ)
  let E := fun t => (1 + C * δ) * Real.exp (e t) - (1 - Q t / r 0) * Real.exp (-e t)
  let ηH := fun t => |S t / (cν * Real.exp (a * t)) - 1|
  let G := fun t => (2 * dH / (δ * cν)) * Real.exp (-(2 * s) * t)
  let F := fun t => E t * (1 + ηH t) + ηH t + G t
  have hexp (b : ℝ) (hb : 0 < b) : Tendsto (fun t : ℝ => Real.exp (-b * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hb))
  have hQ : Tendsto Q atTop (𝓝 0) := by simpa only [mul_zero] using (hexp a ha).const_mul δ
  have he : Tendsto e atTop (𝓝 (C * δ)) := by
    have hp := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).continuousAt.tendsto.comp hQ
    simpa only [e, Function.comp_def, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), zero_add] using
      (hp.add_const δ).const_mul C
  have hE : Tendsto E atTop (𝓝 (L δ)) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := ((Real.continuous_exp.continuousAt.tendsto.comp he).const_mul (1 + C * δ)).sub
      ((hone.sub (hQ.div_const (r 0))).mul (Real.continuous_exp.continuousAt.tendsto.comp he.neg))
    simpa only [E, L, Function.comp_def, zero_div, sub_zero, one_mul] using hh
  have hηH : Tendsto ηH atTop (𝓝 0) := by
    have hh := ((hOut.2.2.1.div_const cν).sub_const 1).abs
    change Tendsto (fun t => |(Real.exp (-a * t) * S t) / cν - 1|) atTop (𝓝 |cν / cν - 1|) at hh
    have heq (t : ℝ) : S t / (cν * Real.exp (a * t)) = (Real.exp (-a * t) * S t) / cν := by
      rw [show -a * t = -(a * t) by ring, Real.exp_neg]
      ring
    simpa only [ηH, heq, div_self hcν.ne', sub_self, abs_zero] using hh
  have hG : Tendsto G atTop (𝓝 0) := by
    simpa only [mul_zero] using (hexp (2 * s) (by positivity)).const_mul (2 * dH / (δ * cν))
  have hF : Tendsto F atTop (𝓝 (L δ)) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [add_zero, mul_one] using ((hE.mul (hone.add hηH)).add hηH).add hG
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((hQ.eventually_lt_const zero_lt_one).and
    (hF.eventually_lt_const (show L δ < η / 2 by linarith only [hsmall.1, hη])))
  refine ⟨δ, max 0 T, hδ, hsmall.2.2.2, le_max_left _ _, hδr, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn u v hv hlo hhi
  have ht := hT v ((le_max_right _ _).trans hv)
  have hu : 0 < (u : ℝ) := (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 ((half_pos hδ).trans_le hlo)
  have huQ : (u : ℝ) ≤ Q v := by
    apply (mul_le_mul_iff_left₀ (Real.exp_pos (a * v))).1
    calc
      (u : ℝ) * Real.exp (a * v) ≤ δ := hhi
      _ = Q v * Real.exp (a * v) := by
        dsimp only [Q]
        rw [mul_assoc, ← Real.exp_add, show -a * (v : ℝ) + a * v = 0 by ring, Real.exp_zero, mul_one]
  let hf' := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
  have hy := hx.horizon_prefix hU hV hUR u.property.1 v.property.1 u.property.2 v.property.2 hc hi hrc hr0 hp hf
  let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (v : ℝ))
    le_rfl (by simpa only [zero_add] using u.property.2) le_rfl (by simpa only [zero_add] using v.property.2) x
  let uu : Icc 0 (u : ℝ) := ⟨u, u.property.1, le_rfl⟩
  let vv : Icc 0 (v : ℝ) := ⟨v, v.property.1, le_rfl⟩
  have hfn' : (eLpNorm f p (volume.restrict (Icc 0 (u : ℝ)))).toReal ≤ A :=
    (scalar_prefix_norm_le u.property.2 hf).trans hfn
  have hcb : 0 ≤ a * (1 - 1 / p.toReal) :=
    mul_nonneg ha.le (by linarith only [(incoming_exponent_bounds hp).1])
  have hrel := houter u v u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    p hp f hf' y hy hfn' hcb (hhi.trans hsmall.2.2.1.le)
  let e₀ := C * ((u : ℝ) ^ (1 - 2 / p.toReal) + (u : ℝ) * Real.exp (a * v))
  let E₀ := (1 + C * ((u : ℝ) * Real.exp (a * v))) * Real.exp e₀ -
    (1 - (u : ℝ) / r 0) * Real.exp (-e₀)
  have he' : e₀ ≤ e v := by
    have hpow := (Real.rpow_le_rpow_of_exponent_ge hu (huQ.trans ht.1.le)
      (incoming_exponent_bounds hp).2).trans
        (Real.rpow_le_rpow hu.le huQ (by norm_num : (0 : ℝ) ≤ 1 / 2))
    exact mul_le_mul_of_nonneg_left (add_le_add hpow hhi) hC
  have hE' : E₀ ≤ E v := by
    have hfirst := mul_le_mul
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hhi hC))
      (Real.exp_le_exp.2 he') (Real.exp_pos _).le (by positivity : 0 ≤ 1 + C * δ)
    have hinit : 1 - Q v / r 0 ≤ 1 - (u : ℝ) / r 0 :=
      sub_le_sub_left (div_le_div_of_nonneg_right huQ hrp.le) 1
    have hsecond := mul_le_mul_of_nonneg_right hinit (Real.exp_pos (-e v)).le
    have hinit0 : 0 ≤ 1 - (u : ℝ) / r 0 := by
      rw [sub_nonneg, div_le_one hrp]
      exact (u.property.2.trans_lt hUR).le
    exact sub_le_sub hfirst (hsecond.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg he')) hinit0))
  have hS : 0 < S v := neg_pos.2 (horizon_normalization _ v).1
  have hresult := hy.radial_outer_reference_bound hy.choose rfl
    (incomingWave_constraint_data u.property.1 (u.property.2.trans_lt hUR) hp hf' (horizonPhi h r 0)).1
    hS hcν vv (ε := E v) (η := ηH v) (a := a) (rplus := B.event)
    (fun q => (hrel.1 q vv).trans hE') le_rfl uu hu
  have htrace := (hy.horizon_traces u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    hc hi hrc hr0 hφ hrd hp hf').2 vv
  rw [htrace] at hresult
  let P := (u : ℝ) * (cν * Real.exp (a * v))
  have hP : 0 < P := mul_pos hu (mul_pos hcν (Real.exp_pos _))
  have hPlo : δ * cν / 2 ≤ P := by
    have hh := mul_le_mul_of_nonneg_right hlo hcν.le
    dsimp only [P]
    nlinarith only [hh]
  have hPhi : P ≤ cν * δ := by
    have hh := mul_le_mul_of_nonneg_right hhi hcν.le
    dsimp only [P]
    nlinarith only [hh]
  have htail : |r v - B.event| / P ≤ G v := by
    apply (div_le_div_of_nonneg_right (hrdec v v.property.1) hP.le).trans
    apply (div_le_div_of_nonneg_left (mul_nonneg hdH (Real.exp_pos _).le)
      (by positivity : 0 < δ * cν / 2) hPlo).trans_eq
    dsimp only [G]
    ring
  have hnu := hx.horizon_overlap_nu hU hV hUR u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    hc hi hrc hr0 hp hf hf' hy u.property uu.property v.property vv.property
  have hrad := congrArg (fun z : WaveVector => z 0)
    (hx.horizon_overlap hU hV hUR u.property.1 v.property.1 (u.property.2.trans_lt hUR)
      hc hi hrc hr0 hp hf hf' hy u.property uu.property v.property vv.property).1
  rw [← hnu, ← hrad] at hresult
  have hG0 : 0 ≤ G v := by dsimp only [G]; positivity
  have hνerr := (hresult.1.trans (le_add_of_nonneg_right hG0)).trans_lt ht.2
  have hgaperr := (hresult.2.trans (add_le_add le_rfl htail)).trans_lt ht.2
  have hgaplo : cν * δ / 4 < B.event - x.1 u v 0 := by
    have hh : (1 / 2 : ℝ) < (B.event - x.1 u v 0) / P := by linarith only [(abs_lt.1 hgaperr).1, hη1]
    have hh' := (lt_div_iff₀ hP).1 hh
    nlinarith only [hh', hPlo]
  have hgaphi : B.event - x.1 u v 0 < 2 * cν * δ := by
    have hh : (B.event - x.1 u v 0) / P < 2 := by linarith only [(abs_lt.1 hgaperr).2, hη1]
    have hh' := (div_lt_iff₀ hP).1 hh
    nlinarith only [hh', hPhi]
  have hrclose : |x.1 u v 0 - B.event| < η := by
    rw [abs_sub_comm, abs_of_pos ((by positivity : 0 < cν * δ / 4).trans hgaplo)]
    nlinarith only [hgaphi, hsmall.2.1, hη]
  have hconverted := hconvert (x.1 u v 0) u
    (radialNuField hV B.charge B.cosmological (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v)
    (cν * Real.exp (a * v)) hu (mul_pos hcν (Real.exp_pos _)) hrclose
    (hνerr.trans (half_lt_self hη)) (hgaperr.trans (half_lt_self hη))
  exact ⟨⟨hgaplo, hgaphi⟩, hconverted.2⟩

end CauchyHorizon.Background
