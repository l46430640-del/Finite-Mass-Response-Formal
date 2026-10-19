import CauchyHorizon.Characteristic.OuterNormalization
import CauchyHorizon.Characteristic.HorizonBounds
import CauchyHorizon.Reduced.OuterFlux

/-! The actual thin outer flux and lambda/r have uniform leading coefficients up to the horizon. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

theorem exists_outer_flux_normalization (B : Background) {s H dH A : ℝ}
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
    ∀ cap ε : ℝ, 0 < cap → 0 < ε → ∃ δ T : ℝ, 0 < δ ∧ δ < cap ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (_hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U * Real.exp (B.outerRate * V) ≤ δ →
        ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
          (∀ w : Icc 0 U,
            B.event / 2 ≤ x.1 w v 0 ∧
            |x.1 w v 0 * (Real.exp (x.1 w v 2) * radialPotential (x.1 w v 0) B.charge B.cosmological) /
              ((cν * Real.exp (B.outerRate * v)) * (x.1 u v 0) ^ 2) + B.outerRate / B.event| < ε) ∧
          |x.2.1 u v 0 / x.1 u v 0 -
            r v * horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological / (x.1 u v 0) ^ 2 +
            (B.outerRate / B.event) * u * (cν * Real.exp (B.outerRate * v))| ≤
              ε * u * (cν * Real.exp (B.outerRate * v)) := by
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
  have hNH0 : 0 < NH := zero_lt_one.trans_le hNH
  obtain ⟨δ₀, C, hδ₀, _, hC, houter⟩ := exists_horizon_outer_normalization
    hc hi hrc hr0 hφ hrd ha le_rfl ha hρ hnH hNH0 hH hW hA haxis hνaxis hout hlout
  dsimp only
  intro cap ε hcap hε
  let K := fun q : ℝ × ℝ × ℝ × ℝ =>
    4 * q.1 * radialPotential q.1 B.charge B.cosmological * q.2.2.1 * q.2.2.2 / q.2.1 ^ 2
  let q₀ : ℝ × ℝ × ℝ × ℝ := (B.event, B.event, 1, 1)
  have hKc : ContinuousAt K q₀ := by
    dsimp only [K, radialPotential]
    fun_prop (disch := dsimp only [q₀]; positivity [B.event_pos])
  have hK0 : K q₀ = -(a / B.event) := by
    dsimp only [K, q₀]
    rw [B.radialPotential_event]
    dsimp only [a]
    field_simp [B.event_pos.ne']
  have hnear : ∀ᶠ q in 𝓝 q₀, |K q + a / B.event| < ε :=
    ((hKc.tendsto.add_const (a / B.event)).abs).eventually_lt_const
      (by simpa only [hK0, neg_add_cancel, abs_zero] using hε)
  obtain ⟨η₀, hη₀, hball₀⟩ := Metric.mem_nhds_iff.1 hnear
  let η := min η₀ (B.event / 2)
  have hη : 0 < η := lt_min hη₀ (half_pos B.event_pos)
  have hηR : η ≤ B.event / 2 := min_le_right _ _
  have hball := fun {q} (hq : q ∈ Metric.ball q₀ η) =>
    hball₀ (Metric.ball_subset_ball (min_le_left η₀ (B.event / 2)) hq)
  let e := fun d : ℝ => C * (d ^ (1 / 2 : ℝ) + d)
  let E := fun d : ℝ => (1 + C * d) * Real.exp (e d) - (1 - d / r 0) * Real.exp (-e d)
  have hec : Continuous e := by
    exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).add continuous_id).const_mul C
  have hEc : Continuous E := by dsimp only [E]; fun_prop
  have he0 : e 0 = 0 := by simp [e]
  have hE0 : E 0 = 0 := by simp [E, he0]
  have hremc : Continuous (fun d => E d + (1 - Real.exp (-e d))) := by fun_prop
  have hsmall : ∀ᶠ d in 𝓝 (0 : ℝ), E d < 1 ∧ E d + (1 - Real.exp (-e d)) < η ∧
      2 * NH * d < η / 2 ∧ d < min δ₀ (min cap (min 1 (r 0 / 2))) := by
    refine (hEc.continuousAt.tendsto.eventually_lt_const (by simpa only [hE0] using zero_lt_one)).and ?_
    refine (hremc.continuousAt.tendsto.eventually_lt_const
      (by simpa only [hE0, he0, neg_zero, Real.exp_zero, sub_self, zero_add] using hη)).and ?_
    refine ((continuous_id.const_mul (2 * NH)).continuousAt.tendsto.eventually_lt_const
      (by simpa only [id_eq, mul_zero] using half_pos hη)).and ?_
    exact eventually_lt_nhds (by positivity)
  obtain ⟨δ, hδ, hsmall⟩ := hsmall.exists_gt
  have hδbase : δ < δ₀ := hsmall.2.2.2.trans_le (min_le_left _ _)
  have hδcap : δ < cap := hsmall.2.2.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hsmall.2.2.2.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  let ηH := fun t => |S t / (cν * Real.exp (a * t)) - 1|
  have hηH : Tendsto ηH atTop (𝓝 0) := by
    have hh := ((hOut.2.2.1.div_const cν).sub_const 1).abs
    change Tendsto (fun t => |(Real.exp (-a * t) * S t) / cν - 1|) atTop (𝓝 |cν / cν - 1|) at hh
    have heq (t : ℝ) : S t / (cν * Real.exp (a * t)) = (Real.exp (-a * t) * S t) / cν := by
      rw [show -a * t = -(a * t) by ring, Real.exp_neg]
      ring
    simpa only [ηH, heq, div_self hcν.ne', sub_self, abs_zero] using hh
  have htail : Tendsto (fun t : ℝ => dH * Real.exp (-(2 * s) * t)) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-(2 * s) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (by linarith only [hs] : -(2 * s) < 0))
    simpa only [mul_zero] using he.const_mul dH
  obtain ⟨T, hT⟩ := eventually_atTop.1
    ((hηH.eventually_lt_const hη).and (htail.eventually_lt_const (half_pos hη)))
  refine ⟨δ, max 0 T, hδ, hδcap, le_max_left _ _, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hwidth
  let ν := radialNuField hV B.charge B.cosmological (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let σ := U * Real.exp (a * V)
  let e₀ := C * (U ^ (1 - 2 / p.toReal) + σ)
  let E₀ := (1 + C * σ) * Real.exp e₀ - (1 - U / r 0) * Real.exp (-e₀)
  have hUδ : U ≤ δ := (le_mul_of_one_le_right hU
    (Real.one_le_exp_iff.2 (mul_nonneg ha.le hV))).trans hwidth
  have hpow : U ^ (1 - 2 / p.toReal) ≤ δ ^ (1 / 2 : ℝ) := by
    rcases hU.eq_or_lt with hz | hu
    · rw [← hz, Real.zero_rpow (by linarith only [(incoming_exponent_bounds hp).2] : 1 - 2 / p.toReal ≠ 0)]
      exact Real.rpow_nonneg hδ.le _
    · exact (Real.rpow_le_rpow_of_exponent_ge hu (hUδ.trans hδ1) (incoming_exponent_bounds hp).2).trans
        (Real.rpow_le_rpow hU hUδ (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have he : e₀ ≤ e δ := mul_le_mul_of_nonneg_left (add_le_add hpow hwidth) hC
  have hE : E₀ ≤ E δ := by
    have hfirst := mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_left hwidth hC))
      (Real.exp_le_exp.2 he) (Real.exp_pos _).le (by positivity : 0 ≤ 1 + C * δ)
    have hinit := sub_le_sub_left (div_le_div_of_nonneg_right hUδ hrp.le) 1
    have hsecond := mul_le_mul_of_nonneg_right hinit (Real.exp_pos (-e δ)).le
    have hinit0 : 0 ≤ 1 - U / r 0 := by rw [sub_nonneg, div_le_one hrp]; exact hUR.le
    exact sub_le_sub hfirst (hsecond.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg he)) hinit0))
  have hcb : 0 ≤ a * (1 - 1 / p.toReal) :=
    mul_nonneg ha.le (by linarith only [(incoming_exponent_bounds hp).1])
  have hnorm := houter U V hU hV hUR p hp f hf x hx hfn hcb (hwidth.trans hδbase.le)
  have hpoint (v : Icc 0 V) (hv : max 0 T ≤ (v : ℝ)) (u : Icc 0 U) :
      |x.1 u v 0 - B.event| < η ∧ |Real.exp (x.1 u v 2) / (4 * S v) - 1| < η := by
    have ht := hT v ((le_max_right _ _).trans hv)
    have hS : 0 < S v := neg_pos.2 (horizon_normalization _ v).1
    have hgap : |r v - x.1 u v 0| < η / 2 := by
      rcases u.property.1.eq_or_lt with hz | hu
      · have hu0 : u = ⟨0, le_rfl, hU⟩ := Subtype.ext hz.symm
        rw [hu0, (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
        change |r v - r v| < η / 2
        rw [sub_self, abs_zero]
        exact half_pos hη
      · have hh := (hnorm.2.1 u hu v).trans hE
        have hq : |(r v - x.1 u v 0) / ((u : ℝ) * S v)| ≤ 1 + E δ := by
          have habs := abs_add_le ((r v - x.1 u v 0) / ((u : ℝ) * S v) - 1) 1
          rw [sub_add_cancel, abs_one] at habs
          linarith only [habs, hh]
        rw [abs_div, abs_of_pos (mul_pos hu hS)] at hq
        have hq' := (div_le_iff₀ (mul_pos hu hS)).1 hq
        have hscale : (u : ℝ) * Real.exp (a * v) ≤ δ :=
          (mul_le_mul u.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 ha.le))
            (Real.exp_pos _).le hU).trans hwidth
        have hSu : (u : ℝ) * S v ≤ NH * δ := by
          have hh' := mul_le_mul_of_nonneg_left (hνaxis v v.property.1).2 u.property.1
          have hh'' := mul_le_mul_of_nonneg_left hscale hNH0.le
          nlinarith only [hh', hh'']
        have htwo : |r v - x.1 u v 0| ≤ 2 * NH * δ := by
          nlinarith only [hq', hSu, hsmall.1, mul_pos hu hS]
        exact htwo.trans_lt hsmall.2.2.1
    have hrclose : |x.1 u v 0 - B.event| < η := by
      have hh := abs_sub_le (x.1 u v 0) (r v) B.event
      rw [abs_sub_comm (x.1 u v 0) (r v)] at hh
      have hrad := (hrdec v v.property.1).trans_lt ht.2
      rw [Real.norm_eq_abs] at hrad
      linarith only [hh, hgap, hrad]
    have hconf : |Real.exp (x.1 u v 2) / (4 * S v) - 1| < η :=
      ((hnorm.2.2 u v).trans (add_le_add hE (sub_le_sub_left (Real.exp_le_exp.2 (neg_le_neg he)) 1))).trans_lt
        hsmall.2.1
    exact ⟨hrclose, hconf⟩
  have hrow (v : Icc 0 V) (hv : max 0 T ≤ (v : ℝ)) (u w : Icc 0 U) :
      |x.1 w v 0 * (Real.exp (x.1 w v 2) * radialPotential (x.1 w v 0) B.charge B.cosmological) /
        ((cν * Real.exp (a * v)) * (x.1 u v 0) ^ 2) + a / B.event| < ε := by
    have hu := hpoint v hv u
    have hw := hpoint v hv w
    have hS : 0 < S v := neg_pos.2 (horizon_normalization _ v).1
    have hh := hball (show (x.1 w v 0, x.1 u v 0, Real.exp (x.1 w v 2) / (4 * S v),
        S v / (cν * Real.exp (a * v))) ∈ Metric.ball q₀ η from by
      rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq,
        Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt hw.1 (max_lt hu.1 (max_lt hw.2 (hT v ((le_max_right _ _).trans hv)).1)))
    have heq : K (x.1 w v 0, x.1 u v 0, Real.exp (x.1 w v 2) / (4 * S v), S v / (cν * Real.exp (a * v))) =
        x.1 w v 0 * (Real.exp (x.1 w v 2) * radialPotential (x.1 w v 0) B.charge B.cosmological) /
          ((cν * Real.exp (a * v)) * (x.1 u v 0) ^ 2) := by
      dsimp only [K]
      field_simp [hS.ne']
    change |K (x.1 w v 0, x.1 u v 0, Real.exp (x.1 w v 2) / (4 * S v),
      S v / (cν * Real.exp (a * v))) + a / B.event| < ε at hh
    rwa [heq] at hh
  intro u v hv
  refine ⟨fun w => ⟨?_, hrow v hv u w⟩, ?_⟩
  · have hh := (abs_lt.1 (hpoint v hv w).1).1
    linarith only [hh, hηR]
  have hbound (w : Icc 0 U) :
      |x.1 w v 0 * (Real.exp (x.1 w v 2) * radialPotential (x.1 w v 0) B.charge B.cosmological) /
        (cν * Real.exp (a * v)) + (a / B.event) * (x.1 u v 0) ^ 2| ≤ ε * (x.1 u v 0) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (hrow v hv u w).le (sq_nonneg (x.1 u v 0))
    have heq : (x.1 w v 0 * (Real.exp (x.1 w v 2) * radialPotential (x.1 w v 0) B.charge B.cosmological) /
        ((cν * Real.exp (a * v)) * (x.1 u v 0) ^ 2) + a / B.event) * (x.1 u v 0) ^ 2 =
        x.1 w v 0 * (Real.exp (x.1 w v 2) * radialPotential (x.1 w v 0) B.charge B.cosmological) /
          (cν * Real.exp (a * v)) + (a / B.event) * (x.1 u v 0) ^ 2 := by
      field_simp [hx.choose u v]
    rw [← heq, abs_mul, abs_of_nonneg (sq_nonneg (x.1 u v 0))]
    exact hh
  have hh := hx.outer_lambda_coefficient hx.choose rfl
    (mul_pos hcν (Real.exp_pos _)) v hbound u
  rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v] at hh
  have hcanc (z : ℝ) : (z * (x.1 u v 0) ^ 2) * u * (cν * Real.exp (a * v)) / (x.1 u v 0) ^ 2 =
      z * u * (cν * Real.exp (a * v)) := by field_simp [hx.choose u v]
  simp only [hcanc] at hh
  exact hh

end CauchyHorizon.Background
