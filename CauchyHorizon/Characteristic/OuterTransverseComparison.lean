import CauchyHorizon.Characteristic.OuterMomentComparison
import CauchyHorizon.Reduced.ScalarRegularity

/-! The actual transverse scalar trace approaches its incoming term on every smaller outer section. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 600000 in
theorem exists_outer_transverse_comparison (B : Background) {s H dH A b k : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hbpos : 0 < b) (hb1 : b < 1) (hcrit : k = B.outerRate * b) (hks : k < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ₀ K : ℝ, 0 < δ₀ ∧ 0 < K ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (P : ℝ →ᵇ ℝ)
          (_hkp : k ≤ B.outerRate * (1 - 1 / p.toReal)) (_hP : Integrable (fun t => P t ^ 2))
          (hf : MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x),
          (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))).toReal ≤ A →
          ∀ (l S : ℝ) (g : ℝ → ℝ), 0 ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
            (∀ t ∈ Icc l S, g t ∈ Ioc 0 U ∧ g t * Real.exp (B.outerRate * t) ≤ δ) →
            let E := fun t => g t * Real.exp (k * t) *
              (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                  (Icc 0 U) (g t) - (r 0 - g t) * logarithmicIncoming b ℓ P (g t))
            IntegrableOn (fun t => E t ^ 2) (Icc l S) ∧
              (∫ t in l..S, E t ^ 2) ≤ K * δ ^ 2 * (1 + ∫ t, P t ^ 2) ∧
              (∫ t in l..S, E t ^ 2) / δ ^ (2 * b) ≤
                K * δ ^ (2 * (1 - b)) * (1 + ∫ t, P t ^ 2) := by
  intro hi hr0
  let a := B.outerRate
  let ρ := (B.event - dH) / 2
  have ha : 0 < a := B.outerRate_pos
  have hρ : 0 < ρ := half_pos (sub_pos.2 hdHR)
  have hka : k < a := by rw [hcrit]; nlinarith only [ha, hb1]
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨W, hW, hrlam⟩ := B.horizon_radius_lambda_bounds hs hH hdH hdHR hb hrdec
  have haxis (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : r t ∈ Icc (2 * ρ) (B.event + dH) :=
    ⟨by dsimp only [ρ]; linarith only [(hrlam t ht).1.1], (hrlam t ht).1.2⟩
  have hlout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      |horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological| ≤ W :=
    (hrlam t ht).2.trans (mul_le_of_le_one_right hW (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) ht)))
  obtain ⟨nH, NH, hnH, _, hNH, hνaxis⟩ := hOut.nu_bounds hs hc hi hrc hr0
  obtain ⟨Δ, Ce, _De, hΔ, _hΔ1, _hΔr, _hCe, _hDe, henergy⟩ :=
    exists_horizon_outer_energy_bound hc hi hrc hr0 hφ hrd ha hbpos hb1 hcrit hks hρ hnH
      (zero_lt_one.trans_le hNH) hH hW hA haxis hνaxis (fun t _ => hb t) hlout
  obtain ⟨δf, _L, _Cf, D, hδf, _hδf1, _hL, _hCf, hD, htransport⟩ :=
    B.exists_late_outer_feedback hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  let E₀ := 4 * H ^ 2 / (s - k)
  let E₁ := 8 * Ce ^ 2 * Δ ^ (2 * b) / a
  let K := 1 + (D / (a - k)) ^ 2 * (E₀ + E₁)
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨min Δ δf, K, lt_min hΔ hδf, hK, ?_⟩
  intro δ hδ hδ₀
  have hδΔ : δ ≤ Δ := hδ₀.trans (min_le_left _ _)
  obtain ⟨_T, _hT, htransport⟩ := htransport δ hδ (hδ₀.trans (min_le_right _ _))
  intro U V hU hV hUR p hp ℓ P hkp hP hf x hx hfn l S g hl hlS hSV hgc hg E
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let C := scalarTransportCorrection hV ν x.2.1
  let Mw := outerRadiationEnvelope hδ.le a k x
  let Me := outerRadiationEnvelope hΔ.le a k x
  let Q := fun t => g t * Real.exp (k * t) *
    intervalExtension hV (intervalExtension hU C (g t)) t
  have hQc : ContinuousOn Q (Icc l S) := by dsimp only [Q]; fun_prop
  have hgu (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Icc 0 U := ⟨(hg t ht).1.1.le, (hg t ht).1.2⟩
  have htv (t : ℝ) (ht : t ∈ Icc l S) : t ∈ Icc 0 V := ⟨hl.trans ht.1, ht.2.trans hSV⟩
  have hwidth (t : ℝ) (ht : t ∈ Icc l S) : g t ≤ δ * Real.exp (-a * t) := by
    have hh := mul_le_mul_of_nonneg_right (hg t ht).2 (Real.exp_pos (-a * t)).le
    simpa only [a, mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one] using hh
  have hcor := ((htransport U V hU hV hUR p hp (logarithmicIncoming b ℓ P) hf x hx hfn).2 k hka).1
  have hqe := causalExpIntegral_dominated_energy hV (sub_pos.2 hka) hl hlS hSV Mw hQc
    (C := D * δ) (fun t ht => by
      have hh := mul_le_mul_of_nonneg_left
        (hcor ⟨g t, hgu t ht⟩ ⟨t, htv t ht⟩ (hwidth t ht)) (hgu t ht).1
      have hJ : 0 ≤ causalExpIntegral hV (a - k) Mw ⟨t, htv t ht⟩ :=
        intervalIntegral.integral_nonneg (htv t ht).1
          (fun w _ => mul_nonneg (Real.exp_pos _).le (outerRadiationEnvelope_nonneg hδ.le a k x _))
      simp only [Q, abs_mul, abs_of_nonneg (hgu t ht).1, abs_of_pos (Real.exp_pos _),
        intervalExtension_apply, projIcc_of_mem hU (hgu t ht), projIcc_of_mem hV (htv t ht)]
      calc
        _ ≤ g t * (D * Real.exp (a * t) * causalExpIntegral hV (a - k) Mw ⟨t, htv t ht⟩) := by
          simpa only [mul_assoc] using hh
        _ = (g t * Real.exp (a * t)) * (D * causalExpIntegral hV (a - k) Mw ⟨t, htv t ht⟩) := by ring
        _ ≤ δ * (D * causalExpIntegral hV (a - k) Mw ⟨t, htv t ht⟩) :=
          mul_le_mul_of_nonneg_right (hg t ht).2 (mul_nonneg hD.le hJ)
        _ = _ := by ring)
  have hmee := (henergy U V hU hV hUR p hp ℓ P hP hf x hx hfn hkp).1
  have hMw : (∫ t in (0 : ℝ)..V, (Mw (projIcc 0 V hV t)) ^ 2) ≤ E₀ + E₁ * ∫ t, P t ^ 2 := by
    have hwi : Continuous (fun t => Mw (projIcc 0 V hV t)) := by fun_prop
    have hei : Continuous (fun t => Me (projIcc 0 V hV t)) := by fun_prop
    exact (intervalIntegral.integral_mono_on (μ := volume) hV ((hwi.pow 2).intervalIntegrable _ _)
      ((hei.pow 2).intervalIntegrable _ _) (fun t _ =>
        (sq_le_sq₀ (outerRadiationEnvelope_nonneg hδ.le a k x _) (outerRadiationEnvelope_nonneg hΔ.le a k x _)).2
          (outerRadiationEnvelope_mono_width hU hδ.le hΔ.le hδΔ x _))).trans hmee
  have hfc : ContinuousOn (logarithmicIncoming b ℓ P) (Ioi 0) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl ht.ne'))
    · exact P.continuous.comp_continuousOn
        (continuousOn_const.sub (continuousOn_id.log (fun t ht => ht.ne')))
  have hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 0 = -1 := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]
    rfl
  have hif : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      incomingWaveVelocity hUR hp hf u 1 = logarithmicIncoming b ℓ P u := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]
    rfl
  have heq (t : ℝ) (ht : t ∈ Icc l S) : E t = Q t := by
    have hd := hx.scalar_hasDerivWithinAt_of_continuous rfl hinu hfc hif (hg t ht).1
      (projIcc 0 V hV t)
    have hdd := hd.derivWithin ((uniqueDiffOn_Icc ((hg t ht).1.1.trans_le (hg t ht).1.2)) _ (hgu t ht))
    simp only [intervalExtension_apply] at hdd
    dsimp only [E, Q, intervalExtension_apply]
    rw [hdd, projIcc_of_mem hU (hgu t ht), mul_div_cancel₀ _ (hx.choose _ _)]
    simp only [incomingWaveCurve_apply, incomingRadius, Matrix.cons_val_zero]
    ring
  have hei : IntegrableOn (fun t => E t ^ 2) (Icc l S) :=
    ((hQc.congr heq).pow 2).integrableOn_Icc
  have he : (∫ t in l..S, E t ^ 2) = ∫ t in l..S, Q t ^ 2 :=
    intervalIntegral.integral_congr (fun t ht => congrArg (fun q : ℝ => q ^ 2)
      (heq t (by simpa only [uIcc_of_le hlS] using ht)))
  have hPI : 0 ≤ ∫ t, P t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  have hbudget : E₀ + E₁ * (∫ t, P t ^ 2) ≤ (E₀ + E₁) * (1 + ∫ t, P t ^ 2) := by
    nlinarith only [hE₁, mul_nonneg hE₀ hPI]
  have hbound : (∫ t in l..S, E t ^ 2) ≤ K * δ ^ 2 * (1 + ∫ t, P t ^ 2) := by
    rw [he]
    calc
      _ ≤ (D * δ / (a - k)) ^ 2 * (E₀ + E₁ * ∫ t, P t ^ 2) :=
        hqe.trans (mul_le_mul_of_nonneg_left hMw (sq_nonneg _))
      _ ≤ (D * δ / (a - k)) ^ 2 * ((E₀ + E₁) * (1 + ∫ t, P t ^ 2)) :=
        mul_le_mul_of_nonneg_left hbudget (sq_nonneg _)
      _ = ((D / (a - k)) ^ 2 * (E₀ + E₁)) * (δ ^ 2 * (1 + ∫ t, P t ^ 2)) := by ring
      _ ≤ _ := by
        have hh : (D / (a - k)) ^ 2 * (E₀ + E₁) ≤ K := by dsimp only [K]; linarith
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ δ ^ 2 * (1 + ∫ t, P t ^ 2))
  refine ⟨hei, hbound, ?_⟩
  have hpw : δ ^ (2 : ℕ) / δ ^ (2 * b) = δ ^ (2 * (1 - b)) := by
    rw [← Real.rpow_natCast δ 2, ← Real.rpow_sub hδ]
    congr 1
    ring
  exact (div_le_div_of_nonneg_right hbound (Real.rpow_nonneg hδ.le (2 * b))).trans_eq (by rw [← hpw]; ring)

end CauchyHorizon.Background
