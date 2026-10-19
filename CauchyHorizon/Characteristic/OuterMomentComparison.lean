import CauchyHorizon.Characteristic.OuterMoment
import CauchyHorizon.Characteristic.LateOuterFeedback
import CauchyHorizon.Characteristic.OuterEnergyBound

/-! The actual outer radiation approaches its signed first moment with all feedback controlled. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon

theorem outerRadiationEnvelope_mono_width {U V δ Δ a k : ℝ}
    (hU : 0 ≤ U) (hδ : 0 ≤ δ) (hΔ : 0 ≤ Δ) (hδΔ : δ ≤ Δ)
    (x : WaveState U V) (v : Icc 0 V) :
    outerRadiationEnvelope hδ a k x v ≤ outerRadiationEnvelope hΔ a k x v := by
  apply (outerRadiationEnvelope_le_iff hU hδ x v).2
  intro u hu
  exact (outerRadiationEnvelope_le_iff hU hΔ x v).1 le_rfl u
    (hu.trans (mul_le_mul_of_nonneg_right hδΔ (Real.exp_pos _).le))

namespace Background

set_option maxHeartbeats 600000 in
theorem exists_outer_radiation_moment_comparison (B : Background) {s H dH A b k : ℝ}
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
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∀ cap ε : ℝ, 0 < cap → 0 < ε →
      ∃ δ T : ℝ, 0 < δ ∧ δ < cap ∧ δ ≤ 1 ∧ 0 ≤ T ∧
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (P : ℝ →ᵇ ℝ)
          (_hkp : k ≤ B.outerRate * (1 - 1 / p.toReal)) (_hP : Integrable (fun t => P t ^ 2))
          (hf : MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x),
          (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))).toReal ≤ A →
          let E := fun (u : Icc 0 U) (v : Icc 0 V) =>
            x.1 u v 0 * x.2.1 u v 1 -
              (B.outerRate / B.event) * r 0 * (cν * Real.exp (B.outerRate * v)) *
                ∫ t in (0 : ℝ)..u, t * logarithmicIncoming b ℓ P t
          ∀ (l S : ℝ) (g : ℝ → ℝ), T ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
            (∀ t ∈ Icc l S, g t ∈ Icc 0 U ∧ g t * Real.exp (B.outerRate * t) ≤ δ) →
            IntegrableOn (fun t => (Real.exp (k * t) * E (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2)
              (Icc l S) ∧
            (∫ t in l..S, (Real.exp (k * t) * E (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2) ≤
              ε * δ ^ (2 * (b + 1)) * (1 + ∫ t, P t ^ 2) := by
  intro hi hr0 cν
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
  obtain ⟨δf, _L, Cf, _Dt, hδf, _hδf1, _hL, hCf, _hDt, hfeedback⟩ :=
    B.exists_late_outer_feedback hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  obtain ⟨Cm, _hCm, hmoment⟩ := B.exists_outer_moment_energy hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  let E₀ := 4 * H ^ 2 / (s - k)
  let E₁ := 8 * Ce ^ 2 * Δ ^ (2 * b) / a
  let D := (Cf / (a - k)) ^ 2
  let K := 3 * D * (E₀ + E₁)
  let q := 2 * (b + 1)
  let m := 2 * (1 - b)
  let d := 2 * (s - k)
  let Ch := H ^ 2 / d
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp only [E₁]; positivity
  have hD : 0 ≤ D := sq_nonneg _
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hm : 0 < m := by dsimp only [m]; linarith only [hb1]
  have hd : 0 < d := by dsimp only [d]; linarith only [hks]
  intro cap ε hcap hε
  let η := min 1 (ε * a / 12)
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hηsq := mul_le_mul_of_nonneg_left (min_le_left 1 (ε * a / 12)) hη.le
  have hηbound : 6 * η ^ 2 / a ≤ ε / 2 := by
    apply (div_le_iff₀ ha).2
    have hh := min_le_right 1 (ε * a / 12)
    change η ≤ ε * a / 12 at hh
    change η * η ≤ η * 1 at hηsq
    nlinarith only [hηsq, hh]
  have hsmall : ∀ᶠ w : ℝ in 𝓝 0, K * w ^ m < ε / 2 :=
    ((Real.continuous_rpow_const hm.le).const_mul K).continuousAt.tendsto.eventually_lt_const
      (by simpa only [Real.zero_rpow hm.ne', mul_zero] using half_pos hε)
  obtain ⟨δs, hδs, hsmall⟩ := hsmall.exists_gt
  obtain ⟨δ, Tm, hδ, hδcap, hδ1, hTm, hmoment⟩ :=
    hmoment (min cap (min Δ (min δf δs))) η (by positivity) hη
  have hδΔ : δ ≤ Δ := hδcap.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδf' : δ ≤ δf := hδcap.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδs' : δ ≤ δs := hδcap.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmallδ : K * δ ^ m ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδs' hm.le) hK).trans hsmall.le
  obtain ⟨Tf, hTf, hfeedback⟩ := hfeedback δ hδ hδf'
  have hexp (c : ℝ) (hc : 0 < c) : Tendsto (fun t : ℝ => Real.exp (-c * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have htail : Tendsto (fun t : ℝ => 3 * Cm * Real.exp (-(4 * s) * t) + 3 * Ch * Real.exp (-d * t))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((hexp (4 * s) (by positivity)).const_mul (3 * Cm)).add ((hexp d hd).const_mul (3 * Ch))
  obtain ⟨Th, hTh⟩ := eventually_atTop.1 (htail.eventually_lt_const
    (show 0 < (ε / 2) * δ ^ q by positivity))
  refine ⟨δ, max Tm (max Tf Th), hδ, hδcap.trans_le (min_le_left _ _), hδ1,
    hTm.trans (le_max_left _ _), ?_⟩
  intro U V hU hV hUR p hp ℓ P hkp hP hf x hx hfn E l S g hl hlS hSV hgc hg
  have hlm : Tm ≤ l := (le_max_left _ _).trans hl
  have hlf : Tf ≤ l := ((le_max_left _ _).trans (le_max_right _ _)).trans hl
  have hlh : Th ≤ l := ((le_max_right _ _).trans (le_max_right _ _)).trans hl
  have hl0 : 0 ≤ l := hTm.trans hlm
  have hg' (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Icc 0 U ∧ g t ≤ δ * Real.exp (-a * t) := by
    refine ⟨(hg t ht).1, ?_⟩
    have hh := mul_le_mul_of_nonneg_right (hg t ht).2 (Real.exp_pos (-a * t)).le
    simpa only [a, mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one] using hh
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let F := scalarRadiationFeedback hU hV x.1 x.2.1 ν hx.choose
  let Mw := outerRadiationEnvelope hδ.le a k x
  let Me := outerRadiationEnvelope hΔ.le a k x
  let Ew := fun t => Real.exp (k * t) * E (projIcc 0 U hU (g t)) (projIcc 0 V hV t)
  let Fw := fun t => Real.exp (k * t) * F (projIcc 0 U hU (g t)) (projIcc 0 V hV t)
  let Ow := fun t => Real.exp (k * t) * h t
  let Rw := fun t => Real.exp (k * t) *
    (E (projIcc 0 U hU (g t)) (projIcc 0 V hV t) - h (projIcc 0 V hV t) -
      F (projIcc 0 U hU (g t)) (projIcc 0 V hV t))
  have hme := hmoment U V hU hV hUR p hp b k ℓ P hbpos hcrit hkp hP hf x hx hfn l S g hlm hlS hSV hgc hg
  have hfe := (((hfeedback U V hU hV hUR p hp (logarithmicIncoming b ℓ P) hf x hx hfn).2 k hka).2.2
    l S g hlf hlS hSV hgc hg')
  have hmee := (henergy U V hU hV hUR p hp ℓ P hP hf x hx hfn hkp).1
  have hMw : (∫ t in (0 : ℝ)..V, (Mw (projIcc 0 V hV t)) ^ 2) ≤ E₀ + E₁ * ∫ t, P t ^ 2 := by
    have hwi : Continuous (fun t => Mw (projIcc 0 V hV t)) := by fun_prop
    have hei : Continuous (fun t => Me (projIcc 0 V hV t)) := by fun_prop
    have hh := intervalIntegral.integral_mono_on (μ := volume) hV ((hwi.pow 2).intervalIntegrable _ _)
      ((hei.pow 2).intervalIntegrable _ _) (fun t _ =>
        (sq_le_sq₀ (outerRadiationEnvelope_nonneg hδ.le a k x _) (outerRadiationEnvelope_nonneg hΔ.le a k x _)).2
          (outerRadiationEnvelope_mono_width hU hδ.le hΔ.le hδΔ x _))
    exact hh.trans hmee
  have hri : IntegrableOn (fun t => Rw t ^ 2) (Icc l S) := by
    apply hme.1.congr
    filter_upwards [] with t
    dsimp only [Rw, E]
    ring
  have hre : (∫ t in l..S, Rw t ^ 2) ≤
      2 * (η * δ) ^ 2 * δ ^ (2 * b) / a * (∫ t, P t ^ 2) + Cm * Real.exp (-(4 * s) * l) := by
    convert hme.2 using 1
    congr 1
    ext t
    dsimp only [Rw, E]
    ring
  have hfi : IntegrableOn (fun t => Fw t ^ 2) (Icc l S) := hfe.1
  have hfe' : (∫ t in l..S, Fw t ^ 2) ≤ (Cf * δ ^ 2 / (a - k)) ^ 2 * (E₀ + E₁ * ∫ t, P t ^ 2) :=
    hfe.2.trans (mul_le_mul_of_nonneg_left hMw (sq_nonneg _))
  have hOc : Continuous Ow := by dsimp only [Ow]; fun_prop
  have hOb (t : ℝ) : ‖Ow t ^ 2‖ ≤ H ^ 2 * Real.exp (-d * t) := by
    have hh := mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos (k * t)).le
    rw [Real.norm_eq_abs] at hh
    have hsq := (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (by positivity)).2 hh
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      Ow t ^ 2 = (Real.exp (k * t) * |h t|) ^ 2 := by simp only [Ow, mul_pow, sq_abs]
      _ ≤ (Real.exp (k * t) * (H * Real.exp (-s * t))) ^ 2 := hsq
      _ = _ := by
        rw [show Real.exp (k * t) * (H * Real.exp (-s * t)) =
          H * (Real.exp (k * t) * Real.exp (-s * t)) by ring,
          mul_pow, ← Real.exp_add, ← Real.exp_nat_mul]
        congr 2
        dsimp only [d]
        ring
  have hoe : (∫ t in l..S, Ow t ^ 2) ≤ Ch * Real.exp (-d * l) := by
    rw [intervalIntegral.integral_of_le hlS]
    have hh := setIntegral_mono_set (exponentialTail_integrable hd (hOc.pow 2) hOb l)
      (Filter.Eventually.of_forall (fun t => sq_nonneg (Ow t)))
      (Filter.Eventually.of_forall (fun t (ht : t ∈ Ioc l S) => ht.1))
    exact hh.trans ((le_abs_self _).trans (exponentialTail_norm_le hd hOb l))
  have harg : ContinuousOn (fun t => (projIcc 0 U hU (g t), projIcc 0 V hV t)) (Icc l S) :=
    ((continuous_projIcc (a := (0 : ℝ)) (b := U) (h := hU)).comp_continuousOn hgc).prodMk
      (continuous_projIcc (a := (0 : ℝ)) (b := V) (h := hV)).continuousOn
  have hJc : ContinuousOn (fun u => ∫ t in (0 : ℝ)..u, t * logarithmicIncoming b ℓ P t) (Icc 0 U) := by
    simpa only [uIcc_of_le hU] using intervalIntegral.continuousOn_primitive_interval'
      (logarithmicIncoming_first_moment hbpos hU ℓ P).1 left_mem_uIcc
  have hJg := hJc.domRestrict.comp_continuousOn (continuous_fst.comp_continuousOn harg)
  have hθg : ContinuousOn (fun t => x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 *
      x.2.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 1) (Icc l S) := by
    have hz := ((continuous_apply (0 : Fin 3)).comp x.1.uncurry.continuous).comp_continuousOn harg
    have hw := ((continuous_apply (1 : Fin 3)).comp x.2.1.uncurry.continuous).comp_continuousOn harg
    exact hz.mul hw
  have hEc : ContinuousOn Ew (Icc l S) := by
    dsimp only [Ew, E]
    exact (by fun_prop : ContinuousOn (fun t => Real.exp (k * t)) (Icc l S)).mul
      (hθg.sub ((by fun_prop : ContinuousOn (fun t : ℝ =>
        (B.outerRate / B.event) * r 0 * (cν * Real.exp (B.outerRate * projIcc 0 V hV t))) (Icc l S)).mul hJg))
  have hei : IntegrableOn (fun t => Ew t ^ 2) (Icc l S) := (hEc.pow 2).integrableOn_Icc
  have hoi : IntegrableOn (fun t => Ow t ^ 2) (Icc l S) := (hOc.pow 2).integrableOn_Icc
  have hsum := intervalIntegral.integral_mono_on (μ := volume) hlS
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hei)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 (((hri.add hfi).add hoi).const_mul 3))
    (fun t ht => show Ew t ^ 2 ≤ 3 * ((Rw t ^ 2 + Fw t ^ 2) + Ow t ^ 2) from by
      have htV : t ∈ Icc 0 V := ⟨hl0.trans ht.1, ht.2.trans hSV⟩
      have heq : Ew t = Rw t + Fw t + Ow t := by
        dsimp only [Ew, Rw, Fw, Ow]
        rw [projIcc_of_mem hV htV]
        ring
      rw [heq]
      nlinarith only [sq_nonneg (Rw t - Fw t), sq_nonneg (Rw t - Ow t), sq_nonneg (Fw t - Ow t)])
  have hrii := (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hri
  have hfii := (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hfi
  have hoii := (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hoi
  simp only [Pi.add_apply] at hsum
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hrii.add hfii) hoii,
    intervalIntegral.integral_add hrii hfii] at hsum
  have hPI : 0 ≤ ∫ t, P t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  have hpw : δ ^ (4 : ℕ) = δ ^ q * δ ^ m := by
    rw [← Real.rpow_add hδ, show q + m = 4 by dsimp only [q, m]; ring]
    norm_num
  have hpw' : δ ^ (2 : ℕ) * δ ^ (2 * b) = δ ^ q := by
    rw [← Real.rpow_natCast δ 2, ← Real.rpow_add hδ]
    congr 1
    dsimp only [q]
    ring
  have hmcoef : 3 * (2 * (η * δ) ^ 2 * δ ^ (2 * b) / a * (∫ t, P t ^ 2)) ≤
      (ε / 2) * δ ^ q * ∫ t, P t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hηbound (mul_nonneg (Real.rpow_nonneg hδ.le q) hPI)
    calc
      _ = (6 * η ^ 2 / a) * ((δ ^ 2 * δ ^ (2 * b)) * ∫ t, P t ^ 2) := by ring
      _ ≤ _ := by rw [hpw']; simpa only [mul_assoc] using hh
  have hfcoef : 3 * ((Cf * δ ^ 2 / (a - k)) ^ 2 * (E₀ + E₁ * ∫ t, P t ^ 2)) ≤
      (ε / 2) * δ ^ q * (1 + ∫ t, P t ^ 2) := by
    have hbudget : E₀ + E₁ * (∫ t, P t ^ 2) ≤ (E₀ + E₁) * (1 + ∫ t, P t ^ 2) := by
      nlinarith only [hE₁, mul_nonneg hE₀ hPI]
    calc
      _ = 3 * D * δ ^ 4 * (E₀ + E₁ * ∫ t, P t ^ 2) := by dsimp only [D]; ring
      _ ≤ 3 * D * δ ^ 4 * ((E₀ + E₁) * (1 + ∫ t, P t ^ 2)) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = (K * δ ^ m) * (δ ^ q * (1 + ∫ t, P t ^ 2)) := by rw [hpw]; dsimp only [K]; ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hsmallδ
          (mul_nonneg (Real.rpow_nonneg hδ.le q) (by positivity))
  have htail' := (hTh l hlh).le
  refine ⟨hei, ?_⟩
  have hh := hsum.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hre hfe') hoe) (by norm_num))
  change _ ≤ ε * δ ^ q * (1 + ∫ t, P t ^ 2)
  nlinarith only [hh, hmcoef, hfcoef, htail']

end Background
end CauchyHorizon
