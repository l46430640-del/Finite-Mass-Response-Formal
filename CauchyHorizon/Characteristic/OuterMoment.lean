import CauchyHorizon.Characteristic.MovingOuterFlux
import CauchyHorizon.Reduced.ScalarFeedback
import CauchyHorizon.Analysis.LogarithmicMatching

/-! The actual horizontal radiation integral is approximated by its signed first moment. -/

open Set MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 600000 in
theorem exists_outer_moment_energy (B : Background) {s H dH A : ℝ}
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ cap ε : ℝ, 0 < cap → 0 < ε →
      ∃ δ T : ℝ, 0 < δ ∧ δ < cap ∧ δ ≤ 1 ∧ 0 ≤ T ∧
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (p : ℝ≥0∞) (hp : 4 ≤ p) (b k ℓ : ℝ) (P : ℝ →ᵇ ℝ)
          (_hb : 0 < b) (_hcrit : k = B.outerRate * b)
          (_hkp : k ≤ B.outerRate * (1 - 1 / p.toReal)) (_hP : Integrable (fun t => P t ^ 2))
          (hf : MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x),
          (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))).toReal ≤ A →
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let F := scalarRadiationFeedback hU hV x.1 x.2.1 ν hx.choose
          let E := fun (u : Icc 0 U) (v : Icc 0 V) =>
            x.1 u v 0 * x.2.1 u v 1 - h v - F u v -
              (B.outerRate / B.event) * r 0 * (cν * Real.exp (B.outerRate * v)) *
                ∫ t in (0 : ℝ)..u, t * logarithmicIncoming b ℓ P t
          ∀ (l S : ℝ) (g : ℝ → ℝ), T ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
            (∀ t ∈ Icc l S, g t ∈ Icc 0 U ∧ g t * Real.exp (B.outerRate * t) ≤ δ) →
            IntegrableOn (fun t => (Real.exp (k * t) * E (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2)
              (Icc l S) ∧
            (∫ t in l..S, (Real.exp (k * t) * E (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2) ≤
              2 * (ε * δ) ^ 2 * δ ^ (2 * b) / B.outerRate * (∫ t, P t ^ 2) +
                C * Real.exp (-(4 * s) * l) := by
  intro hi hr0 cν
  let a := B.outerRate
  let α := a / B.event
  have ha : 0 < a := B.outerRate_pos
  have hα : 0 < α := div_pos ha B.event_pos
  have hcν : 0 < cν := Real.exp_pos _
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨C₀, _hC₀, hmoving⟩ := B.exists_moving_outer_flux hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  refine ⟨2 * C₀ ^ 2 / (4 * s), by positivity, ?_⟩
  intro cap ε hcap hε
  let η := ε / (cν * (r 0 + α) + 1)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨δ, T, hδ, hδcap, hδ1, hT, hmove⟩ :=
    hmoving (min cap η) η (lt_min hcap hη) hη
  have hδη : δ ≤ η := hδcap.le.trans (min_le_right _ _)
  have hsmall : cν * (η * r 0 + α * δ) ≤ ε := by
    have he : η * (cν * (r 0 + α) + 1) = ε := div_mul_cancel₀ _ (by positivity)
    have hm := mul_le_mul_of_nonneg_left hδη (mul_pos hcν hα).le
    nlinarith only [he, hm, hη]
  refine ⟨δ, T, hδ, hδcap.trans_le (min_le_left _ _), hδ1, hT, ?_⟩
  intro U V hU hV hUR p hp b k ℓ P hbpos hcrit hkp hP hf x hx hfn ν F E l S g hl hlS hSV hgc hg
  let f := logarithmicIncoming b ℓ P
  have hf2 : MemLp f 2 (volume.restrict (Icc 0 U)) :=
    hf.mono_exponent ((by norm_num : (2 : ℝ≥0∞) ≤ 4).trans hp)
  let H₀ := fun v => r v * horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological
  let Q := fun (u : Icc 0 U) (v : Icc 0 V) =>
    H₀ v * ∫ t in (0 : ℝ)..u, (r 0 - t) / (x.1 (projIcc 0 U hU t) v 0) ^ 2 * f t
  have hgeo := (hmove U V hU hV hUR p hp f hf x hx hfn).1
  have hQE := ((hmove U V hU hV hUR p hp f hf x hx hfn).2 k hkp).2 l S g hl hlS hSV hgc hg
  have hfi (u : Icc 0 U) : IntervalIntegrable f volume 0 u :=
    (logarithmicIncoming_primitive hbpos u.property.1 ℓ P).1
  have htheta (u : Icc 0 U) (v : Icc 0 V) :
      x.1 u v 0 * x.2.1 u v 1 = h v +
        (∫ t in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU t) v 0 *
          ((r 0 - t) / x.1 (projIcc 0 U hU t) v 0) * f t) + F u v := by
    have hh := hx.theta_incoming_feedback hx.choose rfl
      (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 u v
    have ht : x.1 ⟨0, le_rfl, hU⟩ v 0 *
        horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0 v 1 = h v := by
      rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
      change r v * (h v / r v) = h v
      field_simp [hr0 v]
    rw [ht] at hh
    convert hh using 2
    congr 1
    simp only [intervalIntegral.integral_of_le u.property.1]
    apply integral_congr_ae
    have hsub : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
    filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) (incomingWaveVelocity_ae hUR hp hf),
      ae_restrict_mem measurableSet_Ioc] with t ht htu
    rw [ht, incomingWaveCurve_apply, projIcc_of_mem hU (hsub htu)]
    rfl
  have hHc : Continuous (fun v : Icc 0 V => H₀ v) :=
    (hrc.comp continuous_subtype_val).mul
      ((continuous_apply (0 : Fin 3)).comp
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0).continuous)
  let K : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
    (⟨fun q : Icc 0 U × Icc 0 V =>
      (-x.2.1.uncurry q 0 / x.1.uncurry q 0 + H₀ q.2 / (x.1.uncurry q 0) ^ 2) * (r 0 - (q.1 : ℝ)) -
        α * r 0 * (q.1 : ℝ) * (cν * Real.exp (a * q.2)), by
      have hzc : Continuous (fun q : Icc 0 U × Icc 0 V => x.1.uncurry q 0) :=
        (continuous_apply (0 : Fin 3)).comp x.1.uncurry.continuous
      have hwc : Continuous (fun q : Icc 0 U × Icc 0 V => x.2.1.uncurry q 0) :=
        (continuous_apply (0 : Fin 3)).comp x.2.1.uncurry.continuous
      exact (((hwc.neg.div hzc (fun q => hx.choose q.1 q.2)).add
        ((hHc.comp continuous_snd).div (hzc.pow 2) (fun q => pow_ne_zero 2 (hx.choose q.1 q.2)))).mul
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).sub (by fun_prop)⟩ :
      C(Icc 0 U × Icc 0 V, ℝ)).curry
  let R := fun (u : Icc 0 U) (v : Icc 0 V) => ∫ t in (0 : ℝ)..u, K (projIcc 0 U hU t) v * f t
  have hReq (u : Icc 0 U) (v : Icc 0 V) : R u v = E u v + Q u v := by
    have hlc : Continuous (fun t => -x.2.1 (projIcc 0 U hU t) v 0 *
        ((r 0 - t) / x.1 (projIcc 0 U hU t) v 0)) := by
      fun_prop (disch := intro t; exact hx.choose _ _)
    have hQc : Continuous (fun t => (r 0 - t) / (x.1 (projIcc 0 U hU t) v 0) ^ 2) := by
      fun_prop (disch := intro t; exact pow_ne_zero 2 (hx.choose _ _))
    have hIi := (hfi u).continuousOn_mul hlc.continuousOn
    have hQi := ((hfi u).continuousOn_mul hQc.continuousOn).const_mul (H₀ v)
    have hJi : IntervalIntegrable (fun t => (α * r 0 * (cν * Real.exp (a * v))) * (t * f t)) volume 0 u :=
      ((hfi u).continuousOn_mul continuous_id.continuousOn).const_mul _
    calc
      R u v = ∫ t in (0 : ℝ)..u,
          (-x.2.1 (projIcc 0 U hU t) v 0 * ((r 0 - t) / x.1 (projIcc 0 U hU t) v 0) * f t +
            H₀ v * ((r 0 - t) / (x.1 (projIcc 0 U hU t) v 0) ^ 2 * f t)) -
              (α * r 0 * (cν * Real.exp (a * v))) * (t * f t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le u.property.1] at ht
        have htU : t ∈ Icc 0 U := ⟨ht.1, ht.2.trans u.property.2⟩
        change ((-x.2.1 (projIcc 0 U hU t) v 0 / x.1 (projIcc 0 U hU t) v 0 +
          H₀ v / (x.1 (projIcc 0 U hU t) v 0) ^ 2) * (r 0 - (projIcc 0 U hU t : ℝ)) -
          α * r 0 * (projIcc 0 U hU t : ℝ) * (cν * Real.exp (a * v))) * f t = _
        dsimp only
        rw [projIcc_of_mem hU htU]
        ring
      _ = E u v + Q u v := by
        rw [intervalIntegral.integral_sub (hIi.add hQi) hJi, intervalIntegral.integral_add hIi hQi,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        dsimp only [E, Q]
        rw [htheta u v]
        dsimp only [α, a, f]
        ring
  have hK (u : Icc 0 U) (v : Icc 0 V) (hv : T ≤ (v : ℝ))
      (hu : (u : ℝ) * Real.exp (a * v) ≤ δ) : |K u v| ≤ ε * δ := by
    have hu0 := u.property.1
    have hub : (u : ℝ) ≤ δ := (le_mul_of_one_le_right u.property.1
      (Real.one_le_exp_iff.2 (mul_nonneg ha.le v.property.1))).trans hu
    let D := x.2.1 u v 0 / x.1 u v 0 - H₀ v / (x.1 u v 0) ^ 2 + α * u * (cν * Real.exp (a * v))
    have hD : |D| ≤ η * u * (cν * Real.exp (a * v)) := (hgeo u v hv hu).2
    have hrad : 0 < r 0 - (u : ℝ) := sub_pos.2 (u.property.2.trans_lt hUR)
    have heq : K u v = -D * (r 0 - u) - α * (u : ℝ) ^ 2 * (cν * Real.exp (a * v)) := by
      change (-x.2.1 u v 0 / x.1 u v 0 + H₀ v / (x.1 u v 0) ^ 2) * (r 0 - u) -
        α * r 0 * u * (cν * Real.exp (a * v)) = _
      dsimp only [D]
      ring
    rw [heq]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_neg, abs_of_pos hrad, abs_of_nonneg (by positivity :
      0 ≤ α * (u : ℝ) ^ 2 * (cν * Real.exp (a * v)))]
    have hfirst := mul_le_mul hD (sub_le_self (r 0) u.property.1) hrad.le (by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hub
      (show 0 ≤ α * (u : ℝ) * (cν * Real.exp (a * v)) by positivity)
    have hscale := mul_le_mul_of_nonneg_left hu
      (show 0 ≤ cν * (η * r 0 + α * δ) by positivity)
    have hlast := mul_le_mul_of_nonneg_right hsmall hδ.le
    nlinarith only [hfirst, hsecond, hscale, hlast]
  have hRpoint (u : Icc 0 U) (v : Icc 0 V) (hv : T ≤ (v : ℝ))
      (hu : (u : ℝ) * Real.exp (a * v) ≤ δ) : |R u v| ≤ (ε * δ) * ∫ t in (0 : ℝ)..u, |f t| := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le u.property.1
      (f := fun t => K (projIcc 0 U hU t) v * f t)
      (g := fun t => (ε * δ) * |f t|)
      (Filter.Eventually.of_forall (fun t ht => by
        have htU : t ∈ Icc 0 U := ⟨ht.1.le, ht.2.trans u.property.2⟩
        rw [Real.norm_eq_abs, abs_mul, projIcc_of_mem hU htU]
        exact mul_le_mul_of_nonneg_right (hK ⟨t, htU⟩ v hv
          ((mul_le_mul_of_nonneg_right ht.2 (Real.exp_pos _).le).trans hu)) (abs_nonneg _)))
      ((hfi u).abs.const_mul _)
    simpa only [R, Real.norm_eq_abs, intervalIntegral.integral_const_mul] using hh
  let Rg := fun t => Real.exp (k * t) * R (projIcc 0 U hU (g t)) (projIcc 0 V hV t)
  let Qg := fun t => Real.exp (k * t) * Q (projIcc 0 U hU (g t)) (projIcc 0 V hV t)
  let Eg := fun t => Real.exp (k * t) * E (projIcc 0 U hU (g t)) (projIcc 0 V hV t)
  have harg : ContinuousOn (fun t => (projIcc 0 U hU (g t), projIcc 0 V hV t)) (Icc l S) :=
    ((continuous_projIcc (a := (0 : ℝ)) (b := U) (h := hU)).comp_continuousOn hgc).prodMk
      (continuous_projIcc (a := (0 : ℝ)) (b := V) (h := hV)).continuousOn
  have hRg : ContinuousOn Rg (Icc l S) := by
    have hRc := continuous_kernel_primitive hU K hf2
    change Continuous (fun q : Icc 0 U × Icc 0 V => R q.1 q.2) at hRc
    exact (by fun_prop : ContinuousOn (fun t => Real.exp (k * t)) (Icc l S)).mul
      (hRc.comp_continuousOn harg)
  let G := fun t => b * terminalGreen hbpos |P| t
  let τ := ℓ - Real.log δ
  have hPa : Integrable (fun t => |P| t ^ 2) := by
    change Integrable (fun t => |P t| ^ 2)
    simpa only [sq_abs] using hP
  obtain ⟨hGi, hGE⟩ := terminalGreen_l2_contraction hbpos |P| hPa
  have hshift : Integrable (fun t => G (τ + a * t) ^ 2) := (hGi.comp_add_left τ).comp_mul_left' ha.ne'
  have hchange : (∫ t, G (τ + a * t) ^ 2) = (1 / a) * ∫ t, G t ^ 2 := by
    rw [Measure.integral_comp_mul_left (fun t => G (τ + t) ^ 2) a,
      integral_add_left_eq_self (fun t => G t ^ 2) τ]
    simp only [abs_of_pos (inv_pos.2 ha), smul_eq_mul, one_div]
  have hRE : (∫ t in l..S, Rg t ^ 2) ≤ (ε * δ) ^ 2 * δ ^ (2 * b) / a * ∫ t, P t ^ 2 := by
    have hbound (t : ℝ) (ht : t ∈ Icc l S) :
        Rg t ^ 2 ≤ ((ε * δ) * δ ^ b) ^ 2 * G (τ + a * t) ^ 2 := by
      have htV : t ∈ Icc 0 V := ⟨hT.trans (hl.trans ht.1), ht.2.trans hSV⟩
      have hgt : g t ≤ δ * Real.exp (-a * t) := by
        have hh := mul_le_mul_of_nonneg_right (hg t ht).2 (Real.exp_pos (-a * t)).le
        simpa only [a, mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one] using hh
      have hsource := logarithmicIncoming_outer_source (hg t ht).1.1 hδ hbpos hcrit ℓ P t
      rw [min_eq_left hgt] at hsource
      have hpoint := hRpoint ⟨g t, (hg t ht).1⟩ ⟨t, htV⟩ (hl.trans ht.1) (hg t ht).2
      have hbound : |Rg t| ≤ ((ε * δ) * δ ^ b) * G (τ + a * t) := by
        rw [show Rg t = Real.exp (k * t) * R ⟨g t, (hg t ht).1⟩ ⟨t, htV⟩ by
          dsimp only [Rg]; rw [projIcc_of_mem hU (hg t ht).1, projIcc_of_mem hV htV],
          abs_mul, abs_of_pos (Real.exp_pos _)]
        have h1 := mul_le_mul_of_nonneg_left hpoint (Real.exp_pos (k * t)).le
        have h2 := mul_le_mul_of_nonneg_left hsource (mul_pos hε hδ).le
        exact (h1.trans (by simpa only [f, mul_left_comm] using h2)).trans_eq (by dsimp only [G, τ]; ring)
      have hn := (abs_nonneg (Rg t)).trans hbound
      simpa only [mul_pow, sq_abs] using (sq_le_sq₀ (abs_nonneg _) hn).2 hbound
    have hright : Continuous (fun t => ((ε * δ) * δ ^ b) ^ 2 * G (τ + a * t) ^ 2) := by fun_prop
    have hh := intervalIntegral.integral_mono_on (μ := volume) hlS ((hRg.pow 2).intervalIntegrable_of_Icc hlS)
      (hright.intervalIntegrable l S) hbound
    rw [intervalIntegral.integral_const_mul] at hh
    have hseg : (∫ t in l..S, G (τ + a * t) ^ 2) ≤ ∫ t, G (τ + a * t) ^ 2 := by
      rw [intervalIntegral.integral_of_le hlS]
      exact setIntegral_le_integral hshift (Filter.Eventually.of_forall (fun t => sq_nonneg _))
    have hwhole := hseg.trans_eq hchange
    have hPE : (∫ t, G t ^ 2) ≤ ∫ t, P t ^ 2 := by
      change (∫ t, G t ^ 2) ≤ ∫ t, |P t| ^ 2 at hGE
      simpa only [sq_abs] using hGE
    have he := hh.trans (mul_le_mul_of_nonneg_left
      (hwhole.trans (mul_le_mul_of_nonneg_left hPE (one_div_nonneg.2 ha.le))) (sq_nonneg _))
    have hpw : (δ ^ b) ^ 2 = δ ^ (2 * b) := by
      rw [mul_comm (2 : ℝ) b, Real.rpow_mul hδ.le, Real.rpow_two]
    exact he.trans_eq (by rw [mul_pow, hpw]; ring)
  have hRi : IntegrableOn (fun t => Rg t ^ 2) (Icc l S) := (hRg.pow 2).integrableOn_Icc
  have hQi : IntegrableOn (fun t => Qg t ^ 2) (Icc l S) := hQE.1
  have hEq (t : ℝ) : Eg t = Rg t - Qg t := by
    dsimp only [Eg, Rg, Qg]
    rw [hReq]
    ring
  have hEi : IntegrableOn (fun t => Eg t ^ 2) (Icc l S) := by
    let KQ : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
      (⟨fun q : Icc 0 U × Icc 0 V => H₀ q.2 * ((r 0 - (q.1 : ℝ)) / (x.1.uncurry q 0) ^ 2), by
        have hz := (continuous_apply (0 : Fin 3)).comp x.1.uncurry.continuous
        exact (hHc.comp continuous_snd).mul
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div (hz.pow 2)
            (fun q => pow_ne_zero 2 (hx.choose q.1 q.2)))⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry
    have hQc : Continuous (fun q : Icc 0 U × Icc 0 V => Q q.1 q.2) := by
      apply (continuous_kernel_primitive hU KQ hf2).congr
      intro q
      dsimp only [Q]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le q.1.property.1] at ht
      change H₀ q.2 * ((r 0 - (projIcc 0 U hU t : ℝ)) / (x.1 (projIcc 0 U hU t) q.2 0) ^ 2) * f t =
        H₀ q.2 * ((r 0 - t) / (x.1 (projIcc 0 U hU t) q.2 0) ^ 2 * f t)
      rw [projIcc_of_mem hU (show t ∈ Icc 0 U from ⟨ht.1, ht.2.trans q.1.property.2⟩)]
      ring
    have hQgc : ContinuousOn Qg (Icc l S) :=
      (by fun_prop : ContinuousOn (fun t => Real.exp (k * t)) (Icc l S)).mul (hQc.comp_continuousOn harg)
    have hEgc : ContinuousOn Eg (Icc l S) := (hRg.sub hQgc).congr (fun t _ => hEq t)
    exact (hEgc.pow 2).integrableOn_Icc
  have hSi : IntervalIntegrable (fun t => 2 * (Rg t ^ 2 + Qg t ^ 2)) volume l S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 ((hRi.add hQi).const_mul 2)
  have hsum := intervalIntegral.integral_mono_on (μ := volume) hlS
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hEi)
    hSi
    (fun t _ => by rw [hEq]; nlinarith only [sq_nonneg (Rg t + Qg t)])
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hRi)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hQi)] at hsum
  refine ⟨hEi, ?_⟩
  exact (hsum.trans (mul_le_mul_of_nonneg_left (add_le_add hRE hQE.2) (by norm_num))).trans_eq (by dsimp only [a]; ring)

end CauchyHorizon.Background
