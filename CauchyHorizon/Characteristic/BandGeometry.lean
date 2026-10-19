import CauchyHorizon.Radial.Band
import CauchyHorizon.Characteristic.FiniteGeometry
import CauchyHorizon.Characteristic.MassFlux
import CauchyHorizon.Reduced.MassRadialRate
import CauchyHorizon.Characteristic.LateMass

/-! Uniform fixed-band geometry from entry mass and a lower kappa bootstrap. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 800000 in
theorem Background.exists_band_geometry (B : Background) {Y R : ℝ}
    (hY : B.inner < Y) (hYR : Y ≤ R) (hR : R < B.event) :
    ∃ ε q P : ℝ, 0 < ε ∧ 0 < q ∧ 0 ≤ P ∧
      ∀ {U V : ℝ} {h r : ℝ → ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
        (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
        (_hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
        (_hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
          (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
        {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
        {x : WaveState U V}
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x)
        (u : Icc 0 U) (a b : Icc 0 V), a ≤ b → ∀ κ₀ : ℝ, 0 < κ₀ →
        let N := radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
        let m := massField B.charge B.cosmological x.1 x.2.1 N hx.choose
        let D := (R - Y) / (κ₀ * q)
        (∀ w ∈ Icc a b, x.1 u w 0 ∈ Icc Y R) →
        (∀ w ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) →
        B.mass - ε ≤ m u a →
          (∀ w ∈ Icc a b, κ₀ * q ≤ -x.2.1 u w 0) ∧ (b : ℝ) - a ≤ D ∧
          (Y / R) * Real.exp (-(4 * P) * D) * ((u : ℝ) * (-N u a)) ≤ (u : ℝ) * (-N u b) ∧
          (u : ℝ) * (-N u b) ≤ (R / Y) * Real.exp (4 * P * D) * ((u : ℝ) * (-N u a)) := by
  have hY0 : 0 < Y := B.inner_pos.trans hY
  have hR0 : 0 < R := hY0.trans_le hYR
  obtain ⟨ε, q, hε, hq, hF⟩ := B.exists_band_margin hY hYR hR
  obtain ⟨P, hP, hpot⟩ := radialPotential_bounded B.charge B.cosmological (R := R) hY0
  refine ⟨ε, q, P, hε, hq, hP, ?_⟩
  intro U V h r hU hV hUR hc hi hrc hr0 hφ hrd p hp f hf x hx u a b hab κ₀ hk0
  let N := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 N hx.choose
  let D := (R - Y) / (κ₀ * q)
  change (∀ w ∈ Icc a b, x.1 u w 0 ∈ Icc Y R) →
    (∀ w ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) → B.mass - ε ≤ m u a → _
  intro hrange hk hm
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hn (u' : Icc 0 U) (v : Icc 0 V) : N u' v < 0 := (hg u' v).2.2.1
  have hl (w : Icc 0 V) (hw : w ∈ Icc a b) : κ₀ * q ≤ -x.2.1 u w 0 := by
    have hmm : B.mass - ε ≤ m u w := hm.trans
      (hx.mass_monotone hU hV hUR hc hi hrc hr0 hφ hrd hp hf u hw.1)
    have hFw := hF (x.1 u w 0) (hrange w hw) (m u w) hmm
    have hid := massField_lambda_eq_kappa (e := B.charge) (Λ := B.cosmological)
      x.1 x.2.1 N hx.choose (fun u v => (hn u v).ne) u w
    change x.2.1 u w 0 = (-Real.exp (x.1 u w 2) / (4 * N u w)) *
      horizonFunction (x.1 u w 0) (m u w) B.charge B.cosmological at hid
    have hb := mul_le_mul_of_nonneg_left hFw (hg u w).2.2.2.1.le
    have hkk := mul_le_mul_of_nonneg_right (hk w hw) hq.le
    nlinarith only [hid, hb, hkk]
  have haR := hrange a (left_mem_Icc.2 hab)
  have hbR := hrange b (right_mem_Icc.2 hab)
  let rad : ℝ → ℝ := fun t => intervalExtension hV (x.1 u) t 0
  let vel : ℝ → ℝ := fun t => intervalExtension hV (x.2.1 u) t 0
  have hrc' : Continuous rad := by fun_prop
  have hvc : Continuous vel := by fun_prop
  have hd (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) : HasDerivAt rad (vel t) t := by
    have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.le.trans b.property.2⟩
    have hd := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (hx.longitudinal_derivative u htV)
    change HasDerivWithinAt rad (x.2.1 u ⟨t, htV⟩ 0) (Icc 0 V) t at hd
    have hh : HasDerivWithinAt rad (vel t) (Icc 0 V) t := by
      simpa only [vel, intervalExtension_apply, projIcc_of_mem hV htV] using hd
    exact hh.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (a : ℝ) ≤ b from hab)
    hrc'.continuousOn hd (hvc.intervalIntegrable (a : ℝ) b)
  have hint := intervalIntegral.integral_mono_on (μ := volume) (show (a : ℝ) ≤ b from hab)
    (hvc.intervalIntegrable _ _) (g := fun _ => -(κ₀ * q)) intervalIntegrable_const
    (fun t ht => by
      have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
      have hh := neg_le_neg (hl ⟨t, htV⟩ ⟨ht.1, ht.2⟩)
      simpa only [neg_neg, vel, intervalExtension_apply, projIcc_of_mem hV htV] using hh)
  rw [hi, intervalIntegral.integral_const, smul_eq_mul] at hint
  simp only [rad, intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property] at hint
  have htime : (b : ℝ) - a ≤ D := by
    apply (le_div_iff₀ (mul_pos hk0 hq)).2
    nlinarith only [hint, haR.2, hbR.1]
  have hflux := radialNuField_flux_segment_bound hx.choose (fun u v => (hg u v).2.1) hn u a b hab
    (fun w hw => hpot (x.1 u w 0) (hrange w hw)) (fun w _ => (hg u w).2.2.2.2)
  change Real.exp (-(4 * P) * ((b : ℝ) - a)) * (x.1 u a 0 * (-N u a)) ≤ x.1 u b 0 * (-N u b) ∧
    x.1 u b 0 * (-N u b) ≤ Real.exp (4 * P * ((b : ℝ) - a)) * (x.1 u a 0 * (-N u a)) at hflux
  have hloExp : Real.exp (-(4 * P) * D) ≤ Real.exp (-(4 * P) * ((b : ℝ) - a)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left htime (neg_nonpos.2 (mul_nonneg (by norm_num) hP)))
  have hhiExp : Real.exp (4 * P * ((b : ℝ) - a)) ≤ Real.exp (4 * P * D) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htime (mul_nonneg (by norm_num) hP))
  have hNa : 0 ≤ -N u a := (neg_pos.2 (hn u a)).le
  have hNb : 0 ≤ -N u b := (neg_pos.2 (hn u b)).le
  have hlow : Y * Real.exp (-(4 * P) * D) * (-N u a) ≤ R * (-N u b) := calc
    _ ≤ Real.exp (-(4 * P) * D) * (x.1 u a 0 * (-N u a)) := by
      have hh := mul_le_mul_of_nonneg_right haR.1 (mul_nonneg (Real.exp_pos (-(4 * P) * D)).le hNa)
      nlinarith only [hh]
    _ ≤ Real.exp (-(4 * P) * ((b : ℝ) - a)) * (x.1 u a 0 * (-N u a)) :=
      mul_le_mul_of_nonneg_right hloExp (mul_nonneg (hg u a).2.1.le hNa)
    _ ≤ x.1 u b 0 * (-N u b) := hflux.1
    _ ≤ _ := mul_le_mul_of_nonneg_right hbR.2 hNb
  have hupp : Y * (-N u b) ≤ R * Real.exp (4 * P * D) * (-N u a) := calc
    _ ≤ x.1 u b 0 * (-N u b) := mul_le_mul_of_nonneg_right hbR.1 hNb
    _ ≤ Real.exp (4 * P * ((b : ℝ) - a)) * (x.1 u a 0 * (-N u a)) := hflux.2
    _ ≤ Real.exp (4 * P * D) * (x.1 u a 0 * (-N u a)) :=
      mul_le_mul_of_nonneg_right hhiExp (mul_nonneg (hg u a).2.1.le hNa)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right haR.2 (mul_nonneg (Real.exp_pos (4 * P * D)).le hNa)
      nlinarith only [hh]
  refine ⟨hl, htime, ?_, ?_⟩
  · have hh : (Y / R) * Real.exp (-(4 * P) * D) * (-N u a) ≤ -N u b := by
      apply (le_of_mul_le_mul_left ?_ hR0)
      calc
        R * ((Y / R) * Real.exp (-(4 * P) * D) * (-N u a)) = Y * Real.exp (-(4 * P) * D) * (-N u a) := by
          field_simp
        _ ≤ _ := hlow
    have hu := mul_le_mul_of_nonneg_left hh u.property.1
    nlinarith only [hu]
  · have hh : -N u b ≤ (R / Y) * Real.exp (4 * P * D) * (-N u a) := by
      apply (le_of_mul_le_mul_left ?_ hY0)
      calc
        Y * (-N u b) ≤ R * Real.exp (4 * P * D) * (-N u a) := hupp
        _ = Y * ((R / Y) * Real.exp (4 * P * D) * (-N u a)) := by field_simp
    have hu := mul_le_mul_of_nonneg_left hh u.property.1
    nlinarith only [hu]

theorem Background.exists_late_band_geometry (B : Background) {Y R s H dH A : ℝ}
    (hY : B.inner < Y) (hYR : Y ≤ R) (hR : R < B.event)
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ T q P : ℝ, 0 < U₀ ∧ U₀ ≤ r 0 / 4 ∧ 0 ≤ T ∧ 0 < q ∧ 0 ≤ P ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ U₀ →
        ∀ (u : Icc 0 U) (a b : Icc 0 V), T ≤ (a : ℝ) → a ≤ b → ∀ κ₀ : ℝ, 0 < κ₀ →
          let N := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let D := (R - Y) / (κ₀ * q)
          (∀ w ∈ Icc a b, x.1 u w 0 ∈ Icc Y R) →
          (∀ w ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) →
            (∀ w ∈ Icc a b, κ₀ * q ≤ -x.2.1 u w 0) ∧ (b : ℝ) - a ≤ D ∧
            (Y / R) * Real.exp (-(4 * P) * D) * ((u : ℝ) * (-N u a)) ≤ (u : ℝ) * (-N u b) ∧
            (u : ℝ) * (-N u b) ≤ (R / Y) * Real.exp (4 * P * D) * ((u : ℝ) * (-N u a)) := by
  obtain ⟨ε, q, P, hε, hq, hP, hband⟩ := B.exists_band_geometry hY hYR hR
  obtain ⟨U₀, T, hU₀, hU₀r, hT, hmass⟩ :=
    B.exists_late_mass_lower hs hH hdH hdHR hA hε hc hb hrc hrb hrd hrdec hOut
  refine ⟨U₀, T, q, P, hU₀, hU₀r, hT, hq, hP, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hUU u a b hTa hab κ₀ hk0
  dsimp only
  intro hrange hk
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  exact hband hU hV hUR hc (horizon_mass_integrable hs hH hc hb) hrc
    (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne') hφ hrd hp hf hx u a b hab κ₀ hk0 hrange hk
    (hmass U V hU hV hUR p hp f hf x hx hfn hUU u a hTa)

end CauchyHorizon
