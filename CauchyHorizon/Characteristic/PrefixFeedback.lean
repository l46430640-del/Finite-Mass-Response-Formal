import CauchyHorizon.Characteristic.MatchingFeedback

/-! Transfer the pre-entry energy through the continuous lapse, not rough derivative traces. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_prefix_feedback_decay (B : Background) {s H dH A ρ D c : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hρ : 0 < ρ) (hρR : ρ ≤ B.event + dH) (hD : 0 ≤ D)
    (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ C E : ℝ, 0 < U₀ ∧ U₀ ≤ r 0 / 4 ∧ 0 ≤ C ∧ 0 ≤ E ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → c ≤ B.outerRate * (1 - 1 / p.toReal) →
        ∀ z : Icc 0 U, (z : ℝ) ≤ U₀ → (∀ w ≤ z, ∀ v, ρ ≤ x.1 w v 0) →
          (z : ℝ) * Real.exp (B.outerRate * V) ≤ D →
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let v : Icc 0 V := ⟨V, hV, le_rfl⟩
          (∫ t in (0 : ℝ)..z, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
            (-intervalExtension hU ν t v)) ≤ C * Real.exp (-(min B.outerRate (2 * c)) * V) ∧
          ∀ w ≤ z, |x.2.1 w v 1| ≤ E * Real.exp (-c * V) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let R := B.event + dH
  have hR : 0 ≤ R := hρ.le.trans hρR
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  obtain ⟨U₀, n, N, L, hU₀, hU₀r, hn, hN, hL, hgeom⟩ :=
    B.exists_bounded_width_geometry (D := D) hs hH hdH hdHR hA hρ hρR hc hb hrc hrb hrd hrdec hOut
  obtain ⟨C₀, D₀, hC₀, hD₀, hfeedback⟩ := exists_weighted_feedback_envelope hc hi hrc hr0 hφ hrd
    hc0 hca hρ hR hn hN.le hL hH hA hD
  let E := ((H + L * (r 0 / ρ) * (A * max 1 D)) / ρ) *
    Real.exp (L * N * D / (ρ ^ 2 * (B.outerRate - c)))
  refine ⟨U₀, C₀ + D₀, E, hU₀, hU₀r, add_nonneg hC₀ hD₀, by dsimp only [E]; positivity, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb z hz hlo hwidth
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
  let τ := intervalTranslate (a := 0) (U := (z : ℝ)) le_rfl (by simpa using z.property.2)
  let hfz := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl z.property.2) le_rfl)
  let y := waveTranslate (a := 0) (U := (z : ℝ)) (b := 0) (V := V) le_rfl
    (by simpa using z.property.2) le_rfl (by simp) x
  have hy := hx.horizon_prefix hU hV hUR z.property.1 hV z.property.2 le_rfl hc hi hrc hr0 hp hf
  have hzy : y.1 = x.1.comp τ := by
    ext q w i
    change x.1 (τ q) (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by simp) w) i = x.1 (τ q) w i
    rw [intervalTranslate_zero, ContinuousMap.id_apply]
  have hwy (q : Icc 0 (z : ℝ)) (w : Icc 0 V) : y.2.1 q w = x.2.1 (τ q) w := by
    change x.2.1 (τ q) (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by simp) w) = _
    rw [intervalTranslate_zero, ContinuousMap.id_apply]
  let νy := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve z.property.1 (z.property.2.trans_lt hUR) hp hfz (horizonPhi h r 0)) y.1 hy.choose
  have hny : νy = ν.comp τ := by
    have hzi : (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)).comp τ =
        incomingWaveCurve z.property.1 (z.property.2.trans_lt hUR) hp hfz (horizonPhi h r 0) :=
      incomingWaveCurve_prefix hU z.property.1 hUR z.property.2 hp hf hfz _
    simpa only [νy, ν, hzi, ← hzy] using
      radialNuField_comp_left hV B.charge B.cosmological
        (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose τ
  have hloy (q : Icc 0 (z : ℝ)) (w : Icc 0 V) : ρ ≤ y.1 q w 0 := by
    rw [hzy]
    exact hlo (τ q) (by change 0 + (q : ℝ) ≤ z; simpa only [zero_add] using q.property.2) w
  have hfnz := (scalar_prefix_norm_le z.property.2 hf).trans hfn
  have hg := hgeom z V z.property.1 hV (z.property.2.trans_lt hUR) p hp f hfz y hy hfnz hz hloy hwidth
  have hnhi (q : Icc 0 (z : ℝ)) (w : Icc 0 V) : |νy q w| ≤ N * Real.exp (B.outerRate * w) := by
    rw [abs_of_neg (hy.interior_gauge z.property.1 hV (z.property.2.trans_lt hUR)
      hc hi hrc hr0 hφ hrd hp hfz q w).2.2.1]
    exact (hg q w).2.2.2
  have hout (w : Icc 0 V) : Real.exp (c * w) * |h w| ≤ H := by
    have hh := mul_le_mul_of_nonneg_left (hb w) (Real.exp_pos (c * w)).le
    rw [Real.norm_eq_abs] at hh
    have he : Real.exp (c * w) * Real.exp (-s * w) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith only [mul_nonneg (sub_nonneg.2 hcs) w.property.1]
    nlinarith only [hh, mul_le_mul_of_nonneg_left he hH]
  let top : Icc 0 (z : ℝ) := ⟨z, z.property.1, le_rfl⟩
  have htop : τ top = z := Subtype.ext (zero_add _)
  have hk := (hfeedback z V z.property.1 hV (z.property.2.trans_lt hUR) p hp f hfz y hy hfnz hcb hloy
    (fun q w => (hg q w).1) (fun q w => (hg q w).2.2.1) hnhi (fun q w => (hg q w).2.1) hout hwidth top).2.1
  change Real.exp (-(C₀ * Real.exp (-B.outerRate * V) + D₀ * Real.exp (-(2 * c) * V))) ≤
    -Real.exp (y.1 top v 2) / (4 * νy top v) at hk
  rw [hzy, hny] at hk
  simp only [ContinuousMap.comp_apply, htop] at hk
  rw [(hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd hp hf v).2 z] at hk
  have hQ := neg_le_neg (Real.exp_le_exp.mp hk)
  simp only [neg_neg] at hQ
  have he (q : ℝ) (hq : min B.outerRate (2 * c) ≤ q) :
      Real.exp (-q * V) ≤ Real.exp (-(min B.outerRate (2 * c)) * V) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hq) hV)
  refine ⟨hQ.trans ?_, ?_⟩
  · have hh := add_le_add (mul_le_mul_of_nonneg_left (he _ (min_le_left _ _)) hC₀)
      (mul_le_mul_of_nonneg_left (he _ (min_le_right _ _)) hD₀)
    simpa only [add_mul] using hh
  · have hscalar := (hy.horizon_weighted_scalar z.property.1 hV (z.property.2.trans_lt hUR)
      hc hi hrc hr0 hφ hrd hp hfz hA hfnz hc0.le hca hcb hρ hN.le hL hH hD hloy
      hnhi (fun q w => (hg q w).2.1) hout hwidth).1
    intro w hw
    have hh := hscalar ⟨w, w.property.1, hw⟩ v
    rw [hwy] at hh
    have ht : τ ⟨w, w.property.1, hw⟩ = w := Subtype.ext (zero_add _)
    simpa only [ht] using hh

end CauchyHorizon.Background
