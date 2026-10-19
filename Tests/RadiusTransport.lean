import CauchyHorizon.Characteristic.BandCoordinates
import CauchyHorizon.Characteristic.RadiusTransport

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Tests

-- The actual fixed-radius identity holds even at the endpoints of a closed time window.
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ : ℝ, ∃ σ : Ioi (0 : ℝ) → ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧
          ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
            (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl hfU) x),
                ∀ (hUp : 0 < U) (l S : ℝ), σ ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
                  ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ (Icc Y Z ×ˢ Icc l S) ∧
                    ∀ q ∈ Icc Y Z ×ˢ Icc l S,
                      let u := projIcc 0 U hU (χ q)
                      let v := projIcc 0 V hV q.2
                      let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) /
                        (4 * intervalExtension hV (ν u) t)
                      x.1 u v 0 = q.1 ∧ x.2.1 u v 0 < 0 ∧
                        HasDerivWithinAt
                          (fun t => -1 / intervalExtension hV (intervalExtension hU x.2.1 (χ (q.1, t))) t 0)
                          ((deriv κ q.2 / κ q.2) / x.2.1 u v 0 -
                            (x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2))
                          (Icc l S) q.2 := by
  intro hi hr0
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ := B.exists_band_coordinates
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, T, τ, σ, hU₀, hUδ, hT, _hτ, hσ, hsolve⟩ := hband Y Z hY hYZ hYR hZ
  let η : Ioi (0 : ℝ) := ⟨B.outerRate / 2, half_pos B.outerRate_pos⟩
  refine ⟨U₀, fun W => max (σ W) (τ η), hU₀, hUδ, ?_⟩
  intro f hf hfn U V hU hV hUR hUU hfU x hx hUp l S hl hlS hSV
  have hσl := (le_max_left _ _).trans hl
  have hTl := (hσ ⟨U, hUp⟩).trans hσl
  obtain ⟨χ, hχc, _hJc, hpoint⟩ :=
    hsolve 4 le_rfl f hf hfn U V hU hV hUR hUU hfU x hx hUp l S hσl hlS hSV
  refine ⟨χ, hχc, ?_⟩
  intro q hq
  have hp := hpoint q hq
  have hu : χ q ∈ Icc 0 U := ⟨hp.1.1.le, hp.1.2.le⟩
  have hv : q.2 ∈ Icc 0 V := ⟨hT.le.trans (hTl.trans hq.2.1), hq.2.2.trans hSV.le⟩
  let u : Icc 0 U := ⟨χ q, hu⟩
  let v : Icc 0 V := ⟨q.2, hv⟩
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
  have he := hp.2.2.2 η (((le_max_right _ _).trans hl).trans hq.2.1)
  rw [projIcc_of_mem hU hu, projIcc_of_mem hV hv] at hp he ⊢
  have hn : ν u v < 0 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hfU u v).2.2.1
  have hN : χ q * ν u v < 0 := mul_neg_of_pos_of_neg hp.1.1 hn
  have hspeed : 0 < x.2.1 u v 0 / (χ q * ν u v) := by
    have he' := (abs_lt.1 ((le_add_of_nonneg_left
      (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans_lt he)).1
    change -(B.outerRate / 2) < x.2.1 u v 0 / (χ q * ν u v) - B.outerRate at he'
    linarith only [he', B.outerRate_pos]
  have hneg : x.2.1 u v 0 < 0 :=
    ((div_pos_iff.1 hspeed).resolve_left (fun h => (not_lt_of_ge hN.le) h.2)).1
  have hg := hp.2.2.1.comp_hasDerivWithinAt q.2
    ((hasDerivWithinAt_const q.2 (Icc l S) q.1).prodMk (hasDerivWithinAt_id q.2 (Icc l S)))
    (show MapsTo (fun t : ℝ => (q.1, t)) (Icc l S) (Icc Y Z ×ˢ Icc l S) from fun _ ht => ⟨hq.1, ht⟩)
  have hg' : HasDerivWithinAt (fun t => χ (q.1, t)) (-x.2.1 u v 0 / ν u v) (Icc l S) (v : ℝ) := by
    simpa only [Function.comp_def, id_eq, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, zero_mul, one_mul, zero_sub, neg_div,
      projIcc_of_mem hU hu, projIcc_of_mem hV hv] using hg
  have hh := (hx.horizon_radius_transport hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hfU
    u v hp.1 ⟨hT.trans_le (hTl.trans hq.2.1), hq.2.2.trans_lt hSV⟩ hneg.ne).2
      (Icc l S) (fun t => χ (q.1, t)) rfl hg'
  exact ⟨hp.2.1, hneg, hh⟩

end CauchyHorizon.Tests
