import CauchyHorizon.Characteristic.ScalarEnergy
import CauchyHorizon.Characteristic.BandCoordinates

/-! Actual finite-window scalar energy on uniformly admitted compact radius bands. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_band_energy (B : Background) (hm : B.criticalExponent < 1) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h rH : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous rH) (hrb : ∀ t, B.event - dH ≤ rH t) (hrinit : B.inner < rH 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt rH
      (horizonFunction (rH t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖rH t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h rH s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ : ℝ, ∃ σ τ : Ioi (0 : ℝ) → ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧
          ∀ (p₀ : ℝ≥0∞) (hp₀ : 4 ≤ p₀) (f : ℝ → ℝ),
            MemLp f p₀ (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p₀ (volume.restrict (Icc 0 δ))).toReal ≤ A → ContDiffOn ℝ 1 f (Ioi 0) →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < rH 0), U ≤ U₀ →
              ∀ (hfU : MemLp f p₀ (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h rH 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp₀ hfU) x),
                ∀ (hUp : 0 < U) (l S : ℝ), σ ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                  let D := Icc (0 : ℝ) (Z - Y) ×ˢ Icc l S
                  let zIn := incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h rH 0)
                  let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
                  ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ D ∧
                    (∀ z ∈ D, χ z ∈ Ioo 0 U ∧
                      x.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 = Z - z.1) ∧
                    (∀ z ∈ D, z.2 ∈ Ioo 0 V) ∧
                    (∀ ε : Ioi (0 : ℝ), ∀ z ∈ D, τ ε ≤ z.2 →
                      |Real.log (B.outerRate * (χ z * ν (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) / B.F (Z - z.1)))| +
                        |x.2.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 /
                          (χ z * ν (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2)) - B.outerRate| < ε) ∧
                    ∀ P : ℝ → ℝ, ContDiffOn ℝ 1 P (Ioo 0 V) →
                      let u := fun z : ℝ × ℝ => projIcc 0 U hU (χ z)
                      let v := fun z : ℝ × ℝ => projIcc 0 V hV z.2
                      let ρ := fun z => x.1 (u z) (v z) 0
                      let n := fun z => ν (u z) (v z)
                      let L := fun z => x.2.1 (u z) (v z) 0
                      let ζ := fun z => zIn (u z) 0 * f (χ z) + scalarTransportCorrection hV ν x.2.1 (u z) (v z)
                      let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - y)
                      let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - y)
                      let p := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * (ρ z * x.2.1 (u z) (v z) 1) - X (ρ z) * P z.2
                      let q := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * χ z * ζ z / B.criticalWeight (ρ z) - W (ρ z) * P z.2
                      let α := fun z => L z / (ρ z * χ z * n z) * B.criticalWeight (ρ z)
                      let β := fun z => χ z * n z / (ρ z * L z) / B.criticalWeight (ρ z)
                      let c := fun z => -1 / L z
                      let d := fun z => B.innerRate * (c z - -1 / B.F (ρ z))
                      let S₁ := fun z => (L z / (ρ z * χ z * n z) - B.outerRate / ρ z) *
                        B.criticalWeight (ρ z) * W (ρ z) * P z.2
                      let S₂ := fun z => ((χ z * n z / (ρ z * L z) - 1 / (B.outerRate * ρ z)) /
                        B.criticalWeight (ρ z) * X (ρ z) + d z * W (ρ z)) * P z.2 - c z * W (ρ z) * deriv P z.2
                      let cv := fun z => (x.2.1 (u z) (v z) 2 -
                        radialSourceField B.charge B.cosmological x.1 x.2.1 ν hx.choose (u z) (v z) / n z) / L z -
                          ρ z * (x.2.1 (u z) (v z) 1) ^ 2 / (L z) ^ 2
                      let N := fun y => ∫ t in l..S, p (y, t) ^ 2 + q (y, t) ^ 2
                      ContinuousOn N (Icc 0 (Z - Y)) ∧
                        (∀ y ∈ Ioo 0 (Z - Y), HasDerivAt N
                          ((∫ t in l..S, 2 * (α (y, t) + β (y, t)) * p (y, t) * q (y, t) +
                            (2 * d (y, t) + cv (y, t)) * q (y, t) ^ 2 +
                            2 * S₁ (y, t) * p (y, t) + 2 * S₂ (y, t) * q (y, t)) +
                            c (y, l) * q (y, l) ^ 2 - c (y, S) * q (y, S) ^ 2) y) ∧
                        ContinuousOn S₁ D ∧ ContinuousOn S₂ D ∧
                        ∀ G : ℝ → ℝ, ContinuousOn G (Icc 0 (Z - Y)) →
                          (∀ z ∈ D, |α z + β z| + |2 * d z + cv z| ≤ G z.1) →
                          (∀ η : ℝ → ℝ, ContinuousOn η (Icc 0 (Z - Y)) → (∀ y ∈ Icc 0 (Z - Y), 0 < η y) →
                            N (Z - Y) ≤ (N 0 + ∫ y in (0 : ℝ)..(Z - Y), c (y, l) * q (y, l) ^ 2 +
                              (∫ t in l..S, S₁ (y, t) ^ 2 + S₂ (y, t) ^ 2) / η y) *
                                Real.exp (∫ y in (0 : ℝ)..(Z - Y), G y + η y)) ∧
                          Real.sqrt (N (Z - Y)) ≤
                            (Real.sqrt (N 0) + Real.sqrt (∫ y in (0 : ℝ)..(Z - Y), c (y, l) * q (y, l) ^ 2) +
                              ∫ y in (0 : ℝ)..(Z - Y), Real.sqrt (∫ t in l..S, S₁ (y, t) ^ 2 + S₂ (y, t) ^ 2)) *
                                Real.exp (((∫ y in (0 : ℝ)..(Z - Y), G y) + 1) / 2) := by
  intro hi hr0
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ := B.exists_band_coordinates
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, T, τ, σ, hU₀, hUδ, hT, _hτ, hσ, hsolve⟩ := hband Y Z hY hYZ hYR hZ
  let η : Ioi (0 : ℝ) := ⟨B.outerRate / 2, half_pos B.outerRate_pos⟩
  refine ⟨U₀, (fun W => max (σ W) (τ η)), τ, hU₀, hUδ, ?_⟩
  intro p₀ hp₀ f hf hfn hfc U V hU hV hUR hUU hfU x hx hUp l S hl hlS hSV D zIn ν
  have hσl := (le_max_left _ _).trans hl
  have hTl := (hσ ⟨U, hUp⟩).trans hσl
  obtain ⟨ψ, hψc, _hJc, hpoint⟩ :=
    hsolve p₀ hp₀ f hf hfn U V hU hV hUR hUU hfU x hx hUp l S hσl hlS hSV
  let K : (ℝ × ℝ) → (ℝ × ℝ) := fun z => (Z - z.1, z.2)
  let χ := ψ ∘ K
  have hKmap : MapsTo K D (Icc Y Z ×ˢ Icc l S) := by
    intro z hz
    exact ⟨⟨by dsimp [K]; linarith [hz.1.2], by dsimp [K]; linarith [hz.1.1]⟩, hz.2⟩
  have hχc : ContinuousOn χ D := hψc.comp (by fun_prop) hKmap
  have hχhit (z : ℝ × ℝ) (hz : z ∈ D) : χ z ∈ Ioo 0 U ∧
      x.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 = Z - z.1 :=
    ⟨(hpoint (K z) (hKmap hz)).1, (hpoint (K z) (hKmap hz)).2.1⟩
  refine ⟨χ, hχc, hχhit,
    (fun z hz => ⟨hT.trans_le (hTl.trans hz.2.1), hz.2.2.trans_lt hSV⟩), ?_, ?_⟩
  · intro ε z hz hε
    have hh := (hpoint (K z) (hKmap hz)).2.2.2 ε hε
    have drop {a b c ε : ℝ} (hh : a + b + c < ε) (hb : 0 ≤ b) : a + c < ε := by linarith only [hh, hb]
    exact drop hh (abs_nonneg _)
  intro P hP
  apply hx.radial_mode_energy B hm hU hV hUR hc hi hrc hr0 hφ hrd hp₀ hfU hfc hP
    (sub_nonneg.2 hYZ.le) hlS (R := Z) hχc
  intro z hz
  have hp := hpoint (K z) (hKmap hz)
  have hn : ν (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) < 0 :=
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp₀ hfU _ _).2.2.1
  have he := hp.2.2.2 η (((le_max_right _ _).trans hl).trans hz.2.1)
  have hN : χ z * ν (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) < 0 := mul_neg_of_pos_of_neg hp.1.1 hn
  have hspeed : 0 < x.2.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 /
      (χ z * ν (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2)) := by
    have he' := (abs_lt.1 ((le_add_of_nonneg_left
      (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans_lt he)).1
    change -(B.outerRate / 2) < x.2.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 /
      (χ z * ν (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2)) - B.outerRate at he'
    linarith only [he', B.outerRate_pos]
  have hneg := ((div_pos_iff.1 hspeed).resolve_left (fun h => (not_lt_of_ge hN.le) h.2)).1
  refine ⟨hp.1, ⟨hT.trans_le (hTl.trans hz.2.1), hz.2.2.trans_lt hSV⟩, hp.2.1, ?_, hneg, ?_⟩
  · change x.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 ∈ Ioo B.inner B.event
    rw [(hχhit z hz).2]
    exact ⟨hY.trans_le (hKmap hz).1.1, (hKmap hz).1.2.trans_lt hZ⟩
  · have hKd : HasFDerivAt K
        ((-ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.const_sub Z).prodMk
        (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    convert! hp.2.2.1.comp z hKd.hasFDerivWithinAt hKmap using 1
    apply ContinuousLinearMap.ext
    intro w
    change -(w.1 * _) - w.2 * _ = (-w.1) * _ - w.2 * _
    dsimp only [χ, K, Function.comp_apply]
    ring

end CauchyHorizon.Background
