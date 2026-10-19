import CauchyHorizon.Characteristic.MatchedBand

open Set MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace CauchyHorizon.Tests

-- The critical power need not be smooth at zero to be C1 on the required positive-u domain.
example (ℓ : ℝ) : ContDiffOn ℝ 1
    (fun u : ℝ => (3 / 4 : ℝ) * u ^ ((3 / 4 : ℝ) - 1) * (ℓ - Real.log u)) (Ioi 0) := by
  simpa only [logarithmicIncoming, id_eq] using! logarithmicIncoming_contDiff contDiff_id (3 / 4) ℓ

-- At the critical p=4 exponent, no extra profile-regularity or radius-matching premise remains.
example (B : Background) (hcrit : B.criticalExponent = 3 / 4) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hks : B.innerRate < s)
    {h rH : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous rH) (hrb : ∀ t, B.event - dH ≤ rH t) (hrinit : B.inner < rH 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt rH
      (horizonFunction (rH t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖rH t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h rH s) :
    let b := B.criticalExponent
    let hm : B.criticalExponent < 1 := by rw [hcrit]; norm_num
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (rH t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    let Ch := rH 0 / (B.event * cν ^ b)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y cap e : ℝ, B.inner < Y → Y ≤ R → 0 < cap → 0 < e →
        ∃ Z U₀ C L : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ,
          Z ∈ Ioo Y B.event ∧ B.event - cap < Z ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < C ∧ 0 < L ∧
          ∀ (ℓ : ℝ) (P Q : ℝ →ᵇ ℝ), Integrable (fun t => P t ^ 2) →
            (∀ t, HasDerivAt P (Q t) t) → Integrable (fun t => Q t ^ 2) →
            MemLp (logarithmicIncoming b ℓ P) 4 (volume.restrict (Icc 0 δ)) →
            (eLpNorm (logarithmicIncoming b ℓ P) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < rH 0), U ≤ U₀ →
              ∀ (hfU : MemLp (logarithmicIncoming b ℓ P) 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h rH 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl hfU) x),
                ∀ (ε : Ioi (0 : ℝ)) (hUp : 0 < U) (l S : ℝ), τ ε ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                  let D := Icc (0 : ℝ) (Z - Y) ×ˢ Icc l S
                  let zIn := incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h rH 0)
                  let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
                  ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ D ∧
                    (∀ z ∈ D, χ z ∈ Ioo 0 U ∧
                      x.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 = Z - z.1) ∧
                    let u := fun z : ℝ × ℝ => projIcc 0 U hU (χ z)
                    let v := fun z : ℝ × ℝ => projIcc 0 V hV z.2
                    let ρ := fun z => x.1 (u z) (v z) 0
                    let Lm := fun z => x.2.1 (u z) (v z) 0
                    let ζ := fun z => zIn (u z) 0 * logarithmicIncoming b ℓ P (χ z) + scalarTransportCorrection hV ν x.2.1 (u z) (v z)
                    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - y)
                    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - y)
                    let φ := fun t => B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Z)
                    let P₀ := fun t => Ch * P (φ t)
                    let p := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * (ρ z * x.2.1 (u z) (v z) 1) - X (ρ z) * P₀ z.2
                    let q := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * χ z * ζ z / B.criticalWeight (ρ z) - W (ρ z) * P₀ z.2
                    let N := fun y => ∫ t in l..S, p (y, t) ^ 2 + q (y, t) ^ 2
                    Real.sqrt (N (Z - Y)) ≤
                      (Real.sqrt (e * (1 + ∫ t, P t ^ 2) + L * ∫ t, Q t ^ 2) +
                        Real.sqrt (∫ y in (0 : ℝ)..(Z - Y), (-1 / Lm (y, l)) * q (y, l) ^ 2) +
                        (Z - Y) * Real.sqrt (2 * (ε : ℝ) ^ 2 * (Ch ^ 2 / B.outerRate * ∫ t, P t ^ 2) +
                          2 * C ^ 2 * (Ch ^ 2 * B.outerRate * ∫ t, Q t ^ 2))) *
                            Real.exp (((∫ r in B.inner..B.event, B.energyGrowth r) + (ε : ℝ) * (Z - Y) + 1) / 2) := by
  intro b hm hi hr0 cν Ch
  have hk : B.innerRate ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    have hh := (div_eq_iff B.outerRate_pos.ne').1 hcrit
    norm_num
    linarith only [hh]
  obtain ⟨δ, R, hδ, hR, hband⟩ := B.exists_matched_band_energy hs hH hdH hdHR hA hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y cap e hY hYR hcap he
  obtain ⟨Z, U₀, C, L, τ, hZ, hcapZ, hU₀, hUδ, hC, hL, hsolve⟩ := hband Y cap e hY hYR hcap he
  refine ⟨Z, U₀, C, L, τ, hZ, hcapZ, hU₀, hUδ, hC, hL, ?_⟩
  intro ℓ P Q hPi hPQ hQi hf hfn
  exact hsolve 4 le_rfl ℓ P Q hk hPi hPQ hQi hf hfn

end CauchyHorizon.Tests
