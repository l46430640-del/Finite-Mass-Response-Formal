import CauchyHorizon.Characteristic.BandEnergy

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Tests

-- The coefficient in the energy theorem is exactly the one in BandTransportDecay.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (u : Icc 0 U) (v : Icc 0 V) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hn : radialNuField hV e Λ zIn x.1 hx.choose u v ≠ 0) (hl : x.2.1 u v 0 ≠ 0) :
    let ν := radialNuField hV e Λ zIn x.1 hx.choose
    let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) /
      (4 * intervalExtension hV (ν u) t)
    |(x.2.1 u v 2 - radialSourceField e Λ x.1 x.2.1 ν hx.choose u v / ν u v) / x.2.1 u v 0 -
      x.1 u v 0 * (x.2.1 u v 1) ^ 2 / (x.2.1 u v 0) ^ 2| =
        |(deriv κ v / κ v) / x.2.1 u v 0 -
          (x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2)| :=
  congrArg abs (hx.inverse_lambda_coefficient_eq u v hv hn hl)

-- Critical data and the nonconstant envelope P(t)=t use one chart on the entire window.
example (B : Background) (hm : B.criticalExponent < 1) {s H dH A : ℝ}
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
        ∃ U₀ : ℝ, ∃ σ : Ioi (0 : ℝ) → ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧
          ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
            (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A → ContDiffOn ℝ 1 f (Ioi 0) →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < rH 0), U ≤ U₀ →
              ∀ (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h rH 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl hfU) x),
                ∀ (hUp : 0 < U) (l S : ℝ), σ ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                  let D := Icc (0 : ℝ) (Z - Y) ×ˢ Icc l S
                  let zIn := incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h rH 0)
                  let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
                  ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ D ∧
                    (∀ z ∈ D, χ z ∈ Ioo 0 U ∧
                      x.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 = Z - z.1) ∧
                    let u := fun z : ℝ × ℝ => projIcc 0 U hU (χ z)
                    let v := fun z : ℝ × ℝ => projIcc 0 V hV z.2
                    let ρ := fun z => x.1 (u z) (v z) 0
                    let ζ := fun z => zIn (u z) 0 * f (χ z) + scalarTransportCorrection hV ν x.2.1 (u z) (v z)
                    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - y)
                    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - y)
                    let p := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * (ρ z * x.2.1 (u z) (v z) 1) - X (ρ z) * z.2
                    let q := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * χ z * ζ z / B.criticalWeight (ρ z) - W (ρ z) * z.2
                    let N := fun y => ∫ t in l..S, p (y, t) ^ 2 + q (y, t) ^ 2
                    ContinuousOn N (Icc 0 (Z - Y)) ∧ DifferentiableOn ℝ N (Ioo 0 (Z - Y)) := by
  intro hi hr0
  obtain ⟨δ, R, hδ, hR, hband⟩ := B.exists_band_energy hm
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, σ, _τ, hU₀, hUδ, hsolve⟩ := hband Y Z hY hYZ hYR hZ
  refine ⟨U₀, σ, hU₀, hUδ, ?_⟩
  intro f hf hfn hfc U V hU hV hUR hUU hfU x hx hUp l S hl hlS hSV D zIn ν
  obtain ⟨χ, hχc, hχ, _ht, _hnorm, he⟩ := hsolve 4 le_rfl f hf hfn hfc U V hU hV hUR hUU hfU x hx hUp l S hl hlS hSV
  have hh := he id contDiffOn_id
  exact ⟨χ, hχc, hχ, hh.1, fun y hy => (hh.2.1 y hy).differentiableAt.differentiableWithinAt⟩

end CauchyHorizon.Tests
