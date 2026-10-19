import CauchyHorizon.Characteristic.BandGrowth

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Tests

-- The same finite reference integral bounds every radial truncation.
example (B : Background) (hm : B.criticalExponent < 1) {Y Z : ℝ}
    (hY : B.inner ≤ Y) (hYZ : Y ≤ Z) (hZ : Z ≤ B.event) :
    (∫ r in Y..Z, B.energyGrowth r) ≤ ∫ r in B.inner..B.event, B.energyGrowth r := by
  have hh := B.energyGrowth_regular hm
  exact intervalIntegral.integral_mono_interval hY hYZ hZ
    ((ae_restrict_mem measurableSet_Ioc).mono (fun r hr => hh.2.2 r ⟨hr.1.le, hr.2⟩)) hh.2.1

-- At p=4, eta=1 and zero comparison envelope, the actual energy needs no majorant premise.
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
        ∃ U₀ : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧
          ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
            (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A → ContDiffOn ℝ 1 f (Ioi 0) →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < rH 0), U ≤ U₀ →
              ∀ (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
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
                    let L := fun z => x.2.1 (u z) (v z) 0
                    let ζ := fun z => zIn (u z) 0 * f (χ z) + scalarTransportCorrection hV ν x.2.1 (u z) (v z)
                    let p := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * (ρ z * x.2.1 (u z) (v z) 1)
                    let q := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * χ z * ζ z / B.criticalWeight (ρ z)
                    let N := fun y => ∫ t in l..S, p (y, t) ^ 2 + q (y, t) ^ 2
                    N (Z - Y) ≤ (N 0 + ∫ y in (0 : ℝ)..(Z - Y), (-1 / L (y, l)) * q (y, l) ^ 2) *
                      Real.exp (∫ y in (0 : ℝ)..(Z - Y), B.energyGrowth (Z - y) + (ε : ℝ) + 1) ∧
                    Real.sqrt (N (Z - Y)) ≤
                      (Real.sqrt (N 0) + Real.sqrt (∫ y in (0 : ℝ)..(Z - Y), (-1 / L (y, l)) * q (y, l) ^ 2)) *
                        Real.exp (((∫ r in B.inner..B.event, B.energyGrowth r) + (ε : ℝ) * (Z - Y) + 1) / 2) := by
  intro hi hr0
  obtain ⟨δ, R, hδ, hR, hband⟩ := B.exists_band_reference_energy hm
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, _C, τ, hU₀, hUδ, _hC, hsolve⟩ := hband Y Z hY hYZ hYR hZ
  refine ⟨U₀, τ, hU₀, hUδ, ?_⟩
  intro f hf hfn hfc U V hU hV hUR hUU hfU x hx ε hUp l S hl hlS hSV D zIn ν
  obtain ⟨χ, hχc, hχ, he⟩ := hsolve 4 le_rfl f hf hfn hfc U V hU hV hUR hUU hfU x hx ε hUp l S hl hlS hSV
  refine ⟨χ, hχc, hχ, ?_⟩
  have hh := he (fun _ => 0) contDiffOn_const
  constructor
  · simpa only [mul_zero, sub_zero, deriv_const, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, intervalIntegral.integral_zero, zero_div] using
      hh.1 (fun _ => 1) continuousOn_const (fun _ _ => zero_lt_one)
  · simpa only [mul_zero, sub_zero, deriv_const, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, intervalIntegral.integral_zero, Real.sqrt_zero] using hh.2.1

end CauchyHorizon.Tests
