import CauchyHorizon.Characteristic.BandCoordinates

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Tests

-- The outer endpoint can approach r_plus while lying strictly above the initial horizon radius.
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrinit : B.inner < r 0) (hrinitE : r 0 < B.event)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y : ℝ, 0 < δ ∧ Y ∈ Ioo B.inner B.event ∧
      ∀ cap : ℝ, 0 < cap → ∃ Z U₀ : ℝ, ∃ σ : Ioi (0 : ℝ) → ℝ,
        Y < Z ∧ r 0 < Z ∧ B.event - cap < Z ∧ Z < B.event ∧ 0 < U₀ ∧ U₀ ≤ δ ∧
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
                    χ q ∈ Ioo 0 U ∧ x.1 u v 0 = q.1 ∧
                      HasDerivWithinAt (fun y => χ (y, q.2)) (ν u v)⁻¹ (Icc Y Z) q.1 := by
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ := B.exists_band_coordinates
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro cap hcap
  let L := max R (max (r 0) (B.event - cap))
  have hLE : L < B.event := max_lt hR.2 (max_lt hrinitE (sub_lt_self _ hcap))
  let Z := (L + B.event) / 2
  have hLZ : L < Z := by dsimp only [Z]; linarith only [hLE]
  have hZ : Z < B.event := by dsimp only [Z]; linarith only [hLE]
  have hRZ : R < Z := (le_max_left _ _).trans_lt hLZ
  obtain ⟨U₀, _T, _τ, σ, hU₀, hUδ, _hT, _hτ, _hσ, hsolve⟩ := hband R Z hR.1 hRZ le_rfl hZ
  refine ⟨Z, U₀, σ, hRZ, ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hLZ,
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hLZ, hZ, hU₀, hUδ, ?_⟩
  intro f hf hfn U V hU hV hUR hUU hfU x hx hUp l S hσl hlS hSV
  obtain ⟨χ, hχc, _hJc, hpoint⟩ :=
    hsolve 4 le_rfl f hf hfn U V hU hV hUR hUU hfU x hx hUp l S hσl hlS hSV
  refine ⟨χ, hχc, ?_⟩
  intro q hq
  have hh := hpoint q hq
  refine ⟨hh.1, hh.2.1, ?_⟩
  have hd := hh.2.2.1.comp_hasDerivWithinAt q.1
    ((hasDerivWithinAt_id q.1 (Icc R Z)).prodMk (hasDerivWithinAt_const q.1 (Icc R Z) q.2))
    (show MapsTo (fun y : ℝ => (y, q.2)) (Icc R Z) (Icc R Z ×ˢ Icc l S) from fun _ hy => ⟨hy, hq.2⟩)
  simpa only [Function.comp_def, id_eq, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, zero_mul, one_mul, sub_zero] using hd

end CauchyHorizon.Tests
