import CauchyHorizon.Characteristic.BandTransportDecay

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Tests

-- One late cutoff controls the actual derivatives for every critical profile.
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
        ∃ U₀ d : ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < d ∧
          ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
            ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
              (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
                ∀ (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                  (hx : IsWaveIntegral hU hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR le_rfl hfU) x),
                  ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ∈ Ioo 0 U → (v : ℝ) ∈ Ioo 0 V →
                    T ≤ (v : ℝ) → x.1 u v 0 ∈ Icc Y Z →
                    let ν := radialNuField hV B.charge B.cosmological
                      (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
                    let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) /
                      (4 * intervalExtension hV (ν u) t)
                    let cv := (deriv κ v / κ v) / x.2.1 u v 0 -
                      (x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2)
                    x.2.1 u v 0 ≤ -d ∧ |deriv κ v / κ v| + |cv| < ε ∧
                      ∀ (S : Set ℝ) (g : ℝ → ℝ), g v = u →
                        HasDerivWithinAt g (-x.2.1 u v 0 / ν u v) S v →
                        HasDerivWithinAt
                          (fun t => -1 / intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 0) cv S v := by
  intro hi hr0
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ := B.exists_band_transport_decay
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, C, d, γ, T₀, hU₀, hUδ, _hC, hd, hγ, hT₀, hdecay⟩ := hband Y Z hY hYZ hYR hZ
  refine ⟨U₀, d, hU₀, hUδ, hd, ?_⟩
  intro ε hε
  have hzero : Tendsto (fun t : ℝ => C * Real.exp (-γ * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hγ))).const_mul C
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hzero.eventually_lt_const hε)
  refine ⟨max T₀ T, hT₀.trans_le (le_max_left _ _), ?_⟩
  intro f hf hfn U V hU hV hUR hUU hfU x hx u v hu hv hTv hrband
  have hh := hdecay 4 le_rfl f hf hfn U V hU hV hUR hUU hfU x hx u v hu hv
    ((le_max_left _ _).trans hTv) hrband
  exact ⟨hh.1, hh.2.1.trans_lt (hT v ((le_max_right _ _).trans hTv)), hh.2.2⟩

end CauchyHorizon.Tests
