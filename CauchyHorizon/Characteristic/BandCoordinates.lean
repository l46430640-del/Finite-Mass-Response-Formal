import CauchyHorizon.Characteristic.BandToEvent
import CauchyHorizon.Reduced.RadialCoordinates

/-! Jointly regular radius coordinates on actual compact band windows. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_band_coordinates (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ T : ℝ, ∃ τ σ : Ioi (0 : ℝ) → ℝ,
          0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ (∀ ε, T ≤ τ ε) ∧ (∀ W, T ≤ σ W) ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
            MemLp f p (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
                ∀ (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
                  (hx : IsWaveIntegral hU hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR hp hfU) x),
                  ∀ (hUp : 0 < U) (l S : ℝ), σ ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                    let D := Icc Y Z ×ˢ Icc l S
                    let ν := radialNuField hV B.charge B.cosmological
                      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                    ∃ χ : ℝ × ℝ → ℝ,
                      let J := fun q : ℝ × ℝ =>
                        let u := projIcc 0 U hU (χ q)
                        let v := projIcc 0 V hV q.2
                        (ContinuousLinearMap.toSpanSingleton ℝ (ν u v)⁻¹).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
                          (ContinuousLinearMap.toSpanSingleton ℝ (x.2.1 u v 0 / ν u v)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
                      ContinuousOn χ D ∧ ContinuousOn J D ∧ ∀ q ∈ D,
                        let u := projIcc 0 U hU (χ q)
                        let v := projIcc 0 V hV q.2
                        χ q ∈ Ioo 0 U ∧ x.1 u v 0 = q.1 ∧ HasFDerivWithinAt χ (J q) D q ∧
                          ∀ ε : Ioi (0 : ℝ), τ ε ≤ q.2 →
                            |Real.log (B.outerRate * (χ q * ν u v / B.F q.1))| +
                              |Real.log (B.z q.1 / (χ q * (cν * Real.exp (B.outerRate * q.2))))| +
                                |x.2.1 u v 0 / (χ q * ν u v) - B.outerRate| < ε := by
  classical
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, hδr, hR, hband⟩ := B.exists_band_normalization_to_event
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, T, τ, σ, hU₀, hUδ, hT, hτ, hσ, hsolve⟩ := hband Y Z hY hYZ hYR hZ
  refine ⟨U₀, T, τ, σ, hU₀, hUδ, hT, hτ, hσ, ?_⟩
  intro p hp f hf hfn
  obtain ⟨gY, _hYc, hYa, _hYl, _hpos, hentry, hphysical⟩ := hsolve p hp f hf hfn
  intro U V hU hV hUR hUU hfU x hx hUp l S hσl hlS hSV
  have hTl : T ≤ l := (hσ ⟨U, hUp⟩).trans hσl
  have hYlU := hentry ⟨U, hUp⟩ l hσl
  let D := Icc Y Z ×ˢ Icc l S
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
  have hphys := hphysical U V hU hV hUR hUU hfU x hx
  have htime (q : ℝ × ℝ) (hq : q ∈ D) : q.2 ∈ Ioo 0 V :=
    ⟨hT.trans_le (hTl.trans hq.2.1), hq.2.2.trans_lt hSV⟩
  have hmem (q : ℝ × ℝ) (hq : q ∈ D) : q.2 ∈ Icc 0 V := ⟨(htime q hq).1.le, (htime q hq).2.le⟩
  have hpre (q : ℝ × ℝ) (hq : q ∈ D) : ∃ u : Icc 0 U,
      0 < (u : ℝ) ∧ (u : ℝ) ≤ gY q.2 ∧ x.1 u ⟨q.2, hmem q hq⟩ 0 = q.1 := by
    have hYq := (hYa.antitoneOn hTl (hTl.trans hq.2.1) hq.2.1).trans_lt hYlU
    exact (hphys.1 ⟨q.2, hmem q hq⟩ (hTl.trans hq.2.1) hYq.le q.1 hq.1).exists
  let χ := fun q : ℝ × ℝ => if hq : q ∈ D then ((hpre q hq).choose : ℝ) else 0
  have hχ (q : ℝ × ℝ) (hq : q ∈ D) : χ q ∈ Ioo 0 U ∧
      χ q ≤ gY q.2 ∧
      intervalExtension hV (intervalExtension hU x.1 (χ q)) q.2 0 = q.1 := by
    have hh := (hpre q hq).choose_spec
    have hhigh := hh.2.1.trans_lt ((hYa.antitoneOn hTl (hTl.trans hq.2.1) hq.2.1).trans_lt hYlU)
    dsimp only [χ]
    rw [dif_pos hq]
    refine ⟨⟨hh.1, hhigh⟩, hh.2.1, ?_⟩
    simpa only [intervalExtension_apply, projIcc_of_mem hU (hpre q hq).choose.property,
      projIcc_of_mem hV (hmem q hq)] using hh.2.2
  have hregular := hx.radial_coordinates_regular hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hfU (horizonPhi h r 0)).1
    (fun u v => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU u v).2.2.1)
    (fun q hq => ⟨(hχ q hq).1, htime q hq, (hχ q hq).2.2⟩)
  refine ⟨χ, hregular.1, hregular.2.1, ?_⟩
  intro q hq
  have hh := hχ q hq
  have hu : χ q ∈ Icc 0 U := ⟨hh.1.1.le, hh.1.2.le⟩
  have hv := hmem q hq
  have hhit : x.1 (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2) 0 = q.1 := hh.2.2
  refine ⟨hh.1, hhit, hregular.2.2 q hq, ?_⟩
  intro ε hε
  rw [projIcc_of_mem hU hu, projIcc_of_mem hV hv] at hhit ⊢
  have herr := (hphys.2 ⟨χ q, hu⟩ ⟨q.2, hv⟩ (hTl.trans hq.2.1) hh.2.1
    (hhit.trans_le hq.1.2)).2 ε hε
  rw [hhit] at herr
  exact herr

end CauchyHorizon.Background
