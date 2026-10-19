import CauchyHorizon.Reduced.ScalarCoordinates
import CauchyHorizon.Characteristic.BandCoordinates

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Tests

-- The actual critical data give joint C1 regularity; vOut is only continuous.
example {U V R e Λ φ₀ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    (hfc : ContDiffOn ℝ 1 f (Ioi 0)) (vOut : C(Icc 0 V, WaveVector)) (x : WaveState U V)
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) :
    let zIn := incomingWaveCurve hU hUR le_rfl hf φ₀
    let ν := radialNuField hV e Λ zIn x.1 hx.choose
    let ζ := fun z : ℝ × ℝ => zIn (projIcc 0 U hU z.1) 0 * f z.1 +
      scalarTransportCorrection hV ν x.2.1 (projIcc 0 U hU z.1) (projIcc 0 V hV z.2)
    ContDiffOn ℝ 1 ζ (Ioo 0 U ×ˢ Ioo 0 V) := by
  have hF : ContinuousOn (incomingVelocity R f) (Ioi 0) := by
    have hc := hfc.continuousOn
    unfold incomingVelocity
    fun_prop
  exact (hx.scalar_joint_contDiff rfl (incomingWave_constraint_data hU hUR le_rfl hf φ₀).1
    hF (incomingWaveVelocity_ae hUR le_rfl hf) hfc).2

-- BandCoordinates supplies the chart, its orientation, and nonzero speeds before every profile.
set_option maxHeartbeats 1600000 in
example (B : Background) (hm : B.criticalExponent < 1) {s H dH A : ℝ}
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
            (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A → ContDiffOn ℝ 1 f (Ioi 0) →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl hfU) x),
                ∀ (hUp : 0 < U) (l S : ℝ), σ ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
                  ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ (Icc 0 (Z - Y) ×ˢ Icc l S) ∧
                    (∀ z ∈ Icc 0 (Z - Y) ×ˢ Icc l S,
                      χ z ∈ Ioo 0 U ∧ x.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 = Z - z.1) ∧
                    let n := fun z : ℝ × ℝ => ν (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2)
                    let L := fun z : ℝ × ℝ => x.2.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0
                    let ζ := fun z : ℝ × ℝ => (r 0 - χ z) * f (χ z) +
                      scalarTransportCorrection hV ν x.2.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2)
                    let p := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) *
                      ((Z - z.1) * x.2.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 1)
                    let q := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * χ z * ζ z / B.criticalWeight (Z - z.1)
                    ContinuousOn p (Icc 0 (Z - Y) ×ˢ Icc l S) ∧
                      ContinuousOn q (Icc 0 (Z - Y) ×ˢ Icc l S) ∧
                      ∃ qv : ℝ × ℝ → ℝ, ContinuousOn qv (Icc 0 (Z - Y) ×ˢ Icc l S) ∧
                        (∀ y ∈ Ioo 0 (Z - Y), ∀ t ∈ Icc l S,
                          HasDerivAt (fun w => p (w, t))
                            (L (y, t) / ((Z - y) * χ (y, t) * n (y, t)) * B.criticalWeight (Z - y) * q (y, t)) y ∧
                          HasDerivAt (fun w => q (w, t))
                            (χ (y, t) * n (y, t) / ((Z - y) * L (y, t)) / B.criticalWeight (Z - y) * p (y, t) +
                              B.innerRate * (-1 / L (y, t) - -1 / B.F (Z - y)) * q (y, t) -
                              (-1 / L (y, t)) * qv (y, t)) y) ∧
                        ∀ y ∈ Icc 0 (Z - Y), ∀ t ∈ Icc l S,
                          HasDerivWithinAt (fun v => q (y, v)) (qv (y, t)) (Icc l S) t := by
  intro hi hr0
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ := B.exists_band_coordinates
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, T, τ, σ, hU₀, hUδ, hT, _hτ, hσ, hsolve⟩ := hband Y Z hY hYZ hYR hZ
  let η : Ioi (0 : ℝ) := ⟨B.outerRate / 2, half_pos B.outerRate_pos⟩
  refine ⟨U₀, fun W => max (σ W) (τ η), hU₀, hUδ, ?_⟩
  intro f hf hfn hfc U V hU hV hUR hUU hfU x hx hUp l S hl hlS hSV ν
  have hσl := (le_max_left _ _).trans hl
  have hTl := (hσ ⟨U, hUp⟩).trans hσl
  obtain ⟨ψ, hψc, _hJc, hpoint⟩ :=
    hsolve 4 le_rfl f hf hfn U V hU hV hUR hUU hfU x hx hUp l S hσl hlS hSV
  let D := Icc (0 : ℝ) (Z - Y) ×ˢ Icc l S
  let K : (ℝ × ℝ) → (ℝ × ℝ) := fun z => (Z - z.1, z.2)
  let χ := ψ ∘ K
  have hKmap : MapsTo K D (Icc Y Z ×ˢ Icc l S) := by
    intro z hz
    exact ⟨⟨by dsimp [K]; linarith [hz.1.2], by dsimp [K]; linarith [hz.1.1]⟩, hz.2⟩
  have hχc : ContinuousOn χ D := hψc.comp (by fun_prop) hKmap
  have hχhit (z : ℝ × ℝ) (hz : z ∈ D) : χ z ∈ Ioo 0 U ∧
      x.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 = Z - z.1 :=
    ⟨(hpoint (K z) (hKmap hz)).1, (hpoint (K z) (hKmap hz)).2.1⟩
  have hF : ContinuousOn (incomingVelocity (r 0) f) (Ioi 0) := by
    have hh := hfc.continuousOn
    unfold incomingVelocity
    fun_prop
  have htransport := hx.radial_mode_coordinate_transport B hm rfl
    (incomingWave_constraint_data hU hUR le_rfl hfU (horizonPhi h r 0)).1
    hF (incomingWaveVelocity_ae hUR le_rfl hfU) hfc (H := fun _ => 0) contDiffOn_const
    (R := Z) hχc
  have hh := htransport (by
    intro z hz
    have hp := hpoint (K z) (hKmap hz)
    have hn : ν (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) < 0 :=
      (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hfU _ _).2.2.1
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
    refine ⟨hp.1, ⟨hT.trans_le (hTl.trans hz.2.1), hz.2.2.trans_lt hSV⟩, hp.2.1,
      ?_, hn.ne, hneg.ne, ?_⟩
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
      ring)
  refine ⟨χ, hχc, hχhit, ?_⟩
  -- Replace chart radii and initial radii only on the closed physical window.
  have hin (z : ℝ × ℝ) (hz : z ∈ D) :
      incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0) (projIcc 0 U hU (χ z)) 0 = r 0 - χ z := by
    rw [incomingWaveCurve_apply, projIcc_of_mem hU ⟨(hχhit z hz).1.1.le, (hχhit z hz).1.2.le⟩]
    rfl
  simp only [mul_zero, sub_zero, deriv_const, add_zero] at hh
  obtain ⟨hp, hq, qv, hqv, hspace, htime⟩ := hh
  refine ⟨?_, ?_, qv, hqv, ?_, ?_⟩
  · exact hp.congr (fun z hz => by simp only [(hχhit z hz).2])
  · exact hq.congr (fun z hz => by simp only [(hχhit z hz).2, hin z hz]; rfl)
  · intro y hy t ht
    have hz : (y, t) ∈ D := ⟨⟨hy.1.le, hy.2.le⟩, ht⟩
    have hh := hspace y hy t ht
    rw [(hχhit (y, t) hz).2, hin (y, t) hz] at hh
    constructor
    · exact ((hh.1.hasDerivWithinAt (s := Icc 0 (Z - Y))).congr_of_mem
        (fun w hw => by simp only [(hχhit (w, t) ⟨hw, ht⟩).2])
        ⟨hy.1.le, hy.2.le⟩).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    · exact ((hh.2.hasDerivWithinAt (s := Icc 0 (Z - Y))).congr_of_mem
        (fun w hw => by simp only [(hχhit (w, t) ⟨hw, ht⟩).2, hin (w, t) ⟨hw, ht⟩]; rfl)
        ⟨hy.1.le, hy.2.le⟩).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
  · intro y hy t ht
    exact (htime y hy t ht).congr_of_mem
      (fun v hv => by simp only [(hχhit (y, v) ⟨hy, hv⟩).2, hin (y, v) ⟨hy, hv⟩]; rfl) ht

end CauchyHorizon.Tests
