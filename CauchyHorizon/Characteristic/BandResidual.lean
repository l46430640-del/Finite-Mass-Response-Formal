import CauchyHorizon.Characteristic.BandCoordinates
import CauchyHorizon.Radial.ResidualBound
import CauchyHorizon.Analysis.ResidualEnergy

/-! Uniform finite-window L2 residual bounds on actual nonlinear radius bands. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_band_residual_energy (B : Background) (hm : B.criticalExponent < 1) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - y)
    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - y)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ C T : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ,
          0 < U₀ ∧ U₀ ≤ δ ∧ 0 < C ∧ 0 < T ∧ (∀ ε L, T ≤ τ ε L) ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
            MemLp f p (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x),
                ∀ (hUp : 0 < U) (ε : Ioi (0 : ℝ)) (l S : ℝ), τ ε ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                  ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ (Icc Y Z ×ˢ Icc l S) ∧
                    (∀ q ∈ Icc Y Z ×ˢ Icc l S,
                      χ q ∈ Ioo 0 U ∧ x.1 (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2) 0 = q.1 ∧
                        x.2.1 (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2) 0 < 0) ∧
                    ∀ y ∈ Icc Y Z,
                      let N := fun t => χ (y, t) * ν (projIcc 0 U hU (χ (y, t))) (projIcc 0 V hV t)
                      let L := fun t => x.2.1 (projIcc 0 U hU (χ (y, t))) (projIcc 0 V hV t) 0
                      let α := fun t => (L t / (y * N t) - B.outerRate / y) * B.criticalWeight y * W y
                      let β := fun t => (N t / (y * L t) - 1 / (B.outerRate * y)) / B.criticalWeight y * X y +
                        B.innerRate * (-1 / L t - -1 / B.F y) * W y
                      let γ := fun t => (-1 / L t) * W y
                      ∀ P D : ℝ → ℝ, MemLp P 2 (volume.restrict (Icc l S)) →
                        MemLp D 2 (volume.restrict (Icc l S)) →
                        MemLp (fun t => α t * P t) 2 (volume.restrict (Icc l S)) ∧
                        MemLp (fun t => β t * P t - γ t * D t) 2 (volume.restrict (Icc l S)) ∧
                          (∫ t in Icc l S, (α t * P t) ^ 2 + (β t * P t - γ t * D t) ^ 2) ≤
                            2 * (ε : ℝ) ^ 2 * (∫ t in Icc l S, P t ^ 2) +
                              2 * C ^ 2 * (∫ t in Icc l S, D t ^ 2) := by
  intro hi hr0 X W
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ := B.exists_band_coordinates
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, T, τ, σ, hU₀, hUδ, hT, _hτ, hσ, hsolve⟩ := hband Y Z hY hYZ hYR hZ
  obtain ⟨C, hC, htol⟩ := B.exists_compact_residual_tolerance hm hY hZ
  have htol' (ε : Ioi (0 : ℝ)) := htol ε ε.property
  choose η hη hcoef using htol'
  refine ⟨U₀, C, T, (fun ε L => max (σ L) (τ ⟨η ε, hη ε⟩)), hU₀, hUδ, hC, hT,
    (fun _ L => (hσ L).trans (le_max_left _ _)), ?_⟩
  intro p hp f hf hfn U V hU hV hUR hUU hfU x hx hUp ε l S hstart hlS hSV
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
  obtain ⟨χ, hχc, _hJc, hpoint⟩ :=
    hsolve p hp f hf hfn U V hU hV hUR hUU hfU x hx hUp l S ((le_max_left _ _).trans hstart) hlS hSV
  have hNneg (q : ℝ × ℝ) (hq : q ∈ Icc Y Z ×ˢ Icc l S) :
      χ q * ν (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2) < 0 :=
    mul_neg_of_pos_of_neg (hpoint q hq).1.1
      (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU _ _).2.2.1
  have hsmall (q : ℝ × ℝ) (hq : q ∈ Icc Y Z ×ˢ Icc l S) :
      |Real.log (B.outerRate * (χ q * ν (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2)) / B.F q.1)| +
        |x.2.1 (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2) 0 /
          (χ q * ν (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2)) - B.outerRate| < η ε := by
    have hh := (hpoint q hq).2.2.2 ⟨η ε, hη ε⟩ (((le_max_right _ _).trans hstart).trans hq.2.1)
    have hdrop (a b c : ℝ) (h : a + b + c < η ε) (hb : 0 ≤ b) : a + c < η ε := by linarith only [h, hb]
    simpa only [mul_div_assoc] using hdrop _ _ _ hh (abs_nonneg _)
  have hcoeff (q : ℝ × ℝ) (hq : q ∈ Icc Y Z ×ˢ Icc l S) :=
    hcoef ε q.1 hq.1 (χ q * ν (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2))
      (x.2.1 (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2) 0) (hNneg q hq) (hsmall q hq)
  refine ⟨χ, hχc, (fun q hq => ⟨(hpoint q hq).1, (hpoint q hq).2.1, (hcoeff q hq).1⟩), ?_⟩
  intro y hy N L α β γ P D hP hD
  have hχy : ContinuousOn (fun t => χ (y, t)) (Icc l S) :=
    hχc.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hy, ht⟩)
  have hup : ContinuousOn (fun t => projIcc 0 U hU (χ (y, t))) (Icc l S) :=
    (continuous_projIcc (a := (0 : ℝ)) (b := U) (h := hU)).comp_continuousOn hχy
  have hvp : ContinuousOn (fun t : ℝ => projIcc 0 V hV t) (Icc l S) :=
    (continuous_projIcc (a := (0 : ℝ)) (b := V) (h := hV)).continuousOn
  have hpair : ContinuousOn (fun t =>
      (projIcc 0 U hU (χ (y, t)), projIcc 0 V hV t)) (Icc l S) := hup.prodMk hvp
  have hnuc : ContinuousOn (fun t => ν (projIcc 0 U hU (χ (y, t))) (projIcc 0 V hV t)) (Icc l S) := by
    have hh := ν.uncurry.continuous.comp_continuousOn hpair
    simpa only [Function.comp_def, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair] using hh
  have hNc : ContinuousOn N (Icc l S) := hχy.mul hnuc
  have hLc : ContinuousOn L (Icc l S) :=
    (continuous_apply 0).comp_continuousOn (x.2.1.uncurry.continuous.comp_continuousOn hpair)
  have hy0 : y ≠ 0 := (B.inner_pos.trans (hY.trans_le hy.1)).ne'
  have hA : ContinuousOn (fun t => L t / (y * N t)) (Icc l S) :=
    hLc.div (continuousOn_const.mul hNc) (fun t ht => mul_ne_zero hy0 (hNneg (y, t) ⟨hy, ht⟩).ne)
  have hBc : ContinuousOn (fun t => N t / (y * L t)) (Icc l S) :=
    hNc.div (continuousOn_const.mul hLc) (fun t ht => mul_ne_zero hy0 (hcoeff (y, t) ⟨hy, ht⟩).1.ne)
  have hcc : ContinuousOn (fun t => -1 / L t) (Icc l S) :=
    continuousOn_const.div hLc (fun t ht => (hcoeff (y, t) ⟨hy, ht⟩).1.ne)
  have hαc : ContinuousOn α (Icc l S) :=
    ((hA.sub continuousOn_const).mul continuousOn_const).mul continuousOn_const
  have hβc : ContinuousOn β (Icc l S) :=
    (((hBc.sub continuousOn_const).div_const (B.criticalWeight y)).mul continuousOn_const).add
      ((continuousOn_const.mul (hcc.sub continuousOn_const)).mul continuousOn_const)
  have hγc : ContinuousOn γ (Icc l S) := hcc.mul continuousOn_const
  apply residual_energy_bound (a := α) (b := β) (c := γ) (H := P) (D := D) ε.property.le hC.le
    (hαc.aestronglyMeasurable measurableSet_Icc) (hβc.aestronglyMeasurable measurableSet_Icc)
    (hγc.aestronglyMeasurable measurableSet_Icc) hP hD
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hcoeff (y, t) ⟨hy, ht⟩).2.1.le
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hcoeff (y, t) ⟨hy, ht⟩).2.2

end CauchyHorizon.Background
