import CauchyHorizon.Characteristic.BandEnergy
import CauchyHorizon.Characteristic.BandTransportDecay
import CauchyHorizon.Radial.EnergyGrowth
import CauchyHorizon.Analysis.ResidualEnergy

/-! The actual scalar energy grows at the integrable reference rate plus an arbitrarily small error. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 2000000 in
theorem exists_band_reference_energy (B : Background) (hm : B.criticalExponent < 1) {s H dH A : ℝ}
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
        ∃ U₀ C : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < C ∧
          ∀ (p₀ : ℝ≥0∞) (hp₀ : 4 ≤ p₀) (f : ℝ → ℝ),
            MemLp f p₀ (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p₀ (volume.restrict (Icc 0 δ))).toReal ≤ A → ContDiffOn ℝ 1 f (Ioi 0) →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < rH 0), U ≤ U₀ →
              ∀ (hfU : MemLp f p₀ (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h rH 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp₀ hfU) x),
                ∀ (ε : Ioi (0 : ℝ)) (hUp : 0 < U) (l S : ℝ), τ ε ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                  let D := Icc (0 : ℝ) (Z - Y) ×ˢ Icc l S
                  let zIn := incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h rH 0)
                  let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
                  ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ D ∧
                    (∀ z ∈ D, χ z ∈ Ioo 0 U ∧
                      x.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 = Z - z.1) ∧
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
                      let c := fun z => -1 / L z
                      let d := fun z => B.innerRate * (c z - -1 / B.F (ρ z))
                      let S₁ := fun z => (L z / (ρ z * χ z * n z) - B.outerRate / ρ z) *
                        B.criticalWeight (ρ z) * W (ρ z) * P z.2
                      let S₂ := fun z => ((χ z * n z / (ρ z * L z) - 1 / (B.outerRate * ρ z)) /
                        B.criticalWeight (ρ z) * X (ρ z) + d z * W (ρ z)) * P z.2 - c z * W (ρ z) * deriv P z.2
                      let N := fun y => ∫ t in l..S, p (y, t) ^ 2 + q (y, t) ^ 2
                      (∀ η : ℝ → ℝ, ContinuousOn η (Icc 0 (Z - Y)) → (∀ y ∈ Icc 0 (Z - Y), 0 < η y) →
                        N (Z - Y) ≤ (N 0 + ∫ y in (0 : ℝ)..(Z - Y), c (y, l) * q (y, l) ^ 2 +
                          (∫ t in l..S, S₁ (y, t) ^ 2 + S₂ (y, t) ^ 2) / η y) *
                            Real.exp (∫ y in (0 : ℝ)..(Z - Y), B.energyGrowth (Z - y) + (ε : ℝ) + η y)) ∧
                      Real.sqrt (N (Z - Y)) ≤
                        (Real.sqrt (N 0) + Real.sqrt (∫ y in (0 : ℝ)..(Z - Y), c (y, l) * q (y, l) ^ 2) +
                          ∫ y in (0 : ℝ)..(Z - Y), Real.sqrt (∫ t in l..S, S₁ (y, t) ^ 2 + S₂ (y, t) ^ 2)) *
                            Real.exp (((∫ r in B.inner..B.event, B.energyGrowth r) + (ε : ℝ) * (Z - Y) + 1) / 2) ∧
                      Real.sqrt (N (Z - Y)) ≤
                        (Real.sqrt (N 0) + Real.sqrt (∫ y in (0 : ℝ)..(Z - Y), c (y, l) * q (y, l) ^ 2) +
                          (Z - Y) * Real.sqrt (2 * (ε : ℝ) ^ 2 * (∫ t in l..S, P t ^ 2) +
                            2 * C ^ 2 * (∫ t in l..S, (deriv P t) ^ 2))) *
                              Real.exp (((∫ r in B.inner..B.event, B.energyGrowth r) + (ε : ℝ) * (Z - Y) + 1) / 2) := by
  intro hi hr0
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δe, Re, hδe, hRe, henergy⟩ := B.exists_band_energy hm hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δd, Rd, hδd, _hδdr, hRd, hdecay⟩ := B.exists_band_transport_decay hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨max δe δd, min Re Rd, hδe.trans_le (le_max_left _ _),
    ⟨lt_min hRe.1 hRd.1, (min_le_left _ _).trans_lt hRe.2⟩, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨Ue, σ, τn, hUe, hUeδ, he⟩ := henergy Y Z hY hYZ (hYR.trans (min_le_left _ _)) hZ
  obtain ⟨Ud, C, d₀, γ, T, hUd, _hUdδ, _hC, hd₀, hγ, _hT, hd⟩ := hdecay Y Z hY hYZ (hYR.trans (min_le_right _ _)) hZ
  have htol (ε : Ioi (0 : ℝ)) := B.exists_compact_energy_tolerance hY hZ (half_pos ε.property)
  choose θ hθ hsmall using htol
  obtain ⟨Cs, hCs, hrtol⟩ := B.exists_compact_residual_tolerance hm hY hZ
  have hrtol' (ε : Ioi (0 : ℝ)) := hrtol ε ε.property
  choose θr hθr hrsmall using hrtol'
  let θc := fun ε => min (θ ε) (θr ε)
  have hθc (ε : Ioi (0 : ℝ)) : 0 < θc ε := lt_min (hθ ε) (hθr ε)
  have hzero : Tendsto (fun t : ℝ => C * Real.exp (-γ * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hγ))).const_mul C
  have hlate (ε : Ioi (0 : ℝ)) : ∃ Tε : ℝ, ∀ t ≥ Tε, C * Real.exp (-γ * t) < (ε : ℝ) / 2 :=
    eventually_atTop.1 (hzero.eventually_lt_const (half_pos ε.property))
  choose Tε hTε using hlate
  let τ := fun ε W => max (σ W) (max (τn ⟨θc ε, hθc ε⟩) (max T (Tε ε)))
  refine ⟨min Ue Ud, Cs, τ, lt_min hUe hUd, (min_le_left _ _).trans (hUeδ.trans (le_max_left _ _)), hCs, ?_⟩
  intro p₀ hp₀ f hf hfn hfc U V hU hV hUR hUU hfU x hx ε hUp l S hl hlS hSV D zIn ν
  have hfE := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_left δe δd)) le_rfl)
  have hfD := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_right δe δd)) le_rfl)
  have hEn := (scalar_prefix_norm_le (le_max_left δe δd) hf).trans hfn
  have hDn := (scalar_prefix_norm_le (le_max_right δe δd) hf).trans hfn
  have hσl : σ ⟨U, hUp⟩ ≤ l := (le_max_left _ _).trans hl
  have hnl : τn ⟨θc ε, hθc ε⟩ ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hTl : T ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hl))
  have hεl : Tε ε ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hl))
  obtain ⟨χ, hχc, hχhit, htime, hnorm, heq⟩ := he p₀ hp₀ f hfE hEn hfc U V hU hV hUR
    (hUU.trans (min_le_left _ _)) hfU x hx hUp l S hσl hlS hSV
  refine ⟨χ, hχc, hχhit, ?_⟩
  intro P hP u v ρ n L ζ X W p q c d S₁ S₂ N
  let α := fun z => L z / (ρ z * χ z * n z) * B.criticalWeight (ρ z)
  let β := fun z => χ z * n z / (ρ z * L z) / B.criticalWeight (ρ z)
  let cv := fun z => (x.2.1 (u z) (v z) 2 -
    radialSourceField B.charge B.cosmological x.1 x.2.1 ν hx.choose (u z) (v z) / n z) / L z -
      ρ z * (x.2.1 (u z) (v z) 1) ^ 2 / (L z) ^ 2
  have hcoef (z : ℝ × ℝ) (hz : z ∈ D) :
      |α z + β z| + |2 * d z + cv z| ≤ B.energyGrowth (Z - z.1) + (ε : ℝ) := by
    have hhit : ρ z = Z - z.1 := (hχhit z hz).2
    have hrband : ρ z ∈ Icc Y Z := by rw [hhit]; constructor <;> linarith [hz.1.1, hz.1.2]
    have hu := (hχhit z hz).1
    have hv := htime z hz
    have hum : χ z ∈ Icc 0 U := ⟨hu.1.le, hu.2.le⟩
    have hvm : z.2 ∈ Icc 0 V := ⟨hv.1.le, hv.2.le⟩
    have hu' : (u z : ℝ) ∈ Ioo 0 U := by simpa only [u, projIcc_of_mem hU hum] using hu
    have hv' : (v z : ℝ) ∈ Ioo 0 V := by simpa only [v, projIcc_of_mem hV hvm] using hv
    have hn : n z < 0 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp₀ hfU (u z) (v z)).2.2.1
    have herr : |Real.log (B.outerRate * (χ z * n z) / B.F (ρ z))| + |L z / (χ z * n z) - B.outerRate| < θ ε := by
      have hh := (hnorm ⟨θc ε, hθc ε⟩ z hz (hnl.trans hz.2.1)).trans_le (min_le_left _ _)
      simpa only [n, L, u, v, hhit, mul_div_assoc] using hh
    have hmain : |α z + β z| + |2 * d z| < B.energyGrowth (ρ z) + (ε : ℝ) / 2 := by
      simpa only [α, β, d, c, mul_assoc] using hsmall ε (ρ z) hrband (χ z * n z) (L z)
        (mul_neg_of_pos_of_neg hu.1 hn) herr
    have hdec := hd p₀ hp₀ f hfD hDn U V hU hV hUR (hUU.trans (min_le_right _ _)) hfU x hx
      (u z) (v z) hu' hv' (by simpa only [v, projIcc_of_mem hV hvm] using hTl.trans hz.2.1) hrband
    have hl0 : L z ≠ 0 := (hdec.1.trans_lt (neg_neg_of_pos hd₀)).ne
    let κ := fun t => -Real.exp (intervalExtension hV (x.1 (u z)) t 2) /
      (4 * intervalExtension hV (ν (u z)) t)
    have hecv : cv z = (deriv κ (v z) / κ (v z)) / L z -
        (ρ z * x.2.1 (u z) (v z) 1) ^ 2 / (ρ z * (L z) ^ 2) :=
      hx.inverse_lambda_coefficient_eq (u z) (v z) hv' hn.ne hl0
    have hcv : |cv z| < (ε : ℝ) / 2 := by
      rw [hecv]
      have hh := (le_add_of_nonneg_left (abs_nonneg _)).trans hdec.2.1
      have hlate' : C * Real.exp (-γ * (v z : ℝ)) < (ε : ℝ) / 2 := by
        simpa only [v, projIcc_of_mem hV hvm] using hTε ε z.2 (hεl.trans hz.2.1)
      exact hh.trans_lt hlate'
    have hh := abs_add_le (2 * d z) (cv z)
    rw [hhit] at hmain
    linarith only [hmain, hcv, hh]
  have hGr : ContinuousOn (fun y => B.energyGrowth (Z - y)) (Icc 0 (Z - Y)) := by
    apply (B.energyGrowth_regular hm).1.comp (continuousOn_const.sub continuousOn_id)
    intro y hy
    change Z - y ∈ Ioo B.inner B.event
    constructor <;> linarith only [hY, hZ, hy.1, hy.2]
  obtain ⟨hw, hn⟩ := (heq P hP).2.2.2.2 (fun y => B.energyGrowth (Z - y) + (ε : ℝ))
    (hGr.add continuousOn_const) hcoef
  have hnormbound : Real.sqrt (N (Z - Y)) ≤
      (Real.sqrt (N 0) + Real.sqrt (∫ y in (0 : ℝ)..(Z - Y), c (y, l) * q (y, l) ^ 2) +
        ∫ y in (0 : ℝ)..(Z - Y), Real.sqrt (∫ t in l..S, S₁ (y, t) ^ 2 + S₂ (y, t) ^ 2)) *
          Real.exp (((∫ r in B.inner..B.event, B.energyGrowth r) + (ε : ℝ) * (Z - Y) + 1) / 2) := by
    apply hn.trans
    apply mul_le_mul_of_nonneg_left _
      (add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (intervalIntegral.integral_nonneg_of_forall (sub_nonneg.2 hYZ.le) (fun _ => Real.sqrt_nonneg _)))
    apply Real.exp_le_exp.2
    have hg := B.energyGrowth_regular hm
    have hgint := intervalIntegral.integral_mono_interval hY.le hYZ.le hZ.le
      ((ae_restrict_mem measurableSet_Ioc).mono (fun r hr => hg.2.2 r ⟨hr.1.le, hr.2⟩)) hg.2.1
    rw [intervalIntegral.integral_add (hGr.intervalIntegrable_of_Icc (sub_nonneg.2 hYZ.le)) intervalIntegrable_const,
      intervalIntegral.integral_comp_sub_left, sub_sub_cancel, sub_zero,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    linarith only [hgint]
  have hsource (z : ℝ × ℝ) (hz : z ∈ D) : S₁ z ^ 2 + S₂ z ^ 2 ≤
      2 * (ε : ℝ) ^ 2 * P z.2 ^ 2 + 2 * Cs ^ 2 * (deriv P z.2) ^ 2 := by
    have hhit : ρ z = Z - z.1 := (hχhit z hz).2
    have hrband : ρ z ∈ Icc Y Z := by rw [hhit]; constructor <;> linarith [hz.1.1, hz.1.2]
    have hn0 : χ z * n z < 0 := mul_neg_of_pos_of_neg (hχhit z hz).1.1
      (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp₀ hfU (u z) (v z)).2.2.1
    have herr : |Real.log (B.outerRate * (χ z * n z) / B.F (ρ z))| +
        |L z / (χ z * n z) - B.outerRate| < θr ε := by
      have hh := (hnorm ⟨θc ε, hθc ε⟩ z hz (hnl.trans hz.2.1)).trans_le (min_le_right _ _)
      simpa only [n, L, u, v, hhit, mul_div_assoc] using hh
    have hh := hrsmall ε (ρ z) hrband (χ z * n z) (L z) hn0 herr
    simpa only [S₁, S₂, X, W, d, c, mul_assoc] using
      residual_square_le (H := P z.2) (D := deriv P z.2) ε.property.le hCs.le hh.2.1.le hh.2.2
  have hSqc : ContinuousOn (fun z => S₁ z ^ 2 + S₂ z ^ 2) D :=
    ((heq P hP).2.2.1.pow 2).add ((heq P hP).2.2.2.1.pow 2)
  have hab : (0 : ℝ) ≤ Z - Y := sub_nonneg.2 hYZ.le
  have htimes : Icc l S ⊆ Ioo (0 : ℝ) V := fun t ht => htime (0, t) ⟨⟨le_rfl, hab⟩, ht⟩
  have hPi : IntervalIntegrable (fun t => P t ^ 2) volume l S :=
    ((hP.continuousOn.mono htimes).pow 2).intervalIntegrable_of_Icc hlS
  have hDi : IntervalIntegrable (fun t => (deriv P t) ^ 2) volume l S :=
    (((hP.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono htimes).pow 2).intervalIntegrable_of_Icc hlS
  have hpoint (y : ℝ) (hy : y ∈ Icc 0 (Z - Y)) :
      (∫ t in l..S, S₁ (y, t) ^ 2 + S₂ (y, t) ^ 2) ≤
        2 * (ε : ℝ) ^ 2 * (∫ t in l..S, P t ^ 2) + 2 * Cs ^ 2 * (∫ t in l..S, (deriv P t) ^ 2) := by
    have hslice := hSqc.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hy, ht⟩)
    have hh := intervalIntegral.integral_mono_on hlS (hslice.intervalIntegrable_of_Icc hlS)
      ((hPi.const_mul (2 * (ε : ℝ) ^ 2)).add (hDi.const_mul (2 * Cs ^ 2))) (fun t ht => hsource (y, t) ⟨hy, ht⟩)
    simpa only [intervalIntegral.integral_add (hPi.const_mul _) (hDi.const_mul _),
      intervalIntegral.integral_const_mul, Function.comp_def, id_eq] using hh
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuousOn_rectangle_integral hab hlS hSqc).sqrt.intervalIntegrable_of_Icc hab)
    intervalIntegrable_const (fun y hy => Real.sqrt_le_sqrt (hpoint y hy))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hi
  refine ⟨hw, hnormbound, hnormbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith only [hi]) (Real.exp_pos _).le

end CauchyHorizon.Background
