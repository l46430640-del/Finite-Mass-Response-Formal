import CauchyHorizon.Reduced.ScalarCoordinates
import CauchyHorizon.Characteristic.RadiusTransport
import CauchyHorizon.Analysis.TransportEnergyBound
import CauchyHorizon.Analysis.SourceNorm

/-! Finite-window energy for the actual nonlinear scalar on an inward radius chart. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 2000000 in
theorem IsWaveIntegral.radial_mode_energy
    (B : Background) (hb : B.criticalExponent < 1) {U V : ℝ} {h rH : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < rH 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous rH) (hr0 : ∀ t, rH t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / rH w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt rH
      (horizonFunction (rH t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    {p₀ : ℝ≥0∞} (hp₀ : 4 ≤ p₀) {f : ℝ → ℝ} (hf : MemLp f p₀ (volume.restrict (Icc 0 U)))
    (hfc : ContDiffOn ℝ 1 f (Ioi 0)) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp₀ hf (horizonPhi h rH 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR hp₀ hf) x)
    {H : ℝ → ℝ} (hH : ContDiffOn ℝ 1 H (Ioo 0 V))
    {a b l S R : ℝ} (hab : a ≤ b) (hlS : l ≤ S) {χ : ℝ × ℝ → ℝ}
    (hχc : ContinuousOn χ (Icc a b ×ˢ Icc l S)) :
    let D := Icc a b ×ˢ Icc l S
    let zIn := incomingWaveCurve hU hUR hp₀ hf (horizonPhi h rH 0)
    let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
    let u := fun z : ℝ × ℝ => projIcc 0 U hU (χ z)
    let v := fun z : ℝ × ℝ => projIcc 0 V hV z.2
    let ρ := fun z => x.1 (u z) (v z) 0
    let n := fun z => ν (u z) (v z)
    let L := fun z => x.2.1 (u z) (v z) 0
    let J := fun z =>
      -(ContinuousLinearMap.toSpanSingleton ℝ (n z)⁻¹).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
        (ContinuousLinearMap.toSpanSingleton ℝ (L z / n z)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (∀ z ∈ D, χ z ∈ Ioo 0 U ∧ z.2 ∈ Ioo 0 V ∧ ρ z = R - z.1 ∧
      ρ z ∈ Ioo B.inner B.event ∧ L z < 0 ∧ HasFDerivWithinAt χ (J z) D z) →
    let ζ := fun z => zIn (u z) 0 * f (χ z) + scalarTransportCorrection hV ν x.2.1 (u z) (v z)
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).1 (B.event - y)
    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).2 (B.event - y)
    let p := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * (ρ z * x.2.1 (u z) (v z) 1) - X (ρ z) * H z.2
    let q := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * χ z * ζ z / B.criticalWeight (ρ z) - W (ρ z) * H z.2
    let α := fun z => L z / (ρ z * χ z * n z) * B.criticalWeight (ρ z)
    let β := fun z => χ z * n z / (ρ z * L z) / B.criticalWeight (ρ z)
    let c := fun z => -1 / L z
    let d := fun z => B.innerRate * (c z - -1 / B.F (ρ z))
    let S₁ := fun z => (L z / (ρ z * χ z * n z) - B.outerRate / ρ z) *
      B.criticalWeight (ρ z) * W (ρ z) * H z.2
    let S₂ := fun z => ((χ z * n z / (ρ z * L z) - 1 / (B.outerRate * ρ z)) /
      B.criticalWeight (ρ z) * X (ρ z) + d z * W (ρ z)) * H z.2 - c z * W (ρ z) * deriv H z.2
    let cv := fun z => (x.2.1 (u z) (v z) 2 -
      radialSourceField B.charge B.cosmological x.1 x.2.1 ν hx.choose (u z) (v z) / n z) / L z -
        ρ z * (x.2.1 (u z) (v z) 1) ^ 2 / (L z) ^ 2
    let N := fun y => ∫ t in l..S, p (y, t) ^ 2 + q (y, t) ^ 2
    ContinuousOn N (Icc a b) ∧
      (∀ y ∈ Ioo a b, HasDerivAt N
        ((∫ t in l..S, 2 * (α (y, t) + β (y, t)) * p (y, t) * q (y, t) +
          (2 * d (y, t) + cv (y, t)) * q (y, t) ^ 2 +
          2 * S₁ (y, t) * p (y, t) + 2 * S₂ (y, t) * q (y, t)) +
          c (y, l) * q (y, l) ^ 2 - c (y, S) * q (y, S) ^ 2) y) ∧
      ContinuousOn S₁ D ∧ ContinuousOn S₂ D ∧
      ∀ G : ℝ → ℝ, ContinuousOn G (Icc a b) →
        (∀ z ∈ D, |α z + β z| + |2 * d z + cv z| ≤ G z.1) →
        (∀ η : ℝ → ℝ, ContinuousOn η (Icc a b) → (∀ y ∈ Icc a b, 0 < η y) →
          N b ≤ (N a + ∫ y in a..b, c (y, l) * q (y, l) ^ 2 +
            (∫ t in l..S, S₁ (y, t) ^ 2 + S₂ (y, t) ^ 2) / η y) *
              Real.exp (∫ y in a..b, G y + η y)) ∧
        Real.sqrt (N b) ≤ (Real.sqrt (N a) + Real.sqrt (∫ y in a..b, c (y, l) * q (y, l) ^ 2) +
          ∫ y in a..b, Real.sqrt (∫ t in l..S, S₁ (y, t) ^ 2 + S₂ (y, t) ^ 2)) *
            Real.exp (((∫ y in a..b, G y) + 1) / 2) := by
  intro D zIn ν u v ρ n L J hχ ζ X W p q α β c d S₁ S₂ cv N
  have hnu (z : ℝ × ℝ) : n z < 0 :=
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp₀ hf (u z) (v z)).2.2.1
  have hn0 : ∀ z ∈ D, n z ≠ 0 := fun z _ => (hnu z).ne
  have hL0 : ∀ z ∈ D, L z ≠ 0 := fun z hz => (hχ z hz).2.2.2.2.1.ne
  have hρ0 : ∀ z ∈ D, ρ z ≠ 0 := fun z hz => (B.inner_pos.trans (hχ z hz).2.2.2.1.1).ne'
  have hu0 : ∀ z ∈ D, χ z ≠ 0 := fun z hz => (hχ z hz).1.1.ne'
  have hF : ContinuousOn (incomingVelocity (rH 0) f) (Ioi 0) := by
    have hh := hfc.continuousOn
    unfold incomingVelocity
    fun_prop
  have hinu := (incomingWave_constraint_data hU hUR hp₀ hf (horizonPhi h rH 0)).1
  obtain ⟨hp, hq, qv, hqv, hspace, htime⟩ := hx.radial_mode_coordinate_transport B hb rfl
    hinu hF (incomingWaveVelocity_ae hUR hp₀ hf) hfc hH hχc
      (fun z hz => ⟨(hχ z hz).1, (hχ z hz).2.1, (hχ z hz).2.2.1,
        (hχ z hz).2.2.2.1, hn0 z hz, hL0 z hz, (hχ z hz).2.2.2.2.2⟩)
  have huc : ContinuousOn u D := by dsimp only [u]; fun_prop
  have hvc : ContinuousOn v D := by dsimp only [v]; fun_prop
  have huv := huc.prodMk hvc
  have hρc : ContinuousOn ρ D := by dsimp only [ρ]; fun_prop
  have hnc : ContinuousOn n D := by dsimp only [n]; fun_prop
  have hLc : ContinuousOn L D := by dsimp only [L]; fun_prop
  have hqc : ContinuousOn (fun z => B.criticalWeight (ρ z)) D :=
    B.criticalWeight_continuousOn.comp hρc (fun z hz => (hχ z hz).2.2.2.1)
  have hq0 : ∀ z ∈ D, B.criticalWeight (ρ z) ≠ 0 :=
    fun z hz => (B.criticalWeight_pos (hχ z hz).2.2.2.1).ne'
  have hFc : ContinuousOn (fun z => B.F (ρ z)) D := by
    change ContinuousOn (fun z => 1 - 2 * B.mass / ρ z + B.charge ^ 2 / (ρ z) ^ 2 -
      B.cosmological * (ρ z) ^ 2 / 3) D
    have hr2 : ∀ z ∈ D, (ρ z) ^ 2 ≠ 0 := fun z hz => pow_ne_zero 2 (hρ0 z hz)
    fun_prop (disch := assumption)
  have hF0 : ∀ z ∈ D, B.F (ρ z) ≠ 0 := fun z hz => (B.F_neg (hχ z hz).2.2.2.1).ne
  have hAc : ContinuousOn (fun z => L z / (ρ z * χ z * n z)) D :=
    hLc.div ((hρc.mul hχc).mul hnc) (fun z hz => mul_ne_zero (mul_ne_zero (hρ0 z hz) (hu0 z hz)) (hn0 z hz))
  have hBc : ContinuousOn (fun z => χ z * n z / (ρ z * L z)) D :=
    (hχc.mul hnc).div (hρc.mul hLc) (fun z hz => mul_ne_zero (hρ0 z hz) (hL0 z hz))
  have hα : ContinuousOn α D := hAc.mul hqc
  have hβ : ContinuousOn β D := hBc.div hqc hq0
  have hcc : ContinuousOn c D := continuousOn_const.div hLc hL0
  have hdc : ContinuousOn d D := continuousOn_const.mul (hcc.sub (continuousOn_const.div hFc hF0))
  have hXc : Continuous X := (continuous_extendCurve B.radialLength_pos.le _).comp (continuous_const.sub continuous_id)
  have hWc : Continuous W := (continuous_extendCurve B.radialLength_pos.le _).comp (continuous_const.sub continuous_id)
  have hXρ := hXc.comp_continuousOn hρc
  have hWρ := hWc.comp_continuousOn hρc
  have hHc : ContinuousOn (fun z : ℝ × ℝ => H z.2) D :=
    hH.continuousOn.comp continuousOn_snd (fun z hz => (hχ z hz).2.1)
  have hHdc : ContinuousOn (fun z : ℝ × ℝ => deriv H z.2) D :=
    (hH.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).comp continuousOn_snd (fun z hz => (hχ z hz).2.1)
  have hS₁ : ContinuousOn S₁ D :=
    ((((hAc.sub (continuousOn_const.div hρc hρ0)).mul hqc).mul hWρ).mul hHc)
  have hS₂ : ContinuousOn S₂ D := by
    have hai : ContinuousOn (fun z => 1 / (B.outerRate * ρ z)) D :=
      continuousOn_const.div (continuousOn_const.mul hρc) (fun z hz => mul_ne_zero B.outerRate_pos.ne' (hρ0 z hz))
    exact (((((hBc.sub hai).div hqc hq0).mul hXρ).add (hdc.mul hWρ)).mul hHc).sub ((hcc.mul hWρ).mul hHdc)
  have hcv : ContinuousOn cv D := by
    have hs := (radialSourceField B.charge B.cosmological x.1 x.2.1 ν hx.choose).uncurry.continuous.comp_continuousOn huv
    have he := ((continuous_apply (2 : Fin 3)).comp x.2.1.uncurry.continuous).comp_continuousOn huv
    have hw := ((continuous_apply (1 : Fin 3)).comp x.2.1.uncurry.continuous).comp_continuousOn huv
    exact ((he.sub (hs.div hnc hn0)).div hLc hL0).sub
      ((hρc.mul (hw.pow 2)).div (hLc.pow 2) (fun z hz => pow_ne_zero 2 (hL0 z hz)))
  have hct (y : ℝ) (hy : y ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc l S) :
      HasDerivWithinAt (fun w => c (y, w)) (cv (y, t)) (Icc l S) t := by
    have hz : (y, t) ∈ D := ⟨hy, ht⟩
    have hu := (hχ (y, t) hz).1
    have hv := (hχ (y, t) hz).2.1
    have hum : χ (y, t) ∈ Icc 0 U := ⟨hu.1.le, hu.2.le⟩
    have hvm : t ∈ Icc 0 V := ⟨hv.1.le, hv.2.le⟩
    have hg := (hχ (y, t) hz).2.2.2.2.2.comp_hasDerivWithinAt t
      ((hasDerivWithinAt_const t (Icc l S) y).prodMk (hasDerivWithinAt_id t (Icc l S)))
      (show MapsTo (fun w => (y, w)) (Icc l S) D from fun _ hw => ⟨hy, hw⟩)
    have hg' : HasDerivWithinAt (fun w => χ (y, w)) (-L (y, t) / n (y, t)) (Icc l S) t := by
      simpa only [J, sub_apply, neg_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        smul_eq_mul, zero_mul, one_mul, neg_zero, zero_sub, neg_div] using! hg
    have hh := hx.inverse_lambda_curve_derivative hx.choose hinu
      (fun w s => hx.outgoing_radial_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp₀ hf w s.property)
      ⟨χ (y, t), hum⟩ ⟨t, hvm⟩ hu hv (by simpa only [L, u, v, projIcc_of_mem hU hum, projIcc_of_mem hV hvm] using hL0 (y, t) hz)
      (g := fun w => χ (y, w)) rfl (by simpa only [n, L, u, v, projIcc_of_mem hU hum, projIcc_of_mem hV hvm] using hg')
    simpa only [c, cv, ρ, n, L, u, v, intervalExtension_apply, projIcc_of_mem hU hum,
      projIcc_of_mem hV hvm] using! hh
  have he := transport_energy_identity hab hlS hp hq hcc hα hβ hdc hS₁ hS₂ hqv hcv
    (fun y hy t ht => (hspace y hy t ht).1) (fun y hy t ht => (hspace y hy t ht).2) htime hct
  refine ⟨he.1, he.2, hS₁, hS₂, ?_⟩
  intro G hGc hcoef
  have hc0 (z : ℝ × ℝ) (hz : z ∈ D) : 0 ≤ c z :=
    (div_pos_of_neg_of_neg (by norm_num) (hχ z hz).2.2.2.2.1).le
  have hweighted (η : ℝ → ℝ) (hηc : ContinuousOn η (Icc a b)) (hη0 : ∀ y ∈ Icc a b, 0 < η y) :=
    transport_energy_bound hab hlS hp hq hcc hα hβ hdc hS₁ hS₂ hcv hGc hηc hη0 hc0 hcoef he.2
  refine ⟨hweighted, ?_⟩
  apply source_norm_bound_of_young hab
    (intervalIntegral.integral_nonneg_of_forall hlS (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (continuousOn_rectangle_integral hab hlS ((hS₁.pow 2).add (hS₂.pow 2)))
    (((hcc.mul (hq.pow 2)).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hy => ⟨hy, ⟨le_rfl, hlS⟩⟩))) hGc
    (fun _ _ => intervalIntegral.integral_nonneg_of_forall hlS (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (fun y hy => mul_nonneg (hc0 (y, l) ⟨hy, ⟨le_rfl, hlS⟩⟩) (sq_nonneg _)) hweighted

end CauchyHorizon
