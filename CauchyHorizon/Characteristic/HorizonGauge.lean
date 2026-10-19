import CauchyHorizon.Characteristic.TwoAxisWave
import CauchyHorizon.Reduced.RadialRegularity

/-! The recovered radial derivative has the prescribed horizon trace and gauge. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem horizon_radial_primitive {M e Λ : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) :
    let K := fun w => horizonK (r w) (horizonMass M h w) e Λ
    r t * horizonNu K t = -r 0 +
      ∫ w in 0..t, r w * (Real.exp (horizonLogOmega K w) * radialPotential (r w) e Λ) := by
  let K := fun w => horizonK (r w) (horizonMass M h w) e Λ
  have hm : Continuous (horizonMass M h) := continuous_iff_continuousAt.2
    (fun w => (horizonMass_hasDerivAt hc hi M w).continuousAt)
  have hK : Continuous K := horizonK_continuous hrc hm hr0 e Λ
  have hn : Continuous (horizonNu K) := continuous_iff_continuousAt.2
    (fun w => (horizonNu_hasDerivAt hK w).continuousAt)
  have hl : Continuous (horizonLogOmega K) := continuous_iff_continuousAt.2
    (fun w => (horizonLogOmega_hasDerivAt hK w).continuousAt)
  have hP : Continuous (fun w => radialPotential (r w) e Λ) := by
    unfold radialPotential
    fun_prop (disch := simp [hr0])
  have he (w : ℝ) : horizonFunction (r w) (horizonMass M h w) e Λ * horizonNu K w +
      r w * (2 * K w * horizonNu K w) =
      r w * (Real.exp (horizonLogOmega K w) * radialPotential (r w) e Λ) := by
    rw [(horizon_normalization K w).2.1]
    dsimp only [K]
    unfold horizonFunction horizonK radialPotential
    field_simp [hr0 w]
    ring
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht (hrc.mul hn).continuousOn
    (fun w hw => by
      have hd := (hrd w hw.1.le).mul (horizonNu_hasDerivAt hK w).hasDerivWithinAt
      rw [he w] at hd
      exact hd.hasDerivAt (Ici_mem_nhds hw.1))
    ((hrc.mul ((Real.continuous_exp.comp hl).mul hP)).intervalIntegrable 0 t)
  simp only [Pi.mul_apply, Function.comp_apply] at hp
  rw [(horizon_corner K).1, mul_neg_one] at hp
  change r t * horizonNu K t = -r 0 +
    ∫ w in 0..t, r w * (Real.exp (horizonLogOmega K w) * radialPotential (r w) e Λ)
  linarith only [hp]

theorem IsWaveIntegral.incoming_radial_hasDerivWithinAt {U V R e Λ φ₀ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (v : Icc 0 V) {u : ℝ} (hu : u ∈ Icc 0 U) :
    HasDerivWithinAt (fun t => intervalExtension hU x.1 t v 0)
      (radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose ⟨u, hu⟩ v)
      (Icc 0 U) u := by
  apply hx.radial_hasDerivWithinAt hx.choose (c := ![R, φ₀, Real.log 4]) rfl _ v hu
  filter_upwards [incomingWaveVelocity_ae hUR hp hf] with w hw
  rw [hw]
  rfl

theorem IsWaveIntegral.horizon_radial_trace {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (v : Icc 0 V) :
    radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      x.1 hx.choose ⟨0, le_rfl, hU⟩ v =
        horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) v := by
  let K := fun w => horizonK (r w) (horizonMass M h w) e Λ
  have htrace := (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2
  have hflux : continuousPrimitive hV (radialFluxField e Λ x.1 hx.choose ⟨0, le_rfl, hU⟩) v =
      ∫ w in (0 : ℝ)..v, r w * (Real.exp (horizonLogOmega K w) * radialPotential (r w) e Λ) := by
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le v.property.1] at hw
    have hwV : w ∈ Icc 0 V := ⟨hw.1, hw.2.trans v.property.2⟩
    simp only [intervalExtension_apply, projIcc_of_mem hV hwV]
    rw [radialFluxField_apply, htrace ⟨w, hwV⟩]
    rfl
  have hcorner : incomingWaveCurve hU hUR hp hf (horizonPhi h r 0) ⟨0, le_rfl, hU⟩ 0 = r 0 := by
    rw [incomingWaveCurve_apply]
    change r 0 - 0 = r 0
    exact sub_zero _
  rw [radialNuField_apply, hcorner, hflux, htrace v]
  change (-r 0 + _) / r v = horizonNu K v
  apply (div_eq_iff (hr0 v)).2
  have hp := horizon_radial_primitive hc hi hrc hr0 hrd v.property.1
  simpa only [mul_comm] using hp.symm

theorem IsWaveIntegral.horizon_gauge {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (v : Icc 0 V) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      x.1 hx.choose ⟨0, le_rfl, hU⟩ v
    ν < 0 ∧ Real.exp (x.1 ⟨0, le_rfl, hU⟩ v 2) = -4 * ν ∧
      -Real.exp (x.1 ⟨0, le_rfl, hU⟩ v 2) / (4 * ν) = 1 := by
  dsimp only
  rw [hx.horizon_radial_trace hU hV hUR hc hi hrc hr0 hφ hrd hp hf v,
    (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
  exact horizon_normalization _ v

end CauchyHorizon
