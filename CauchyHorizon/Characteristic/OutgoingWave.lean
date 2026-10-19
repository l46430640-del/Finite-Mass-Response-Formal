import CauchyHorizon.Characteristic.HorizonRates
import CauchyHorizon.Reduced.IntegralRegularity

/-! The constructed horizon fields and their continuous characteristic velocity. -/

open MeasureTheory Set

namespace CauchyHorizon

noncomputable def horizonVector (M e Λ : ℝ) (h r : ℝ → ℝ) (t : ℝ) : WaveVector :=
  ![r t, horizonPhi h r t,
    horizonLogOmega (fun w => horizonK (r w) (horizonMass M h w) e Λ) t]

noncomputable def horizonVelocity (M e Λ : ℝ) (h r : ℝ → ℝ) (t : ℝ) : WaveVector :=
  ![horizonFunction (r t) (horizonMass M h t) e Λ, h t / r t,
    2 * horizonK (r t) (horizonMass M h t) e Λ]

variable {M e Λ V : ℝ} {h r : ℝ → ℝ}

theorem horizonVelocity_continuous (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t)) (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) :
    Continuous (horizonVelocity M e Λ h r) := by
  have hm : Continuous (horizonMass M h) := continuous_iff_continuousAt.2
    (fun t => (horizonMass_hasDerivAt hc hi M t).continuousAt)
  apply continuous_pi
  intro i
  fin_cases i
  · dsimp [horizonVelocity, horizonFunction]
    exact ((continuous_const.sub ((continuous_const.mul hm).div hrc hr0)).add
      (continuous_const.div (hrc.pow 2) (fun t => pow_ne_zero 2 (hr0 t)))).sub
      ((continuous_const.mul (hrc.pow 2)).div_const 3)
  · exact hc.div hrc hr0
  · exact continuous_const.mul (horizonK_continuous hrc hm hr0 e Λ)

theorem horizonVector_continuous (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t)) (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t)) :
    Continuous (horizonVector M e Λ h r) := by
  have hm : Continuous (horizonMass M h) := continuous_iff_continuousAt.2
    (fun t => (horizonMass_hasDerivAt hc hi M t).continuousAt)
  have hK := horizonK_continuous hrc hm hr0 e Λ
  apply continuous_pi
  intro i
  fin_cases i
  · exact hrc
  · exact continuous_iff_continuousAt.2 (fun t => (horizonPhi_hasDerivAt hc hrc hr0 hφ t).continuousAt)
  · exact continuous_iff_continuousAt.2 (fun t => (horizonLogOmega_hasDerivAt hK t).continuousAt)

theorem horizonVector_hasDerivAt (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t)) (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t)) {t : ℝ}
    (hrd : HasDerivAt r (horizonFunction (r t) (horizonMass M h t) e Λ) t) :
    HasDerivAt (horizonVector M e Λ h r) (horizonVelocity M e Λ h r t) t := by
  have hm : Continuous (horizonMass M h) := continuous_iff_continuousAt.2
    (fun t => (horizonMass_hasDerivAt hc hi M t).continuousAt)
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · exact hrd
  · exact horizonPhi_hasDerivAt hc hrc hr0 hφ t
  · exact horizonLogOmega_hasDerivAt (horizonK_continuous hrc hm hr0 e Λ) t

noncomputable def horizonWaveVelocity (M e Λ V : ℝ) (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t)) (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) :
    C(Icc 0 V, WaveVector) :=
  ⟨fun t => horizonVelocity M e Λ h r t,
    (horizonVelocity_continuous hc hi hrc hr0).comp continuous_subtype_val⟩

noncomputable def horizonWaveCurve (hV : 0 ≤ V) (M e Λ : ℝ) (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t)) (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) :
    C(Icc 0 V, WaveVector) :=
  ContinuousMap.const _ ![r 0, horizonPhi h r 0, Real.log 4] +
    continuousPrimitive hV (horizonWaveVelocity M e Λ V hc hi hrc hr0)

theorem horizonWaveCurve_apply (hV : 0 ≤ V) (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t)) (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t) (t : Icc 0 V) :
    horizonWaveCurve hV M e Λ hc hi hrc hr0 t = horizonVector M e Λ h r t := by
  have he : continuousPrimitive hV (horizonWaveVelocity M e Λ V hc hi hrc hr0) t =
      ∫ w in (0 : ℝ)..t, horizonVelocity M e Λ h r w := by
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le t.property.1] at hw
    have hwV : w ∈ Icc 0 V := ⟨hw.1, hw.2.trans t.property.2⟩
    simp only [intervalExtension_apply, projIcc_of_mem hV hwV]
    rfl
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (horizonVector_continuous (M := M) (e := e) (Λ := Λ) hc hi hrc hr0 hφ).continuousOn
    (fun w hw => horizonVector_hasDerivAt hc hi hrc hr0 hφ
      ((hrd w hw.1.le).hasDerivAt (Ici_mem_nhds hw.1)))
    ((horizonVelocity_continuous hc hi hrc hr0).intervalIntegrable (0 : ℝ) t)
  change ![r 0, horizonPhi h r 0, Real.log 4] + continuousPrimitive hV
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) t = _
  rw [he, hp]
  have hcorner : horizonVector M e Λ h r 0 = ![r 0, horizonPhi h r 0, Real.log 4] := by
    simp only [horizonVector, horizonLogOmega, intervalIntegral.integral_same, add_zero]
  rw [hcorner]
  abel

end CauchyHorizon
