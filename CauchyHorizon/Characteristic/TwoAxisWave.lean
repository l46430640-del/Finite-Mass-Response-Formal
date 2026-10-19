import CauchyHorizon.Characteristic.IncomingEstimates
import CauchyHorizon.Characteristic.OutgoingWave
import CauchyHorizon.Reduced.RadialFlux

/-! A uniform local integral solution with the actual rough incoming data and horizon traces. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_local_incoming_wave (e Λ R φ₀ M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (vOut : C(ℝ, WaveVector)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ d : ℝ, 0 < d ∧ d < R ∧ d ≤ 1 ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R), U ≤ d → V ≤ d →
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        ‖incomingWaveVelocity hUR hp hf‖ ≤ M →
      ∃! x : WaveState U V,
        ‖x - waveSeed (incomingWaveCurve hU hUR hp hf φ₀) (vOut.restrict (Icc 0 V))
          (incomingWaveVelocity hUR hp hf)‖ ≤ δ ∧
        IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) (vOut.restrict (Icc 0 V))
          (incomingWaveVelocity hUR hp hf) x := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn vOut.continuous.continuousOn
  let N : ℝ := max (‖(![R, φ₀, Real.log 4] : WaveVector)‖ + M) K
  have hN : 0 ≤ N := (add_nonneg (norm_nonneg _) hM).trans (le_max_left _ _)
  obtain ⟨δ, hδ, _hδR, d₀, hd₀, hd₀1, hsolve⟩ := exists_local_wave_integral e Λ (R / 2) N M (half_pos hR) hN hM
  let d := min d₀ (R / 2)
  have hd : 0 < d := lt_min hd₀ (half_pos hR)
  have hdR : d < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hd1 : d ≤ 1 := (min_le_left _ _).trans hd₀1
  refine ⟨δ, hδ, d, hd, hdR, hd1, ?_⟩
  intro U V hU hV hUR hUd hVd p hp f hf hfn
  have hrange (u : Icc 0 U) : R / 2 ≤ incomingWaveCurve hU hUR hp hf φ₀ u 0 := by
    have hUhalf : U ≤ R / 2 := hUd.trans (min_le_right _ _)
    exact (by linarith : R / 2 ≤ R - U).trans (incomingWaveCurve_radius hU hUR hp hf φ₀ u)
  have hz : ‖incomingWaveCurve hU hUR hp hf φ₀‖ ≤ N := by
    refine (incomingWaveCurve_norm_le hU hUR hp hf φ₀).trans ?_
    have hsqrt : Real.sqrt U ≤ 1 := Real.sqrt_le_one.2 (hUd.trans hd1)
    have hprod : Real.sqrt U * ‖incomingWaveVelocity hUR hp hf‖ ≤ M := by
      simpa only [one_mul] using mul_le_mul hsqrt hfn (norm_nonneg _) zero_le_one
    exact (add_le_add (le_refl ‖(![R, φ₀, Real.log 4] : WaveVector)‖) hprod).trans (le_max_left _ _)
  have hv : ‖vOut.restrict (Icc 0 V)‖ ≤ N := by
    apply (ContinuousMap.norm_le _ hN).2
    intro v
    exact (hK v ⟨v.property.1, v.property.2.trans (hVd.trans hd1)⟩).trans (le_max_right _ _)
  exact hsolve hU hV (hUd.trans (min_le_left _ _)) (hVd.trans (min_le_left _ _))
    (incomingWaveCurve hU hUR hp hf φ₀) (vOut.restrict (Icc 0 V)) (incomingWaveVelocity hUR hp hf)
    hrange hz hv hfn

theorem IsWaveIntegral.horizon_traces {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x) :
    (∀ u : Icc 0 U, x.1 u ⟨0, le_rfl, hV⟩ =
      ![incomingRadius (r 0) u, incomingPhi (horizonPhi h r 0) f u, incomingLogOmega (r 0) f u]) ∧
    (∀ v : Icc 0 V, x.1 ⟨0, le_rfl, hU⟩ v = horizonVector M e Λ h r v) := by
  constructor
  · intro u
    obtain ⟨rx, hfix⟩ := hx
    have hb := waveIteration_incoming_value hU hV e Λ
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x rx u
    rw [hfix] at hb
    exact hb.trans (incomingWaveCurve_apply hU hUR hp hf (horizonPhi h r 0) u)
  · intro v
    rw [hx.horizontal_identity (c := ![r 0, horizonPhi h r 0, Real.log 4]) rfl]
    change horizonWaveCurve hV M e Λ hc hi hrc hr0 v + (∫ t in (0 : ℝ)..0, x.2.2 t) v = _
    simp only [intervalIntegral.integral_same, ContinuousMap.zero_apply, add_zero]
    exact horizonWaveCurve_apply hV hc hi hrc hr0 hφ hrd v

theorem exists_local_horizon_wave {M e Λ : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) (hrp : 0 < r 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ d : ℝ, 0 < d ∧ d < r 0 ∧ d ≤ 1 ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ d → V ≤ d →
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        ‖incomingWaveVelocity hUR hp hf‖ ≤ A →
      ∃ x : WaveState U V,
        IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x ∧
        (∀ u : Icc 0 U, x.1 u ⟨0, le_rfl, hV⟩ =
          ![incomingRadius (r 0) u, incomingPhi (horizonPhi h r 0) f u, incomingLogOmega (r 0) f u]) ∧
        (∀ v : Icc 0 V, x.1 ⟨0, le_rfl, hU⟩ v = horizonVector M e Λ h r v) := by
  let vOut : C(ℝ, WaveVector) := ⟨horizonVelocity M e Λ h r, horizonVelocity_continuous hc hi hrc hr0⟩
  obtain ⟨δ, _hδ, d, hd, hdR, hd1, hsolve⟩ := exists_local_incoming_wave e Λ (r 0)
    (horizonPhi h r 0) A hrp hA vOut
  refine ⟨d, hd, hdR, hd1, ?_⟩
  intro U V hU hV hUR hUd hVd p hp f hf hfn
  obtain ⟨x, hx, _hunique⟩ := hsolve hU hV hUR hUd hVd hp hf hfn
  have hsol : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x := hx.2
  exact ⟨x, hsol, hsol.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf⟩

theorem exists_local_horizon_wave_of_scalar_bound {M e Λ : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) (hrp : 0 < r 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ d : ℝ, 0 < d ∧ d < r 0 ∧ d ≤ 1 ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ d → V ≤ d →
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
      ∃ x : WaveState U V,
        IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x ∧
        (∀ u : Icc 0 U, x.1 u ⟨0, le_rfl, hV⟩ =
          ![incomingRadius (r 0) u, incomingPhi (horizonPhi h r 0) f u, incomingLogOmega (r 0) f u]) ∧
        (∀ v : Icc 0 V, x.1 ⟨0, le_rfl, hU⟩ v = horizonVector M e Λ h r v) := by
  have hB : 0 ≤ 1 + A + r 0 * A ^ 2 := by positivity
  obtain ⟨d, hd, hdR, hd1, hsolve⟩ :=
    exists_local_horizon_wave hc hi hrc hr0 hrp hφ hrd (1 + A + r 0 * A ^ 2) hB
  refine ⟨d, hd, hdR, hd1, ?_⟩
  intro U V hU hV hUR hUd hVd p hp f hf hfn
  exact hsolve hU hV hUR hUd hVd hp hf
    (incomingWaveVelocity_norm_le hU (hUd.trans hd1) hUR hp hf hfn)

theorem IsWaveIntegral.incoming_radialNu_ae {U V R e Λ φ₀ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      x.2.2 u v 0 = radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀)
        x.1 hx.choose (projIcc 0 U hU u) v := by
  apply hx.radialNu_ae hx.choose
  filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
  rw [hu]
  rfl

end CauchyHorizon
