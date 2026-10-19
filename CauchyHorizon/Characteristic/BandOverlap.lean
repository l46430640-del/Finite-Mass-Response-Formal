import CauchyHorizon.Characteristic.ScalarOverlap

/-! Radius-coordinate energy and bottom inflow are independent of the containing rectangle. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 2000000 in
theorem IsWaveIntegral.horizon_band_energy_overlap {M e Λ A B U V : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p₀ : ℝ≥0∞} (hp₀ : 4 ≤ p₀) {f : ℝ → ℝ}
    (hfA : MemLp f p₀ (volume.restrict (Icc 0 A))) (hfU : MemLp f p₀ (volume.restrict (Icc 0 U)))
    {x : WaveState A B} {y : WaveState U V}
    (hx : IsWaveIntegral hA hB e Λ (incomingWaveCurve hA hAR hp₀ hfA (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ B hc hi hrc hr0) (incomingWaveVelocity hAR hp₀ hfA) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp₀ hfU) y)
    (k : ℝ) (X W q₀ H : ℝ → ℝ) {a b l S : ℝ} (hab : a ≤ b) (hlS : l ≤ S)
    (χA χU : ℝ × ℝ → ℝ) :
    let D := Icc a b ×ˢ Icc l S
    let zA := incomingWaveCurve hA hAR hp₀ hfA (horizonPhi h r 0)
    let zU := incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h r 0)
    let νA := radialNuField hB e Λ zA x.1 hx.choose
    let νU := radialNuField hV e Λ zU y.1 hy.choose
    let uA := fun z => projIcc 0 A hA (χA z)
    let uU := fun z => projIcc 0 U hU (χU z)
    let vB := fun z : ℝ × ℝ => projIcc 0 B hB z.2
    let vV := fun z : ℝ × ℝ => projIcc 0 V hV z.2
    let ρA := fun z => x.1 (uA z) (vB z) 0
    let ρU := fun z => y.1 (uU z) (vV z) 0
    (∀ z ∈ D, χA z ∈ Icc 0 A ∧ χU z ∈ Icc 0 U ∧ z.2 ∈ Icc 0 B ∧ z.2 ∈ Icc 0 V ∧ ρA z = ρU z) →
    let ζA := fun z => zA (uA z) 0 * f (χA z) + scalarTransportCorrection hB νA x.2.1 (uA z) (vB z)
    let ζU := fun z => zU (uU z) 0 * f (χU z) + scalarTransportCorrection hV νU y.2.1 (uU z) (vV z)
    let pA := fun z : ℝ × ℝ => Real.exp (k * z.2) * (ρA z * x.2.1 (uA z) (vB z) 1) - X (ρA z) * H z.2
    let pU := fun z : ℝ × ℝ => Real.exp (k * z.2) * (ρU z * y.2.1 (uU z) (vV z) 1) - X (ρU z) * H z.2
    let qA := fun z : ℝ × ℝ => Real.exp (k * z.2) * χA z * ζA z / q₀ (ρA z) - W (ρA z) * H z.2
    let qU := fun z : ℝ × ℝ => Real.exp (k * z.2) * χU z * ζU z / q₀ (ρU z) - W (ρU z) * H z.2
    let cA := fun z => -1 / x.2.1 (uA z) (vB z) 0
    let cU := fun z => -1 / y.2.1 (uU z) (vV z) 0
    EqOn pA pU D ∧ EqOn qA qU D ∧ EqOn cA cU D ∧
      (∀ d ∈ Icc a b, (∫ t in l..S, pA (d, t) ^ 2 + qA (d, t) ^ 2) =
        ∫ t in l..S, pU (d, t) ^ 2 + qU (d, t) ^ 2) ∧
      (∫ d in a..b, cA (d, l) * qA (d, l) ^ 2) = ∫ d in a..b, cU (d, l) * qU (d, l) ^ 2 := by
  intro D zA zU νA νU uA uU vB vV ρA ρU hχ ζA ζU pA pU qA qU cA cU
  have hpoint (z : ℝ × ℝ) (hz : z ∈ D) : χA z = χU z ∧
      x.1 (uA z) (vB z) = y.1 (uU z) (vV z) ∧
      x.2.1 (uA z) (vB z) = y.2.1 (uU z) (vV z) ∧ ζA z = ζU z := by
    obtain ⟨huA, huU, htB, htV, hρ⟩ := hχ z hz
    have heq : x.1 (uA z) ⟨z.2, htB⟩ 0 = y.1 (uU z) ⟨z.2, htV⟩ 0 := by
      simpa only [ρA, ρU, vB, vV, projIcc_of_mem hB htB, projIcc_of_mem hV htV] using hρ
    have he := hx.horizon_radius_scalar_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hφ hrd
      hp₀ hfA hfU hy (uA z) (uU z) htB htV heq
    simpa only [ζA, ζU, νA, νU, zA, zU, uA, uU, vB, vV,
      projIcc_of_mem hA huA, projIcc_of_mem hU huU, projIcc_of_mem hB htB, projIcc_of_mem hV htV] using he
  have hp : EqOn pA pU D := by
    intro z hz
    obtain ⟨_, hr, hw, _⟩ := hpoint z hz
    dsimp only [pA, pU, ρA, ρU]
    rw [hr, hw]
  have hq : EqOn qA qU D := by
    intro z hz
    obtain ⟨hu, hr, _, hζ⟩ := hpoint z hz
    dsimp only [qA, qU, ρA, ρU]
    rw [hu, hr, hζ]
  have hcv : EqOn cA cU D := by
    intro z hz
    dsimp only [cA, cU]
    rw [(hpoint z hz).2.2.1]
  refine ⟨hp, hq, hcv, ?_, ?_⟩
  · intro d hd
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlS] at ht
    have hdt : (d, t) ∈ D := ⟨hd, ht⟩
    change pA (d, t) ^ 2 + qA (d, t) ^ 2 = pU (d, t) ^ 2 + qU (d, t) ^ 2
    rw [hp hdt, hq hdt]
  · apply intervalIntegral.integral_congr
    intro d hd
    rw [uIcc_of_le hab] at hd
    have hdl : (d, l) ∈ D := ⟨hd, le_rfl, hlS⟩
    change cA (d, l) * qA (d, l) ^ 2 = cU (d, l) * qU (d, l) ^ 2
    rw [hcv hdl, hq hdl]

end CauchyHorizon
