import CauchyHorizon.Characteristic.BandOverlap
import CauchyHorizon.Radial.OuterMatching

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon.Tests

section

variable {G : Background} {A B U V : ℝ} {h r : ℝ → ℝ}
  (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0)
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
  {f : ℝ → ℝ} (hfA : MemLp f 4 (volume.restrict (Icc 0 A)))
  (hfU : MemLp f 4 (volume.restrict (Icc 0 U)))
  {x : WaveState A B} {y : WaveState U V}
  (hx : IsWaveIntegral hA hB G.charge G.cosmological
    (incomingWaveCurve hA hAR le_rfl hfA (horizonPhi h r 0))
    (horizonWaveVelocity G.mass G.charge G.cosmological B hc hi hrc hr0)
    (incomingWaveVelocity hAR le_rfl hfA) x)
  (hy : IsWaveIntegral hU hV G.charge G.cosmological
    (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
    (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
    (incomingWaveVelocity hUR le_rfl hfU) y)

-- Rough p=4 data and closed time endpoints are sufficient for pointwise overlap.
example {u t : ℝ} (huA : u ∈ Icc 0 A) (huU : u ∈ Icc 0 U)
    (htB : t ∈ Icc 0 B) (htV : t ∈ Icc 0 V) :
    let zA := incomingWaveCurve hA hAR le_rfl hfA (horizonPhi h r 0)
    let zU := incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)
    zA ⟨u, huA⟩ 0 * f u + scalarTransportCorrection hB
      (radialNuField hB G.charge G.cosmological zA x.1 hx.choose) x.2.1 ⟨u, huA⟩ ⟨t, htB⟩ =
    zU ⟨u, huU⟩ 0 * f u + scalarTransportCorrection hV
      (radialNuField hV G.charge G.cosmological zU y.1 hy.choose) y.2.1 ⟨u, huU⟩ ⟨t, htV⟩ := by
  exact hx.horizon_overlap_zeta hA hB hAR hU hV hUR hc hi hrc hr0 le_rfl hfA hfU hy huA huU htB htV

-- Independently chosen windows restrict to the same energy and bottom inflow.
set_option maxHeartbeats 2000000 in
example (hm : G.criticalExponent < 1) (H : ℝ → ℝ) {a b l S S₁ S₂ R : ℝ}
    (hab : a ≤ b) (hlS : l ≤ S) (hS₁ : S ≤ S₁) (hS₂ : S ≤ S₂)
    (χA χU : ℝ × ℝ → ℝ)
    (hχA : ∀ z ∈ Icc a b ×ˢ Icc l S₁, χA z ∈ Icc 0 A ∧ z.2 ∈ Icc 0 B ∧
      x.1 (projIcc 0 A hA (χA z)) (projIcc 0 B hB z.2) 0 = R - z.1)
    (hχU : ∀ z ∈ Icc a b ×ˢ Icc l S₂, χU z ∈ Icc 0 U ∧ z.2 ∈ Icc 0 V ∧
      y.1 (projIcc 0 U hU (χU z)) (projIcc 0 V hV z.2) 0 = R - z.1) :
    let zA := incomingWaveCurve hA hAR le_rfl hfA (horizonPhi h r 0)
    let zU := incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)
    let νA := radialNuField hB G.charge G.cosmological zA x.1 hx.choose
    let νU := radialNuField hV G.charge G.cosmological zU y.1 hy.choose
    let uA := fun z => projIcc 0 A hA (χA z)
    let uU := fun z => projIcc 0 U hU (χU z)
    let vB := fun z : ℝ × ℝ => projIcc 0 B hB z.2
    let vV := fun z : ℝ × ℝ => projIcc 0 V hV z.2
    let ρA := fun z => x.1 (uA z) (vB z) 0
    let ρU := fun z => y.1 (uU z) (vV z) 0
    let ζA := fun z => zA (uA z) 0 * f (χA z) + scalarTransportCorrection hB νA x.2.1 (uA z) (vB z)
    let ζU := fun z => zU (uU z) 0 * f (χU z) + scalarTransportCorrection hV νU y.2.1 (uU z) (vV z)
    let X := fun r => extendCurve G.radialLength_pos.le (G.radialMode hm).1 (G.event - r)
    let W := fun r => extendCurve G.radialLength_pos.le (G.radialMode hm).2 (G.event - r)
    let pA := fun z : ℝ × ℝ => Real.exp (G.innerRate * z.2) * (ρA z * x.2.1 (uA z) (vB z) 1) - X (ρA z) * H z.2
    let pU := fun z : ℝ × ℝ => Real.exp (G.innerRate * z.2) * (ρU z * y.2.1 (uU z) (vV z) 1) - X (ρU z) * H z.2
    let qA := fun z : ℝ × ℝ => Real.exp (G.innerRate * z.2) * χA z * ζA z / G.criticalWeight (ρA z) - W (ρA z) * H z.2
    let qU := fun z : ℝ × ℝ => Real.exp (G.innerRate * z.2) * χU z * ζU z / G.criticalWeight (ρU z) - W (ρU z) * H z.2
    (∀ d ∈ Icc a b, (∫ t in l..S, pA (d, t) ^ 2 + qA (d, t) ^ 2) =
      ∫ t in l..S, pU (d, t) ^ 2 + qU (d, t) ^ 2) ∧
    (∫ d in a..b, (-1 / x.2.1 (uA (d, l)) (vB (d, l)) 0) * qA (d, l) ^ 2) =
      ∫ d in a..b, (-1 / y.2.1 (uU (d, l)) (vV (d, l)) 0) * qU (d, l) ^ 2 := by
  intro zA zU νA νU uA uU vB vV ρA ρU ζA ζU X W pA pU qA qU
  have hχ (z : ℝ × ℝ) (hz : z ∈ Icc a b ×ˢ Icc l S) :
      χA z ∈ Icc 0 A ∧ χU z ∈ Icc 0 U ∧ z.2 ∈ Icc 0 B ∧ z.2 ∈ Icc 0 V ∧ ρA z = ρU z := by
    have ha := hχA z ⟨hz.1, hz.2.1, hz.2.2.trans hS₁⟩
    have hu := hχU z ⟨hz.1, hz.2.1, hz.2.2.trans hS₂⟩
    exact ⟨ha.1, hu.1, ha.2.1, hu.2.1, ha.2.2.trans hu.2.2.symm⟩
  exact (hx.horizon_band_energy_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hfA hfU hy
    G.innerRate X W G.criticalWeight H hab hlS χA χU hχ).2.2.2

end

end CauchyHorizon.Tests
