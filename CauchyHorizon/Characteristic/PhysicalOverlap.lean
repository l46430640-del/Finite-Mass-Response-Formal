import CauchyHorizon.Characteristic.FiniteUniqueness

/-! Physical solutions agree at every common point, without nested rectangles. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_overlap {M e Λ A B U V : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hfA : MemLp f p (volume.restrict (Icc 0 A))) (hfU : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState A B} {y : WaveState U V}
    (hx : IsWaveIntegral hA hB e Λ (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ B hc hi hrc hr0) (incomingWaveVelocity hAR hp hfA) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hfU) y)
    {u v : ℝ} (huA : u ∈ Icc 0 A) (huU : u ∈ Icc 0 U) (hvB : v ∈ Icc 0 B) (hvV : v ∈ Icc 0 V) :
    x.1 ⟨u, huA⟩ ⟨v, hvB⟩ = y.1 ⟨u, huU⟩ ⟨v, hvV⟩ ∧
      x.2.1 ⟨u, huA⟩ ⟨v, hvB⟩ = y.2.1 ⟨u, huU⟩ ⟨v, hvV⟩ := by
  have hx' := hx.horizon_prefix hA hB hAR huA.1 hvB.1 huA.2 hvB.2 hc hi hrc hr0 hp hfA
  have hy' := hy.horizon_prefix hU hV hUR huA.1 hvB.1 huU.2 hvV.2 hc hi hrc hr0 hp hfU
  have heq := hx'.incoming_unique huA.1 hvB.1 (huA.2.trans_lt hAR) hp
    (hfA.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl huA.2) le_rfl)) hy'
  have hz := congrArg (fun z : WaveState u v => z.1 ⟨u, huA.1, le_rfl⟩ ⟨v, hvB.1, le_rfl⟩) heq
  have hw := congrArg (fun z : WaveState u v => z.2.1 ⟨u, huA.1, le_rfl⟩ ⟨v, hvB.1, le_rfl⟩) heq
  change x.1 ⟨0 + u, _⟩ ⟨0 + v, _⟩ = y.1 ⟨0 + u, _⟩ ⟨0 + v, _⟩ at hz
  change x.2.1 ⟨0 + u, _⟩ ⟨0 + v, _⟩ = y.2.1 ⟨0 + u, _⟩ ⟨0 + v, _⟩ at hw
  simpa only [zero_add] using And.intro hz hw

end CauchyHorizon
