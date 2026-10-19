import CauchyHorizon.Characteristic.PhysicalOverlap

/-! The recovered transverse radial derivative also agrees on physical overlaps. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_overlap_nu {M e Λ A B U V : ℝ} {h r : ℝ → ℝ}
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
    radialNuField hB e Λ (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0)) x.1 hx.choose ⟨u, huA⟩ ⟨v, hvB⟩ =
      radialNuField hV e Λ (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) y.1 hy.choose ⟨u, huU⟩ ⟨v, hvV⟩ := by
  have hz := (hx.horizon_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy huA huU hvB hvV).1
  have hinit : incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0) ⟨u, huA⟩ 0 =
      incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0) ⟨u, huU⟩ 0 := by
    rw [incomingWaveCurve_apply, incomingWaveCurve_apply]
  have hint : continuousPrimitive hB (radialFluxField e Λ x.1 hx.choose ⟨u, huA⟩) ⟨v, hvB⟩ =
      continuousPrimitive hV (radialFluxField e Λ y.1 hy.choose ⟨u, huU⟩) ⟨v, hvV⟩ := by
    change (∫ t in (0 : ℝ)..v, intervalExtension hB (radialFluxField e Λ x.1 hx.choose ⟨u, huA⟩) t) =
      ∫ t in (0 : ℝ)..v, intervalExtension hV (radialFluxField e Λ y.1 hy.choose ⟨u, huU⟩) t
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hvB.1] at ht
    have htB : t ∈ Icc 0 B := ⟨ht.1, ht.2.trans hvB.2⟩
    have htV : t ∈ Icc 0 V := ⟨ht.1, ht.2.trans hvV.2⟩
    have he := (hx.horizon_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy huA huU htB htV).1
    simp only [intervalExtension_apply, projIcc_of_mem hB htB, projIcc_of_mem hV htV, radialFluxField_apply, he]
  rw [radialNuField_apply, radialNuField_apply, hinit, hint, hz]

end CauchyHorizon
