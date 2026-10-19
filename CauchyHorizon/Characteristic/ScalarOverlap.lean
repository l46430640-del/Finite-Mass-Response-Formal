import CauchyHorizon.Characteristic.PhysicalOverlapNu
import CauchyHorizon.Characteristic.CoordinateOverlap
import CauchyHorizon.Reduced.ScalarTransport

/-! The transported scalar and its radius traces agree on physical overlaps. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_overlap_zeta {M e Λ A B U V : ℝ} {h r : ℝ → ℝ}
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
    let zA := incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0)
    let zU := incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)
    zA ⟨u, huA⟩ 0 * f u + scalarTransportCorrection hB
      (radialNuField hB e Λ zA x.1 hx.choose) x.2.1 ⟨u, huA⟩ ⟨v, hvB⟩ =
    zU ⟨u, huU⟩ 0 * f u + scalarTransportCorrection hV
      (radialNuField hV e Λ zU y.1 hy.choose) y.2.1 ⟨u, huU⟩ ⟨v, hvV⟩ := by
  intro zA zU
  have hinit : zA ⟨u, huA⟩ 0 = zU ⟨u, huU⟩ 0 := by
    simp only [zA, zU, incomingWaveCurve_apply]
  congr 1
  · rw [hinit]
  · change (∫ t in (0 : ℝ)..v, _) = ∫ t in (0 : ℝ)..v, _
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hvB.1] at ht
    have htB : t ∈ Icc 0 B := ⟨ht.1, ht.2.trans hvB.2⟩
    have htV : t ∈ Icc 0 V := ⟨ht.1, ht.2.trans hvV.2⟩
    have hn := hx.horizon_overlap_nu hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy huA huU htB htV
    have hw := (hx.horizon_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy huA huU htB htV).2
    simp only [intervalExtension_apply, projIcc_of_mem hB htB, projIcc_of_mem hV htV]
    change -radialNuField hB e Λ zA x.1 hx.choose ⟨u, huA⟩ ⟨t, htB⟩ * x.2.1 ⟨u, huA⟩ ⟨t, htB⟩ 1 =
      -radialNuField hV e Λ zU y.1 hy.choose ⟨u, huU⟩ ⟨t, htV⟩ * y.2.1 ⟨u, huU⟩ ⟨t, htV⟩ 1
    rw [hn, hw]

theorem IsWaveIntegral.horizon_radius_scalar_overlap {M e Λ A B U V : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hfA : MemLp f p (volume.restrict (Icc 0 A))) (hfU : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState A B} {y : WaveState U V}
    (hx : IsWaveIntegral hA hB e Λ (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ B hc hi hrc hr0) (incomingWaveVelocity hAR hp hfA) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hfU) y)
    (uA : Icc 0 A) (uU : Icc 0 U) {t : ℝ} (htB : t ∈ Icc 0 B) (htV : t ∈ Icc 0 V)
    (heq : x.1 uA ⟨t, htB⟩ 0 = y.1 uU ⟨t, htV⟩ 0) :
    let zA := incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0)
    let zU := incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)
    (uA : ℝ) = (uU : ℝ) ∧ x.1 uA ⟨t, htB⟩ = y.1 uU ⟨t, htV⟩ ∧
      x.2.1 uA ⟨t, htB⟩ = y.2.1 uU ⟨t, htV⟩ ∧
      zA uA 0 * f uA + scalarTransportCorrection hB
        (radialNuField hB e Λ zA x.1 hx.choose) x.2.1 uA ⟨t, htB⟩ =
      zU uU 0 * f uU + scalarTransportCorrection hV
        (radialNuField hV e Λ zU y.1 hy.choose) y.2.1 uU ⟨t, htV⟩ := by
  have hu := hx.horizon_radius_coordinate_unique hA hB hAR hU hV hUR hc hi hrc hr0 hφ hrd
    hp hfA hfU hy uA uU htB htV heq
  rcases uA with ⟨u, huA⟩
  rcases uU with ⟨w, huU⟩
  change u = w at hu
  subst w
  obtain ⟨hz, hw⟩ := hx.horizon_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy huA huU htB htV
  exact ⟨rfl, hz, hw, hx.horizon_overlap_zeta hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy huA huU htB htV⟩

end CauchyHorizon
