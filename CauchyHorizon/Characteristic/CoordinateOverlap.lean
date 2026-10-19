import CauchyHorizon.Characteristic.PhysicalOverlap
import CauchyHorizon.Characteristic.ConstraintWave
import CauchyHorizon.Reduced.RadialLevel

/-! Radius coordinates agree across physical rectangles sharing characteristic data. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_radius_coordinate_unique {M e Λ A B U V : ℝ} {h r : ℝ → ℝ}
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
    (heq : x.1 uA ⟨t, htB⟩ 0 = y.1 uU ⟨t, htV⟩ 0) : (uA : ℝ) = (uU : ℝ) := by
  rcases le_total A U with hAU | hUA
  · have huU : (uA : ℝ) ∈ Icc 0 U := ⟨uA.property.1, uA.property.2.trans hAU⟩
    have hov := congrArg (fun z : WaveVector => z 0)
      (hx.horizon_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy
        uA.property huU htB htV).1
    have ha := hy.radial_strictAnti hy.choose rfl
      (incomingWave_constraint_data hU hUR hp hfU (horizonPhi h r 0)).1 ⟨t, htV⟩
      (fun u => (hy.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU u ⟨t, htV⟩).2.2.1)
    exact congrArg Subtype.val (ha.injective (hov.symm.trans heq))
  · have huA : (uU : ℝ) ∈ Icc 0 A := ⟨uU.property.1, uU.property.2.trans hUA⟩
    have hov := congrArg (fun z : WaveVector => z 0)
      (hx.horizon_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy
        huA uU.property htB htV).1
    have ha := hx.radial_strictAnti hx.choose rfl
      (incomingWave_constraint_data hA hAR hp hfA (horizonPhi h r 0)).1 ⟨t, htB⟩
      (fun u => (hx.interior_gauge hA hB hAR hc hi hrc hr0 hφ hrd hp hfA u ⟨t, htB⟩).2.2.1)
    exact congrArg Subtype.val (ha.injective (heq.trans hov.symm))

end CauchyHorizon
