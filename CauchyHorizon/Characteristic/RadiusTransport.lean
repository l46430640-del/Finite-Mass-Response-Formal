import CauchyHorizon.Characteristic.OutgoingConstraint
import CauchyHorizon.Reduced.MassRadialRate
import CauchyHorizon.Reduced.RadiusTransport

/-! The fixed-radius inverse-speed identity on the actual characteristic solution. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_radius_transport {M e Λ U V : ℝ} {h r : ℝ → ℝ}
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
    (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ∈ Ioo 0 U) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hl0 : x.2.1 u v 0 ≠ 0) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) /
      (4 * intervalExtension hV (ν u) t)
    let K := horizonK (x.1 u v 0) (massField e Λ x.1 x.2.1 ν hx.choose u v) e Λ
    HasDerivAt κ (κ v * (x.2.1 u v 2 - 2 * κ v * K)) v ∧
      ∀ (S : Set ℝ) (g : ℝ → ℝ), g v = u →
        HasDerivWithinAt g (-x.2.1 u v 0 / ν u v) S v →
        HasDerivWithinAt (fun t => -1 / intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 0)
          ((deriv κ v / κ v) / x.2.1 u v 0 -
            (x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2)) S v := by
  intro ν κ K
  have hn : ν u v ≠ 0 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1.ne
  have hκv : κ v = -Real.exp (x.1 u v 2) / (4 * ν u v) := by
    simp only [κ, intervalExtension_apply, projIcc_of_mem hV v.property]
  have hκn : κ v ≠ 0 := by
    rw [hκv]
    exact div_ne_zero (neg_ne_zero.2 (Real.exp_ne_zero _)) (mul_ne_zero (by norm_num) hn)
  have hsource : radialSourceField e Λ x.1 x.2.1 ν hx.choose u v / ν u v = 2 * κ v * K := by
    have hh := (renormalizedMass_first_order (hx.choose u v) hn (x.2.1 u v 0) (x.1 u v 2) e Λ).2
    rw [radialSourceField_apply, hκv]
    change (Real.exp (x.1 u v 2) * radialPotential (x.1 u v 0) e Λ -
      ν u v * x.2.1 u v 0 / x.1 u v 0) / ν u v = _
    calc
      _ = Real.exp (x.1 u v 2) * radialPotential (x.1 u v 0) e Λ / ν u v -
          x.2.1 u v 0 / x.1 u v 0 := by field_simp [hn]
      _ = _ := hh
  have hdκ := (hx.kappa_longitudinal_derivative hx.choose u v hn).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
  change HasDerivAt κ (κ v * (x.2.1 u v 2 -
    radialSourceField e Λ x.1 x.2.1 ν hx.choose u v / ν u v)) v at hdκ
  rw [hsource] at hdκ
  refine ⟨hdκ, ?_⟩
  intro S g hgv hg
  have hh := hx.inverse_lambda_curve_derivative hx.choose
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1
    (fun q w => hx.outgoing_radial_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp hf q w.property)
    u v hu hv hl0 hgv hg
  apply hh.congr_deriv
  rw [hsource, hdκ.deriv]
  field_simp [hκn, hl0, hx.choose u v]

end CauchyHorizon
