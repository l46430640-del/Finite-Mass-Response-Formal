import CauchyHorizon.Characteristic.OutgoingConstraint
import CauchyHorizon.Reduced.MassFlux

/-! Mass traces and fluxes with the prescribed Lp incoming and horizon data. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {M e Λ U V : ℝ} {h r : ℝ → ℝ}
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

include hφ hrd hx

theorem IsWaveIntegral.horizon_mass_trace (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    massField e Λ x.1 x.2.1 N hx.choose ⟨0, le_rfl, hU⟩ v = horizonMass M h v := by
  dsimp only
  have hR : x.1 ⟨0, le_rfl, hU⟩ v 0 = r v :=
    congrArg (fun z : WaveVector => z 0) ((hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v)
  have hw := waveIteration_outgoing_derivative hU hV e Λ
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x hx.choose
  rw [hx.choose_spec] at hw
  have hL : x.2.1 ⟨0, le_rfl, hU⟩ v 0 = horizonFunction (r v) (horizonMass M h v) e Λ := by
    rw [hw]
    rfl
  have hg := hx.horizon_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
  rw [massField_apply, renormalizedMass, Real.exp_neg, hg.2.1, hR, hL]
  unfold horizonFunction
  field_simp [hr0 v, ne_of_lt hg.1]
  ring

theorem IsWaveIntegral.outgoing_mass_derivative (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    HasDerivWithinAt (intervalExtension hV (m u))
      ((x.1 u v 0 * x.2.1 u v 1) ^ 2 / (2 * (-Real.exp (x.1 u v 2) / (4 * N u v)))) (Icc 0 V) v := by
  have hd := hx.mass_longitudinal_derivative hx.choose u v
    (hx.outgoing_radial_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v.property)
  apply hd.congr_deriv
  exact (renormalizedMass_flux_forms (hx.choose u v)
    (ne_of_lt (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1) (x.2.1 u v 0) _ _ e Λ).1

theorem IsWaveIntegral.incoming_mass_derivative :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      let u := projIcc 0 U hU t
      HasDerivWithinAt (fun s => intervalExtension hU m s v)
        (horizonFunction (x.1 u v 0) (m u v) e Λ * (x.1 u v 0 * x.2.2 t v 1) ^ 2 / (2 * N u v))
        (Icc 0 U) t := by
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)
  filter_upwards [hx.mass_horizontal_derivative hx.choose rfl hn hl] with t ht
  intro v
  apply (ht v).congr_deriv
  exact (renormalizedMass_flux_forms (hx.choose (projIcc 0 U hU t) v)
    (ne_of_lt (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf (projIcc 0 U hU t) v).2.2.1)
    _ _ _ e Λ).2

theorem IsWaveIntegral.incoming_mass_integral (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    let J := fun t => -2 * (intervalExtension hU x.1 t v 0) ^ 2 * intervalExtension hU x.2.1 t v 0 *
      Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2
    IntervalIntegrable J volume 0 U ∧ ∀ u : Icc 0 U,
      m u v = horizonMass M h v + ∫ t in (0 : ℝ)..u, J t := by
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)
  obtain ⟨hJ, hmass⟩ := hx.mass_horizontal_integral hx.choose rfl hn hl v
  refine ⟨hJ, fun u => ?_⟩
  rw [hx.horizon_mass_trace hU hV hUR hc hi hrc hr0 hφ hrd hp hf v] at hmass
  exact hmass u

theorem IsWaveIntegral.outgoing_mass_integral (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    m u v = m u ⟨0, le_rfl, hV⟩ + ∫ t in (0 : ℝ)..v,
      -2 * (intervalExtension hV (x.1 u) t 0) ^ 2 * intervalExtension hV (N u) t *
        Real.exp (-intervalExtension hV (x.1 u) t 2) * (intervalExtension hV (x.2.1 u) t 1) ^ 2 :=
  hx.mass_longitudinal_integral hx.choose u
    (fun v => hx.outgoing_radial_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v.property) v

theorem IsWaveIntegral.mass_monotone (u : Icc 0 U) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    Monotone (massField e Λ x.1 x.2.1 N hx.choose u) := by
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField e Λ x.1 x.2.1 N hx.choose
  change Monotone (m u)
  let J := fun t => (intervalExtension hV (x.1 u) t 0 * intervalExtension hV (x.2.1 u) t 1) ^ 2 /
    (2 * (-Real.exp (intervalExtension hV (x.1 u) t 2) / (4 * intervalExtension hV (N u) t)))
  have hm : MonotoneOn (intervalExtension hV (m u)) (Icc 0 V) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := J) (convex_Icc 0 V)
      (intervalExtension hV (m u)).continuous.continuousOn
    · intro t ht
      have ht' := interior_subset ht
      have hd := hx.outgoing_mass_derivative hU hV hUR hc hi hrc hr0 hφ hrd hp hf u ⟨t, ht'⟩
      have he : HasDerivWithinAt (intervalExtension hV (m u)) (J t) (Icc 0 V) t := by
        simpa only [J, intervalExtension_apply, projIcc_of_mem hV ht'] using hd
      exact he.mono interior_subset
    · intro t _ht
      exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
        (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u (projIcc 0 V hV t)).2.2.2.1.le)
  intro a b hab
  simpa only [intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property] using
    hm a.property b.property hab

end CauchyHorizon
