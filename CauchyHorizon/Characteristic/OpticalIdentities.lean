import CauchyHorizon.Characteristic.OutgoingData
import CauchyHorizon.Characteristic.MassFlux
import CauchyHorizon.Reduced.OpticalBoundary

/-! The optical flux, mass and radial product on the same physical development. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

def HasOpticalFluxEquations {U V : ℝ} (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (x : WaveState U V) : Prop :=
  ∃ hr : ∀ u v, x.1 u v 0 ≠ 0,
    let N := radialNuField hV e Λ zIn x.1 hr
    let m := massField e Λ x.1 x.2.1 N hr
    let O := opticalField x
    let J := fun u v => (x.1 u v 0 * x.2.1 u v 1) ^ 2 /
      (x.1 u v 0 * Real.exp (x.1 u v 2))
    ∀ u v,
      horizonFunction (x.1 u v 0) (m u v) e Λ = 4 * N u v * O u v ∧
      HasDerivWithinAt (intervalExtension hV (O u)) (J u v) (Icc 0 V) v ∧
      HasDerivWithinAt (intervalExtension hV (m u)) (-2 * x.1 u v 0 * N u v * J u v) (Icc 0 V) v ∧
      HasDerivWithinAt (fun t => intervalExtension hV (x.1 u) t 0 * intervalExtension hV (N u) t)
        (x.1 u v 0 * Real.exp (x.1 u v 2) * radialPotential (x.1 u v 0) e Λ) (Icc 0 V) v ∧
      (x.2.1 u v 0 < 0 → 0 < O u v ∧ 0 < (4 * O u v)⁻¹ ∧
        (4 * O u v)⁻¹ = N u v / horizonFunction (x.1 u v 0) (m u v) e Λ)

set_option maxHeartbeats 800000 in
theorem IsWaveIntegral.optical_flux_equations (B : Background) {s l U V : ℝ}
    (D : AdmissibleOutgoingData B s l) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < D.radius 0)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi D.tail D.radius 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V D.tail_continuous
        (horizon_mass_integrable D.rate_pos D.upper_nonneg D.tail_continuous D.tail_bound)
        D.radius_continuous (fun v => ((sub_pos.2 D.deviation_lt).trans_le (D.radius_lower v)).ne'))
      (incomingWaveVelocity hUR hp hf) x) :
    HasOpticalFluxEquations hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi D.tail D.radius 0)) x := by
  let hi := horizon_mass_integrable D.rate_pos D.upper_nonneg D.tail_continuous D.tail_bound
  let hr0 := fun v => ((sub_pos.2 D.deviation_lt).trans_le (D.radius_lower v)).ne'
  have hφ := horizonPhi_integrable D.rate_pos D.upper_nonneg (sub_pos.2 D.deviation_lt)
    D.tail_continuous D.radius_continuous D.tail_bound D.radius_lower
  let zIn := incomingWaveCurve hU hUR hp hf (horizonPhi D.tail D.radius 0)
  let N := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 N hx.choose
  refine ⟨hx.choose, fun u v => ?_⟩
  have hN : N u v ≠ 0 := (hx.interior_gauge hU hV hUR D.tail_continuous hi D.radius_continuous hr0
    hφ D.radius_derivative hp hf u v).2.2.1.ne
  have hF : horizonFunction (x.1 u v 0) (m u v) B.charge B.cosmological =
      4 * N u v * opticalField x u v := by
    rw [massField_apply, renormalizedMass_horizonFunction (hx.choose u v), Real.exp_neg]
    change -4 * N u v * x.2.1 u v 0 * (Real.exp (x.1 u v 2))⁻¹ =
      4 * N u v * (-x.2.1 u v 0 / Real.exp (x.1 u v 2))
    ring
  have hz (i : Fin 3) := (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
    (v : ℝ) (hx.longitudinal_derivative u v.property)
  have hl := hx.outgoing_radial_constraint hU hV hUR D.tail_continuous hi D.radius_continuous hr0
    hφ D.radius_derivative hp hf u v.property
  refine ⟨hF, ?_, ?_, ?_, ?_⟩
  · have hd := hl.neg.div ((hz 2).exp) (Real.exp_ne_zero _)
    change HasDerivWithinAt (intervalExtension hV (opticalField x u)) _ (Icc 0 V) v at hd
    apply hd.congr_deriv
    simp only [Function.comp_apply, Pi.neg_apply, intervalExtension_apply,
      projIcc_of_mem hV v.property, ContinuousLinearMap.proj_apply]
    field_simp [hx.choose u v, Real.exp_ne_zero]
    ring
  · have hd := hx.mass_longitudinal_derivative hx.choose u v hl
    apply hd.congr_deriv
    rw [Real.exp_neg]
    field_simp [hx.choose u v, Real.exp_ne_zero]
  · have hd := (hz 0).mul (hx.radialNu_hasDerivWithinAt hx.choose u v)
    apply hd.congr_deriv
    simp only [Function.comp_apply, intervalExtension_apply, projIcc_of_mem hV v.property,
      ContinuousLinearMap.proj_apply, radialSourceField_apply]
    field_simp [hx.choose u v]
    ring
  · intro hlneg
    have hO : 0 < opticalField x u v := div_pos (neg_pos.2 hlneg) (Real.exp_pos _)
    refine ⟨hO, inv_pos.2 (mul_pos (by norm_num) hO), ?_⟩
    rw [hF]
    field_simp [hN, hO.ne']
    rfl

end CauchyHorizon
