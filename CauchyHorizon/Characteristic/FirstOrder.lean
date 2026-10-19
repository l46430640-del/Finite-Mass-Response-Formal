import CauchyHorizon.Characteristic.OutgoingData
import CauchyHorizon.Characteristic.MassFlux
import CauchyHorizon.Reduced.MassRadialRate
import CauchyHorizon.Reduced.KappaRegularity
import CauchyHorizon.Reduced.ScalarTransport

/-! The first-order system for the actual characteristic development, with its mixed regularity. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

def HasFirstOrderEquations {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (x : WaveState U V) : Prop :=
  ∃ hr : ∀ u v, x.1 u v 0 ≠ 0,
    let N := radialNuField hV e Λ zIn x.1 hr
    let m := massField e Λ x.1 x.2.1 N hr
    let κ := fun u (v : Icc 0 V) => -Real.exp (intervalExtension hU x.1 u v 2) /
      (4 * intervalExtension hU N u v)
    let θ := fun u (v : Icc 0 V) => intervalExtension hU x.1 u v 0 *
      intervalExtension hU x.2.1 u v 1
    let ζ := fun u (v : Icc 0 V) => intervalExtension hU x.1 u v 0 * x.2.2 u v 1
    (∀ (u : Icc 0 U) (v : Icc 0 V),
      0 < x.1 u v 0 ∧ N u v < 0 ∧ 0 < κ u v ∧
      HasDerivWithinAt (intervalExtension hV (x.1 u)) (x.2.1 u v) (Icc 0 V) v ∧
      HasDerivWithinAt (fun t => intervalExtension hU x.1 t v 0) (N u v) (Icc 0 U) u ∧
      x.2.1 u v 0 = κ u v * horizonFunction (x.1 u v 0) (m u v) e Λ ∧
      HasDerivWithinAt (intervalExtension hV (N u))
        (2 * κ u v * horizonK (x.1 u v 0) (m u v) e Λ * N u v) (Icc 0 V) v ∧
      HasDerivWithinAt (fun t => intervalExtension hU x.2.1 t v 0)
        (2 * κ u v * horizonK (x.1 u v 0) (m u v) e Λ * N u v) (Icc 0 U) u ∧
      HasDerivWithinAt (intervalExtension hV (m u)) (θ u v ^ 2 / (2 * κ u v)) (Icc 0 V) v) ∧
    (∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (intervalExtension hU x.1) (x.2.2 u) (Icc 0 U) u ∧
      ∀ v : Icc 0 V,
        HasDerivWithinAt (fun t => θ t v)
          (-intervalExtension hU x.2.1 u v 0 * ζ u v / intervalExtension hU x.1 u v 0) (Icc 0 U) u ∧
        HasDerivWithinAt (fun t => ζ u (projIcc 0 V hV t))
          (-intervalExtension hU N u v * θ u v / intervalExtension hU x.1 u v 0) (Icc 0 V) v ∧
        HasDerivWithinAt (fun t => intervalExtension hU m t v)
          (horizonFunction (intervalExtension hU x.1 u v 0) (intervalExtension hU m u v) e Λ *
            ζ u v ^ 2 / (2 * intervalExtension hU N u v)) (Icc 0 U) u) ∧
    ∀ v : Icc 0 V, AbsolutelyContinuousOnInterval (fun u => κ u v) 0 U ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), HasDerivWithinAt (fun t => κ t v)
        (κ u v * ζ u v ^ 2 / (intervalExtension hU x.1 u v 0 * intervalExtension hU N u v))
        (Icc 0 U) u

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.first_order_equations (B : Background) {s l U V : ℝ}
    (D : AdmissibleOutgoingData B s l) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < D.radius 0)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi D.tail D.radius 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V D.tail_continuous
        (horizon_mass_integrable D.rate_pos D.upper_nonneg D.tail_continuous D.tail_bound)
        D.radius_continuous (fun v => ((sub_pos.2 D.deviation_lt).trans_le (D.radius_lower v)).ne'))
      (incomingWaveVelocity hUR hp hf) x) :
    HasFirstOrderEquations hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi D.tail D.radius 0)) x := by
  let hi := horizon_mass_integrable D.rate_pos D.upper_nonneg D.tail_continuous D.tail_bound
  let hr0 := fun v => ((sub_pos.2 D.deviation_lt).trans_le (D.radius_lower v)).ne'
  have hφ := horizonPhi_integrable D.rate_pos D.upper_nonneg (sub_pos.2 D.deviation_lt)
    D.tail_continuous D.radius_continuous D.tail_bound D.radius_lower
  let zIn := incomingWaveCurve hU hUR hp hf (horizonPhi D.tail D.radius 0)
  let N := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 N hx.choose
  obtain ⟨hinu, hinell⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi D.tail D.radius 0)
  have hg := hx.interior_gauge hU hV hUR D.tail_continuous hi D.radius_continuous hr0
    hφ D.radius_derivative hp hf
  have hN (u : Icc 0 U) (v : Icc 0 V) : N u v ≠ 0 := (hg u v).2.2.1.ne
  have hrate (u : Icc 0 U) (v : Icc 0 V) :
      radialSourceField B.charge B.cosmological x.1 x.2.1 N hx.choose u v =
        2 * (-Real.exp (x.1 u v 2) / (4 * N u v)) *
          horizonK (x.1 u v 0) (m u v) B.charge B.cosmological * N u v := by
    have he : Real.exp (x.1 u v 2) * radialPotential (x.1 u v 0) B.charge B.cosmological / N u v -
        x.2.1 u v 0 / x.1 u v 0 = 2 * (-Real.exp (x.1 u v 2) / (4 * N u v)) *
          horizonK (x.1 u v 0) (m u v) B.charge B.cosmological :=
      (renormalizedMass_first_order (hx.choose u v) (hN u v)
        (x.2.1 u v 0) (x.1 u v 2) B.charge B.cosmological).2
    rw [← he, radialSourceField_apply]
    field_simp [hN u v]
  refine ⟨hx.choose, ?_, ?_, ?_⟩
  · intro u v
    simp only [intervalExtension_apply, projIcc_of_mem hU u.property]
    refine ⟨(hg u v).2.1, (hg u v).2.2.1, (hg u v).2.2.2.1,
      hx.longitudinal_derivative u v.property,
      hx.radial_hasDerivWithinAt hx.choose rfl hinu v u.property,
      massField_lambda_eq_kappa x.1 x.2.1 N hx.choose hN u v,
      (hx.radialNu_hasDerivWithinAt hx.choose u v).congr_deriv (hrate u v),
      (hx.lambda_hasDerivWithinAt hx.choose hinu v u.property).congr_deriv (hrate u v), ?_⟩
    exact hx.outgoing_mass_derivative hU hV hUR D.tail_continuous hi D.radius_continuous hr0
      hφ D.radius_derivative hp hf u v
  · filter_upwards [hx.horizontal_derivative rfl, hx.theta_transport rfl, hx.zeta_transport hx.choose hinu,
      hx.incoming_mass_derivative hU hV hUR D.tail_continuous hi D.radius_continuous hr0
        hφ D.radius_derivative hp hf] with u hu hθ hζ hm
    refine ⟨hu, fun v => ⟨?_, ?_, hm v⟩⟩
    · apply (hθ v).congr_deriv
      simp only [intervalExtension_apply]
      field_simp [hx.choose (projIcc 0 U hU u) v]
    · let a := projIcc 0 U hU u
      have hd := (continuousPrimitive_hasDerivWithinAt hV
        (scalarTransportSource N x.2.1 a) v.property).const_add (zIn a 0 * incomingWaveVelocity hUR hp hf u 1)
      have he := hd.congr_of_mem (f₁ := fun t =>
        intervalExtension hU x.1 u (projIcc 0 V hV t) 0 * x.2.2 u (projIcc 0 V hV t) 1)
        (fun t ht => by
          have hz := hζ ⟨t, ht⟩
          change x.1 a ⟨t, ht⟩ 0 * x.2.2 u ⟨t, ht⟩ 1 =
            zIn a 0 * incomingWaveVelocity hUR hp hf u 1 +
              continuousPrimitive hV (scalarTransportSource N x.2.1 a) ⟨t, ht⟩ at hz
          simpa only [intervalExtension_apply, projIcc_of_mem hV ht, a] using hz) v.property
      apply he.congr_deriv
      change -N a v * x.2.1 a v 1 = -N a v * (x.1 a v 0 * x.2.1 a v 1) / x.1 a v 0
      field_simp [hx.choose a v]
  · intro v
    obtain ⟨hAC, hd⟩ := hx.kappa_horizontal_regular hx.choose rfl hinu hinell hN v
    refine ⟨hAC, ?_⟩
    filter_upwards [hd] with u hu
    apply hu.congr_deriv
    simp only [intervalExtension_apply]
    field_simp [hx.choose (projIcc 0 U hU u) v, hN (projIcc 0 U hU u) v]

end CauchyHorizon
