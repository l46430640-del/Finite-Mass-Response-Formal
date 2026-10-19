import CauchyHorizon.Reduced.CoordinateMetric
import CauchyHorizon.Geometry.SphericalChart

/-! The coordinate metric of the nonlinear solution is the actual spherical warped metric. -/

open Set
open scoped Manifold

namespace CauchyHorizon

theorem coordinateMetric_spherical_pullback {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ))
    (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (a b : Fin 4 → ℝ) :
    sphereSpacetimeMetric
      (Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2))
      (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2)
      (rotatedSphericalMap A (θ + w.2.1, w.2.2))
      (sphericalSpacetimeDifferential A (θ + w.2.1, w.2.2) a)
      (sphericalSpacetimeDifferential A (θ + w.2.1, w.2.2) b) =
        ∑ i, ∑ j, coordinateMetric hU hV x θ w i j * a i * b j :=
  sphereSpacetimeMetric_pullback _ _ A _ a b

theorem coordinateMetric_spherical_pullback_shift {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ))
    (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (a b : Fin 4 → ℝ) :
    sphereSpacetimeMetric
      (Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2))
      (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2)
      (rotatedSphericalMap A (θ + w.2.1, φ + w.2.2))
      (sphericalSpacetimeDifferential A (θ + w.2.1, φ + w.2.2) a)
      (sphericalSpacetimeDifferential A (θ + w.2.1, φ + w.2.2) b) =
        ∑ i, ∑ j, coordinateMetric hU hV x θ w i j * a i * b j :=
  sphereSpacetimeMetric_pullback _ _ A _ a b

theorem coordinateMetric_spherical_chart_pullback {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ))
    (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hw : (θ + w.2.1, φ + w.2.2) ∈ c.target) (a b : Fin 4 → ℝ) :
    sphereSpacetimeMetric
      (Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2))
      (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2)
      (c.symm (θ + w.2.1, φ + w.2.2))
      ((a 0, a 1), mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) c.symm (θ + w.2.1, φ + w.2.2) (a 2, a 3))
      ((b 0, b 1), mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) c.symm (θ + w.2.1, φ + w.2.2) (b 2, b 3)) =
        ∑ i, ∑ j, coordinateMetric hU hV x θ w i j * a i * b j :=
  spherical_chart_metric_pullback _ _ A c hc hw a b

end CauchyHorizon
