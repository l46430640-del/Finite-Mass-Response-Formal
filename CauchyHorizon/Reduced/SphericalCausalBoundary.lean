import CauchyHorizon.Reduced.IntegralMap
import CauchyHorizon.Geometry.LocalCauchyHorizon

/-! Causal identity for the metric of the same crossing solution. -/

open Set

namespace CauchyHorizon

noncomputable def crossingSpacetimeField {W L : ℝ} (hW : 0 ≤ W) (hL : 0 ≤ L)
    (y : WaveState W L) (va ua : ℝ) (p : SphericalSpacetime) : WaveVector :=
  y.1 (projIcc 0 W hW (p.1.1 - va)) (projIcc 0 L hL (p.1.2 - ua))

def HasSphericalCauchyHorizon {W L : ℝ} (hW : 0 ≤ W) (hL : 0 ≤ L)
    (y : WaveState W L) (va ua : ℝ) (S : Set SphericalSpacetime) : Prop :=
  let M := sphericalOpenRectangle va (va + W) ua (ua + L)
  let z := crossingSpacetimeField hW hL y va ua
  let H := fun p => Real.exp (z p 2)
  let R := fun p => z p 0 ^ 2
  futureDomainOfDependence M H R S = S ∧
    futureCauchyHorizon M H R S = ({0} ×ˢ Ioo ua (ua + L)) ×ˢ univ

theorem crossing_spherical_cauchy_horizon {W L va ua : ℝ} {hW : 0 ≤ W} {hL : 0 ≤ L}
    (y : WaveState W L) (ha : va < 0) (hb : 0 < va + W) (hLp : 0 < L) :
    HasSphericalCauchyHorizon hW hL y va ua (sphericalOpenRectangle va 0 ua (ua + L)) :=
  sphericalRectangle_cauchy_horizon ha hb (by linarith)
    (fun _ _ => Real.exp_pos _) (fun _ _ => sq_nonneg _)

end CauchyHorizon
