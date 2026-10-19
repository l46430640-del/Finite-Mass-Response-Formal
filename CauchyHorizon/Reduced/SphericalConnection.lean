import CauchyHorizon.Geometry.AngularTransition
import CauchyHorizon.Reduced.MetricTransition
import CauchyHorizon.Reduced.CoordinateConnection

/-! The actual weak Levi-Civita coefficients obey the spherical chart transition law. -/

open Set Filter MeasureTheory
open scoped Manifold ContDiff Matrix

namespace CauchyHorizon

theorem coordinateMetric_transition_matrices {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (v y α β : ℝ × ℝ)
    (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hd : EqOn d.symm (rotatedSphericalMap B) d.target)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hdf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    (hy : y ∈ (c.symm.trans d).source) :
    let t := c.symm.trans d
    let J := angularJacobian (fderiv ℝ t y)
    let dJ := angularJacobianDerivative (fderiv ℝ (fderiv ℝ t) y)
    let g := coordinateMetric hU hV x β.1 (v, t y - β)
    let dg := fun k => coordinateMetricPartial hU hV x β.1 k (v, t y - β)
    coordinateMetric hU hV x α.1 (v, y - α) = Jᵀ * g * J ∧
      (fun k => coordinateMetricPartial hU hV x α.1 k (v, y - α)) = metricChangeDerivative g dg J dJ := by
  let t := c.symm.trans d
  let z := x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2)
  constructor
  · ext i j
    have hn := nullMetricForm_transition (Real.exp (z 2)) (z 0 ^ 2)
      A B c d hc hd hci hdf hdi hy (Pi.single i 1) (Pi.single j 1)
    have h := (coordinateMetric_contract hU hV x v (t y) β
      (angularVectorChange (fderiv ℝ t y) (Pi.single i 1))
      (angularVectorChange (fderiv ℝ t y) (Pi.single j 1))).trans
        (hn.trans (coordinateMetric_contract hU hV x v y α (Pi.single i 1) (Pi.single j 1)).symm)
    simpa [matrix_pullback_apply, angularJacobian, Pi.single_apply, t] using h.symm
  · funext k
    ext i j
    have h := coordinateMetricPartial_transition hU hV x v y α β A B c d hc hd hci hdf hdi hy
      (Pi.single k 1) (Pi.single i 1) (Pi.single j 1)
    simpa [metricChangeDerivative_apply, angularJacobian, angularJacobianDerivative,
      Pi.single_apply] using h

theorem coordinateChristoffel_transition {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (v y α β : ℝ × ℝ)
    (hr : x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2) 0 ≠ 0)
    (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hd : EqOn d.symm (rotatedSphericalMap B) d.target)
    (hcf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω c c.source)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hdf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    (hy : y ∈ (c.symm.trans d).source) (hs : Real.sin y.1 ≠ 0)
    (ht : Real.sin ((c.symm.trans d) y).1 ≠ 0) :
    let t := c.symm.trans d
    let J := angularJacobian (fderiv ℝ t y)
    let K := angularJacobian (fderiv ℝ t.symm (t y))
    let dJ := angularJacobianDerivative (fderiv ℝ (fderiv ℝ t) y)
    coordinateChristoffel hU hV x α.1 (v, y - α) =
      connectionChange (coordinateChristoffel hU hV x β.1 (v, t y - β)) J K dJ := by
  let t := c.symm.trans d
  have hgeom (w γ : ℝ × ℝ) (hw : Real.sin w.1 ≠ 0) :
      (coordinateMetric hU hV x γ.1 (v, w - γ))ᵀ = coordinateMetric hU hV x γ.1 (v, w - γ) ∧
      coordinateMetric hU hV x γ.1 (v, w - γ) * coordinateMetricInverse hU hV x γ.1 (v, w - γ) = 1 ∧
      coordinateMetricInverse hU hV x γ.1 (v, w - γ) * coordinateMetric hU hV x γ.1 (v, w - γ) = 1 := by
    have h := nullMetric_geometry
      (Real.exp_pos (x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2) 2))
      (sq_pos_of_ne_zero hr) (sq_pos_of_ne_zero hw)
    have he : γ.1 + (w - γ).1 = w.1 := by change γ.1 + (w.1 - γ.1) = w.1; ring
    simpa only [coordinateMetric, coordinateMetricInverse, he] using
      And.intro h.2.2.2.1 (And.intro h.2.2.2.2.1 h.2.2.2.2.2.1)
  have hgC := hgeom y α hs
  have hgD := hgeom (t y) β ht
  have hΓ : IsMetricConnection (coordinateMetric hU hV x β.1 (v, t y - β))
      (fun k => coordinateMetricPartial hU hV x β.1 k (v, t y - β))
      (coordinateChristoffel hU hV x β.1 (v, t y - β)) := by
    apply christoffel_identities
    · intro i j
      exact congrFun (congrFun hgD.1 j) i
    · exact hgD.2.1
    · intro k i j
      fin_cases k <;> fin_cases i <;> fin_cases j <;> rfl
  have hD := spherical_chart_transition_derivatives c d hcf hci hdf hdi hy
  have hchange := hΓ.change (angularJacobian_mul_eq_one hD.2.1)
    (angularJacobianDerivative_symmetric hD.2.2)
  have hm := coordinateMetric_transition_matrices hU hV x v y α β A B c d hc hd hci hdf hdi hy
  rw [← hm.1, ← hm.2] at hchange
  exact (hchange.eq_christoffel (fun i j => congrFun (congrFun hgC.1 j) i) hgC.2.2).symm

def HasSphericalConnectionTransition {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) : Prop :=
  ∀ (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)),
    EqOn c.symm (rotatedSphericalMap A) c.target →
    EqOn d.symm (rotatedSphericalMap B) d.target →
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω c c.source →
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target →
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source →
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target →
    ∀ (v y α β : ℝ × ℝ), y ∈ (c.symm.trans d).source →
      Real.sin y.1 ≠ 0 → Real.sin ((c.symm.trans d) y).1 ≠ 0 →
      let t := c.symm.trans d
      let J := angularJacobian (fderiv ℝ t y)
      let K := angularJacobian (fderiv ℝ t.symm (t y))
      let dJ := angularJacobianDerivative (fderiv ℝ (fderiv ℝ t) y)
      coordinateChristoffel hU hV x α.1 (v, y - α) =
        connectionChange (coordinateChristoffel hU hV x β.1 (v, t y - β)) J K dJ

theorem IsWaveIntegral.spherical_connection_transition {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) :
    HasSphericalConnectionTransition hU hV x := by
  intro A B c d hc hd hcf hci hdf hdi v y α β hy hs ht
  exact coordinateChristoffel_transition hU hV x v y α β (hx.choose _ _)
    A B c d hc hd hcf hci hdf hdi hy hs ht

end CauchyHorizon
