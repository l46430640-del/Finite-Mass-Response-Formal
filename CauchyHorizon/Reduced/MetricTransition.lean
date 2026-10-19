import CauchyHorizon.Geometry.MetricTransition
import CauchyHorizon.Reduced.CoordinateMetric

/-! Actual weak metric coefficients under the angular chart changes, with chart translations. -/

open Set Filter
open scoped Manifold ContDiff

namespace CauchyHorizon

theorem coordinateMetric_contract {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (v y α : ℝ × ℝ) (a b : Fin 4 → ℝ) :
    let z := x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2)
    (∑ i, ∑ j, coordinateMetric hU hV x α.1 (v, y - α) i j * a i * b j) =
      nullMetricForm (Real.exp (z 2)) (z 0 ^ 2) y a b := by
  have hs : α.1 + (y - α).1 = y.1 := by change α.1 + (y.1 - α.1) = y.1; ring
  simpa only [coordinateMetric, hs] using
    (nullMetricForm_eq_sum (Real.exp (x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2) 2))
      (x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2) 0 ^ 2) y a b).symm

theorem coordinateMetricPartial_contract {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (v y α : ℝ × ℝ) (ξ a b : Fin 4 → ℝ) :
    let z := x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2)
    let p := x.2.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2)
    let q := x.2.2 v.1 (projIcc 0 V hV v.2)
    (∑ k, ξ k * ∑ i, ∑ j, coordinateMetricPartial hU hV x α.1 k (v, y - α) i j * a i * b j) =
      ξ 0 * nullMetricForm (Real.exp (z 2) * q 2) (2 * z 0 * q 0) y a b +
      ξ 1 * nullMetricForm (Real.exp (z 2) * p 2) (2 * z 0 * p 0) y a b +
      z 0 ^ 2 * (2 * Real.sin y.1 * Real.cos y.1) * ξ 2 * a 3 * b 3 := by
  have hs : α.1 + (y - α).1 = y.1 := by change α.1 + (y.1 - α.1) = y.1; ring
  dsimp only [coordinateMetricPartial]
  simp only [hs]
  norm_num [Fin.sum_univ_four, nullMetricForm, nullMetricMatrix, Matrix.diagonal,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide]
  ring

theorem coordinateMetricPartial_transition {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (v y α β : ℝ × ℝ)
    (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hd : EqOn d.symm (rotatedSphericalMap B) d.target)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hdf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    (hy : y ∈ (c.symm.trans d).source) (ξ a b : Fin 4 → ℝ) :
    let t := c.symm.trans d
    let J := fderiv ℝ t y
    let Q := fderiv ℝ (fderiv ℝ t) y (ξ 2, ξ 3)
    let T := angularVectorChange J
    (∑ k, ξ k * ∑ i, ∑ j, coordinateMetricPartial hU hV x α.1 k (v, y - α) i j * a i * b j) =
      (∑ k, T ξ k * ∑ i, ∑ j, coordinateMetricPartial hU hV x β.1 k (v, t y - β) i j * T a i * T b j) +
      (∑ i, ∑ j, coordinateMetric hU hV x β.1 (v, t y - β) i j * angularVectorVariation Q a i * T b j) +
      (∑ i, ∑ j, coordinateMetric hU hV x β.1 (v, t y - β) i j * T a i * angularVectorVariation Q b j) := by
  let z := x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2)
  let p := x.2.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2)
  let q := x.2.2 v.1 (projIcc 0 V hV v.2)
  have hn₀ := nullMetricForm_transition (Real.exp (z 2) * q 2) (2 * z 0 * q 0)
    A B c d hc hd hci hdf hdi hy a b
  have hn₁ := nullMetricForm_transition (Real.exp (z 2) * p 2) (2 * z 0 * p 0)
    A B c d hc hd hci hdf hdi hy a b
  have ha := nullMetricForm_transition_derivative (Real.exp (z 2)) (z 0 ^ 2)
    A B c d hc hd hci hdf hdi hy a b (ξ 2, ξ 3)
  dsimp only
  rw [coordinateMetricPartial_contract, coordinateMetricPartial_contract,
    coordinateMetric_contract, coordinateMetric_contract, hn₀, hn₁]
  change _ = ξ 0 * _ + ξ 1 * _ + _ + _ + _
  dsimp [angularVectorChange, z, p, q] at ha ⊢
  linarith only [ha]

end CauchyHorizon
