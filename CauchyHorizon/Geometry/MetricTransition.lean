import CauchyHorizon.Geometry.SphericalChart
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Differentiate the angular metric identity while allowing arbitrary null coefficients. -/

open Set Filter
open scoped Manifold ContDiff Topology

namespace CauchyHorizon

noncomputable def nullMetricForm (H R : ℝ) (y : ℝ × ℝ) (a b : Fin 4 → ℝ) : ℝ :=
  -(H / 2) * (a 0 * b 1 + a 1 * b 0) + R * (a 2 * b 2 + Real.sin y.1 ^ 2 * a 3 * b 3)

theorem nullMetricForm_eq_sum (H R : ℝ) (y : ℝ × ℝ) (a b : Fin 4 → ℝ) :
    nullMetricForm H R y a b = ∑ i, ∑ j, nullMetricMatrix H R (Real.sin y.1 ^ 2) i j * a i * b j := by
  norm_num [nullMetricForm, nullMetricMatrix, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring

def angularVectorVariation (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (a : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![0, 0, (L (a 2, a 3)).1, (L (a 2, a 3)).2]

theorem angularVectorChange_hasDerivAt {D : ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    {D' : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)} {t : ℝ} (hD : HasDerivAt D D' t) (a : Fin 4 → ℝ) :
    HasDerivAt (fun s => angularVectorChange (D s) a) (angularVectorVariation D' a) t := by
  have h := hD.clm_apply (hasDerivAt_const t (a 2, a 3))
  simp only [map_zero, add_zero] at h
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · exact hasDerivAt_const t (a 0)
  · exact hasDerivAt_const t (a 1)
  · exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h
  · exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t h

theorem nullMetricForm_hasDerivAt (H R : ℝ) {Y : ℝ → ℝ × ℝ} {Y' : ℝ × ℝ}
    {a b : ℝ → Fin 4 → ℝ} {a' b' : Fin 4 → ℝ} {t : ℝ}
    (hY : HasDerivAt Y Y' t) (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => nullMetricForm H R (Y s) (a s) (b s))
      (nullMetricForm H R (Y t) a' (b t) + nullMetricForm H R (Y t) (a t) b' +
        R * (2 * Real.sin (Y t).1 * Real.cos (Y t).1) * Y'.1 * a t 3 * b t 3) t := by
  have hY₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hY
  have hA := hasDerivAt_pi.1 ha
  have hB := hasDerivAt_pi.1 hb
  have hN := (((hA 0).mul (hB 1)).add ((hA 1).mul (hB 0))).const_mul (-(H / 2))
  have hS := (((hA 2).mul (hB 2)).add (((hY₁.sin.pow 2).mul (hA 3)).mul (hB 3))).const_mul R
  apply (hN.add hS).congr_deriv
  dsimp [nullMetricForm]
  ring

theorem nullMetricForm_transition (H R : ℝ)
    (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hd : EqOn d.symm (rotatedSphericalMap B) d.target)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hdf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    {y : ℝ × ℝ} (hy : y ∈ (c.symm.trans d).source) (a b : Fin 4 → ℝ) :
    let t := c.symm.trans d
    nullMetricForm H R (t y) (angularVectorChange (fderiv ℝ t y) a)
      (angularVectorChange (fderiv ℝ t y) b) = nullMetricForm H R y a b := by
  let t := c.symm.trans d
  have hC := spherical_chart_metric_pullback H R A c hc hy.1 a b
  have hD := spherical_chart_metric_pullback H R B d hd (d.map_source hy.2)
    (angularVectorChange (fderiv ℝ t y) a) (angularVectorChange (fderiv ℝ t y) b)
  rw [← nullMetricForm_eq_sum] at hC hD
  apply hD.symm.trans
  apply Eq.trans _ hC
  change sphereSpacetimeMetric H R (d.symm (t y))
    (sphericalChartDifferential d (t y) (angularVectorChange (fderiv ℝ t y) a))
    (sphericalChartDifferential d (t y) (angularVectorChange (fderiv ℝ t y) b)) = _
  rw [sphericalChartDifferential_transition c d hci hdf hdi hy a,
    sphericalChartDifferential_transition c d hci hdf hdi hy b]
  let a' : (ℝ × ℝ) × EuclideanSpace ℝ (Fin 2) := sphericalChartDifferential c y a
  let b' : (ℝ × ℝ) × EuclideanSpace ℝ (Fin 2) := sphericalChartDifferential c y b
  exact congrArg (fun p : UnitSphere => sphereSpacetimeMetric H R p a' b') (d.left_inv hy.2)

theorem nullMetricForm_transition_derivative (H R : ℝ)
    (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hd : EqOn d.symm (rotatedSphericalMap B) d.target)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hdf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    {y : ℝ × ℝ} (hy : y ∈ (c.symm.trans d).source) (a b : Fin 4 → ℝ) (h : ℝ × ℝ) :
    let t := c.symm.trans d
    let J := fderiv ℝ t y
    let Q := fderiv ℝ (fderiv ℝ t) y h
    R * (2 * Real.sin y.1 * Real.cos y.1) * h.1 * a 3 * b 3 =
      R * (2 * Real.sin (t y).1 * Real.cos (t y).1) * (J h).1 *
        angularVectorChange J a 3 * angularVectorChange J b 3 +
      nullMetricForm H R (t y) (angularVectorVariation Q a) (angularVectorChange J b) +
      nullMetricForm H R (t y) (angularVectorChange J a) (angularVectorVariation Q b) := by
  let t := c.symm.trans d
  let z : ℝ → ℝ × ℝ := fun s => y + s • h
  have hz : HasDerivAt z h 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add y using 1 <;>
      first | rfl | simp
  have hz0 : z 0 = y := by simp [z]
  have ht : ContDiffAt ℝ ω t y :=
    (spherical_chart_transition c d hci hdf).contDiffAt (t.open_source.mem_nhds hy)
  have ht' := ht.differentiableAt (by simp)
  have hJ := (ht.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have htz := ht'.hasFDerivAt.comp_hasDerivAt_of_eq 0 hz hz0.symm
  have hJz := hJ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hz hz0.symm
  have hleft := nullMetricForm_hasDerivAt H R hz (hasDerivAt_const 0 a) (hasDerivAt_const 0 b)
  have hright := nullMetricForm_hasDerivAt H R htz
    (angularVectorChange_hasDerivAt hJz a) (angularVectorChange_hasDerivAt hJz b)
  have heq : (fun s => nullMetricForm H R (t (z s))
      (angularVectorChange (fderiv ℝ t (z s)) a) (angularVectorChange (fderiv ℝ t (z s)) b))
      =ᶠ[𝓝 0] (fun s => nullMetricForm H R (z s) a b) := by
    have hmem := hz.continuousAt.preimage_mem_nhds
      (show t.source ∈ 𝓝 (z 0) by rw [hz0]; exact t.open_source.mem_nhds hy)
    filter_upwards [hmem] with s hs
    exact nullMetricForm_transition H R A B c d hc hd hci hdf hdi hs a b
  have he := hright.deriv.symm.trans (heq.deriv_eq.trans hleft.deriv)
  simp only [hz0, Function.comp_apply, nullMetricForm, Pi.zero_apply, zero_mul,
    mul_zero, zero_add, add_zero] at he ⊢
  linarith only [he]

end CauchyHorizon
