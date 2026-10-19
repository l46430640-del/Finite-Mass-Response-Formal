import CauchyHorizon.Geometry.SphericalChart
import CauchyHorizon.Geometry.ElectricField

/-! The electric scalar Einstein source as a bilinear form on the actual sphere tangent space. -/

open Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace

namespace CauchyHorizon

noncomputable def sphereEinsteinSource (H r e Λ pV pu : ℝ) (p : UnitSphere) :
    ((ℝ × ℝ) × TangentSpace (𝓡 2) p) →ₗ[ℝ] ((ℝ × ℝ) × TangentSpace (𝓡 2) p) →ₗ[ℝ] ℝ := by
  apply LinearMap.mk₂ ℝ (fun a b =>
    2 * (pV * a.1.1 + pu * a.1.2) * (pV * b.1.1 + pu * b.1.2) +
      sphereSpacetimeMetric ((Λ - e ^ 2 / r ^ 4) * H) (Λ * r ^ 2 + e ^ 2 / r ^ 2) p a b)
  · intro a b c
    simp only [sphereSpacetimeMetric, unitSphereMetric, Prod.fst_add, Prod.snd_add, map_add,
      inner_add_left]
    ring
  · intro t a b
    simp only [sphereSpacetimeMetric, unitSphereMetric, Prod.smul_fst, Prod.smul_snd,
      map_smul, real_inner_smul_left, smul_eq_mul]
    ring
  · intro a b c
    simp only [sphereSpacetimeMetric, unitSphereMetric, Prod.fst_add, Prod.snd_add, map_add,
      inner_add_right]
    ring
  · intro t a b
    simp only [sphereSpacetimeMetric, unitSphereMetric, Prod.smul_fst, Prod.smul_snd,
      map_smul, real_inner_smul_right, smul_eq_mul]
    ring

theorem sphereEinsteinSource_apply (H r e Λ pV pu : ℝ) (p : UnitSphere)
    (a b : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphereEinsteinSource H r e Λ pV pu p a b =
      2 * (pV * a.1.1 + pu * a.1.2) * (pV * b.1.1 + pu * b.1.2) +
        sphereSpacetimeMetric ((Λ - e ^ 2 / r ^ 4) * H) (Λ * r ^ 2 + e ^ 2 / r ^ 2) p a b := rfl

theorem sphereEinsteinSource_symmetric (H r e Λ pV pu : ℝ) (p : UnitSphere)
    (a b : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphereEinsteinSource H r e Λ pV pu p a b = sphereEinsteinSource H r e Λ pV pu p b a := by
  simp only [sphereEinsteinSource_apply, sphereSpacetimeMetric, unitSphereMetric]
  rw [real_inner_comm]
  ring

theorem sphereEinsteinSource_chart_transition (H r e Λ pV pu : ℝ)
    (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hd : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    {y : ℝ × ℝ} (hy : y ∈ (c.symm.trans d).source) (a b : Fin 4 → ℝ) :
    let t := c.symm.trans d
    sphereEinsteinSource H r e Λ pV pu (d.symm (t y))
      (sphericalChartDifferential d (t y) (angularVectorChange (fderiv ℝ t y) a))
      (sphericalChartDifferential d (t y) (angularVectorChange (fderiv ℝ t y) b)) =
        sphereEinsteinSource H r e Λ pV pu (c.symm y)
          (sphericalChartDifferential c y a) (sphericalChartDifferential c y b) := by
  dsimp only
  rw [sphericalChartDifferential_transition c d hci hd hdi hy a,
    sphericalChartDifferential_transition c d hci hd hdi hy b]
  let a' : (ℝ × ℝ) × EuclideanSpace ℝ (Fin 2) := sphericalChartDifferential c y a
  let b' : (ℝ × ℝ) × EuclideanSpace ℝ (Fin 2) := sphericalChartDifferential c y b
  exact congrArg (fun p : UnitSphere => sphereEinsteinSource H r e Λ pV pu p a' b') (d.left_inv hy.2)

theorem sphereEinsteinSource_chart_pullback {H r e Λ pV pu : ℝ}
    (hH : H ≠ 0) (hr : r ≠ 0) (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target) {y : ℝ × ℝ} (hy : y ∈ c.target)
    (hs : Real.sin y.1 ≠ 0) (a b : Fin 4 → ℝ) :
    let g := nullMetricMatrix H (r ^ 2) (Real.sin y.1 ^ 2)
    let gInv := nullMetricInverse H (r ^ 2) (Real.sin y.1 ^ 2)
    let F := electricTwoForm (e * H / (2 * r ^ 2))
    let dφ : Fin 4 → ℝ := ![pV, pu, 0, 0]
    sphereEinsteinSource H r e Λ pV pu (c.symm y)
      (sphericalChartDifferential c y a) (sphericalChartDifferential c y b) =
        ∑ i, ∑ j, (2 * dφ i * dφ j + 2 * maxwellStress g gInv F i j + Λ * g i j) * a i * b j := by
  dsimp only
  have he := (electric_stress (s := Real.sin y.1) (e := e) hH hr hs).1
  rw [sphereEinsteinSource_apply]
  change 2 * (pV * a 0 + pu * a 1) * (pV * b 0 + pu * b 1) +
    sphereSpacetimeMetric _ _ (c.symm y) _ _ = _
  simp only [sphericalChartDifferential]
  rw [spherical_chart_metric_pullback _ _ A c hc hy a b]
  simp_rw [he]
  norm_num [nullMetricMatrix, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail]
  field_simp
  ring

end CauchyHorizon
