import CauchyHorizon.Geometry.NullMetric
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The angular matrix is the pullback of the actual unit sphere's induced metric. -/

open Set
open scoped InnerProductSpace Manifold ContDiff

namespace CauchyHorizon

abbrev SphereAmbient := EuclideanSpace ℝ (Fin 3)
abbrev UnitSphere := Metric.sphere (0 : SphereAmbient) 1

noncomputable def sphericalPoint (y : ℝ × ℝ) : SphereAmbient :=
  WithLp.toLp 2 ![Real.sin y.1 * Real.cos y.2, Real.sin y.1 * Real.sin y.2, Real.cos y.1]

theorem sphericalPoint_mem (y : ℝ × ℝ) : sphericalPoint y ∈ UnitSphere := by
  have hi : ⟪sphericalPoint y, sphericalPoint y⟫_ℝ = 1 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_three]
    change (Real.sin y.1 * Real.cos y.2) * (Real.sin y.1 * Real.cos y.2) +
      (Real.sin y.1 * Real.sin y.2) * (Real.sin y.1 * Real.sin y.2) + Real.cos y.1 * Real.cos y.1 = 1
    linear_combination Real.sin y.1 ^ 2 * Real.sin_sq_add_cos_sq y.2 + Real.sin_sq_add_cos_sq y.1
  rw [mem_sphere_zero_iff_norm]
  rw [real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (sphericalPoint y)]

noncomputable def sphericalMap (y : ℝ × ℝ) : UnitSphere := ⟨sphericalPoint y, sphericalPoint_mem y⟩

theorem sphericalPoint_contDiff {n : ℕ∞ω} : ContDiff ℝ n sphericalPoint := by
  apply (contDiff_piLp 2).2
  intro i
  fin_cases i <;> norm_num [sphericalPoint, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail] <;> fun_prop

theorem sphericalMap_contMDiff {n : ℕ∞ω} : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) n sphericalMap := by
  let : Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact sphericalPoint_contDiff.contMDiff.codRestrict_sphere sphericalPoint_mem

noncomputable def sphericalDifferential (y : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] SphereAmbient :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (Real.cos y.1 * Real.cos y.2) • ContinuousLinearMap.fst ℝ ℝ ℝ -
        (Real.sin y.1 * Real.sin y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ,
      (Real.cos y.1 * Real.sin y.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (Real.sin y.1 * Real.cos y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ,
      (-Real.sin y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ])

theorem sphericalPoint_hasFDerivAt (y : ℝ × ℝ) :
    HasFDerivAt sphericalPoint (sphericalDifferential y) y := by
  have h₁ : HasFDerivAt (fun t : ℝ × ℝ => t.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) y :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have h₂ : HasFDerivAt (fun t : ℝ × ℝ => t.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) y :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hd : HasFDerivAt
      (fun t : ℝ × ℝ => ![Real.sin t.1 * Real.cos t.2, Real.sin t.1 * Real.sin t.2, Real.cos t.1])
      (ContinuousLinearMap.pi ![
        (Real.cos y.1 * Real.cos y.2) • ContinuousLinearMap.fst ℝ ℝ ℝ -
          (Real.sin y.1 * Real.sin y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ,
        (Real.cos y.1 * Real.sin y.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (Real.sin y.1 * Real.cos y.2) • ContinuousLinearMap.snd ℝ ℝ ℝ,
        (-Real.sin y.1) • ContinuousLinearMap.fst ℝ ℝ ℝ]) y := by
    apply hasFDerivAt_pi.2
    intro i
    fin_cases i
    · apply (h₁.sin.mul h₂.cos).congr_fderiv
      apply ContinuousLinearMap.ext
      intro a
      norm_num
      ring
    · apply (h₁.sin.mul h₂.sin).congr_fderiv
      apply ContinuousLinearMap.ext
      intro a
      norm_num
      ring
    · simpa using h₁.cos
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp y hd

theorem sphericalDifferential_inner (y a b : ℝ × ℝ) :
    ⟪sphericalDifferential y a, sphericalDifferential y b⟫_ℝ =
      a.1 * b.1 + Real.sin y.1 ^ 2 * a.2 * b.2 := by
  norm_num [PiLp.inner_apply, sphericalDifferential, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, RCLike.inner_apply]
  have hφ := Real.sin_sq_add_cos_sq y.2
  have hθ := Real.sin_sq_add_cos_sq y.1
  linear_combination (a.1 * b.1 * Real.cos y.1 ^ 2 + a.2 * b.2 * Real.sin y.1 ^ 2) * hφ +
    (a.1 * b.1) * hθ

theorem sphericalDifferential_tangent (y a : ℝ × ℝ) :
    ⟪sphericalPoint y, sphericalDifferential y a⟫_ℝ = 0 := by
  norm_num [PiLp.inner_apply, sphericalPoint, sphericalDifferential, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, RCLike.inner_apply]
  linear_combination (a.1 * Real.sin y.1 * Real.cos y.1) * Real.sin_sq_add_cos_sq y.2

noncomputable def unitSphereMetric (p : UnitSphere) (a b : TangentSpace (𝓡 2) p) : ℝ :=
  ⟪mvfderiv (𝓡 2) (fun p : UnitSphere => (p : SphereAmbient)) p a,
    mvfderiv (𝓡 2) (fun p : UnitSphere => (p : SphereAmbient)) p b⟫_ℝ

theorem unitSphereMetric_pullback_of_hasFDerivAt {f : ℝ × ℝ → UnitSphere} {y : ℝ × ℝ}
    {D : (ℝ × ℝ) →L[ℝ] SphereAmbient}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f y)
    (hD : HasFDerivAt (fun t => (f t : SphereAmbient)) D y) (a b : ℝ × ℝ) :
    unitSphereMetric (f y) (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f y a)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f y b) = ⟪D a, D b⟫_ℝ := by
  let : Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hco : MDifferentiableAt (𝓡 2) 𝓘(ℝ, SphereAmbient)
      (fun p : UnitSphere => (p : SphereAmbient)) (f y) :=
    (contMDiff_coe_sphere (m := ∞) (f y)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp y hco hf
  have he : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, SphereAmbient)
      ((fun p : UnitSphere => (p : SphereAmbient)) ∘ f) y = D := hD.hasMFDerivAt.mfderiv
  rw [he] at hc
  have hd (v : ℝ × ℝ) :
      mvfderiv (𝓡 2) (fun p : UnitSphere => (p : SphereAmbient)) (f y)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f y v) = D v :=
    congrArg (fun L : (ℝ × ℝ) →L[ℝ] SphereAmbient => L v) hc.symm
  simp only [unitSphereMetric, hd]

theorem unitSphereMetric_pullback (y a b : ℝ × ℝ) :
    unitSphereMetric (sphericalMap y)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) sphericalMap y a)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) sphericalMap y b) =
        a.1 * b.1 + Real.sin y.1 ^ 2 * a.2 * b.2 := by
  rw [unitSphereMetric_pullback_of_hasFDerivAt
    ((sphericalMap_contMDiff (n := ∞) y).mdifferentiableAt (by simp)) (sphericalPoint_hasFDerivAt y)]
  exact sphericalDifferential_inner y a b

theorem sphericalDifferential_injective {y : ℝ × ℝ} (hy : Real.sin y.1 ≠ 0) :
    Function.Injective (sphericalDifferential y) := by
  intro a b hab
  have ha : sphericalDifferential y (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hh := sphericalDifferential_inner y (a - b) (a - b)
  rw [ha, inner_zero_left] at hh
  change 0 = (a.1 - b.1) * (a.1 - b.1) + Real.sin y.1 ^ 2 * (a.2 - b.2) * (a.2 - b.2) at hh
  have hs : 0 < Real.sin y.1 ^ 2 := sq_pos_of_ne_zero hy
  have h₁ : a.1 = b.1 := by nlinarith [sq_nonneg (a.1 - b.1), mul_nonneg hs.le (sq_nonneg (a.2 - b.2))]
  have h₂ : a.2 = b.2 := by
    rw [h₁, sub_self, zero_mul, zero_add] at hh
    have he : Real.sin y.1 ^ 2 * (a.2 - b.2) ^ 2 = 0 := by nlinarith only [hh]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hs.ne'))
  exact Prod.ext h₁ h₂

theorem sphericalPoint_cover (p : UnitSphere) (y : ℝ × ℝ) :
    ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient,
      A (sphericalPoint y) = (p : SphereAmbient) := by
  have hp : ‖(p : SphereAmbient)‖ = 1 := mem_sphere_zero_iff_norm.1 p.property
  have hq : ‖sphericalPoint y‖ = 1 :=
    mem_sphere_zero_iff_norm.1 (sphericalPoint_mem _)
  exact ⟨Submodule.reflection (ℝ ∙ (sphericalPoint y - (p : SphereAmbient)))ᗮ,
    Submodule.reflection_sub (hq.trans hp.symm)⟩

noncomputable def ambientNullMetric (H R : ℝ) (a b : (ℝ × ℝ) × SphereAmbient) : ℝ :=
  -(H / 2) * (a.1.1 * b.1.2 + a.1.2 * b.1.1) + R * ⟪a.2, b.2⟫_ℝ

noncomputable def sphericalTangentLift (y : ℝ × ℝ) (a : Fin 4 → ℝ) : (ℝ × ℝ) × SphereAmbient :=
  ((a 0, a 1), sphericalDifferential y (a 2, a 3))

theorem spherical_metric_pullback (H R : ℝ) (y : ℝ × ℝ) (a b : Fin 4 → ℝ)
    (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) :
    ambientNullMetric H R ((a 0, a 1), A (sphericalDifferential y (a 2, a 3)))
      ((b 0, b 1), A (sphericalDifferential y (b 2, b 3))) =
      ∑ i, ∑ j, nullMetricMatrix H R (Real.sin y.1 ^ 2) i j * a i * b j := by
  rw [ambientNullMetric, A.inner_map_map, sphericalDifferential_inner]
  norm_num [nullMetricMatrix, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail]
  ring

noncomputable def rotatedSphericalMap (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (y : ℝ × ℝ) : UnitSphere :=
  ⟨A (sphericalPoint y), by
    rw [mem_sphere_zero_iff_norm, A.norm_map]
    exact mem_sphere_zero_iff_norm.1 (sphericalPoint_mem y)⟩

theorem rotatedSphericalMap_contMDiff {n : ℕ∞ω} (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) n (rotatedSphericalMap A) := by
  let : Fact (Module.finrank ℝ SphereAmbient = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (A.contDiff.comp sphericalPoint_contDiff).contMDiff.codRestrict_sphere
    (fun y => (rotatedSphericalMap A y).property)

theorem unitSphereMetric_rotated_pullback (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (y a b : ℝ × ℝ) :
    unitSphereMetric (rotatedSphericalMap A y)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (rotatedSphericalMap A) y a)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (rotatedSphericalMap A) y b) =
        a.1 * b.1 + Real.sin y.1 ^ 2 * a.2 * b.2 := by
  have hD : HasFDerivAt (fun t => (rotatedSphericalMap A t : SphereAmbient))
      (A.toContinuousLinearEquiv.toContinuousLinearMap.comp (sphericalDifferential y)) y :=
    A.toContinuousLinearEquiv.hasFDerivAt.comp y (sphericalPoint_hasFDerivAt y)
  rw [unitSphereMetric_pullback_of_hasFDerivAt
    ((rotatedSphericalMap_contMDiff (n := ∞) A y).mdifferentiableAt (by simp)) hD]
  change ⟪A (sphericalDifferential y a), A (sphericalDifferential y b)⟫_ℝ = _
  rw [A.inner_map_map, sphericalDifferential_inner]

theorem rotatedSphericalMap_regular_cover (p : UnitSphere) (φ : ℝ) :
    ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient,
      rotatedSphericalMap A (Real.pi / 2, φ) = p ∧
      Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (rotatedSphericalMap A) (Real.pi / 2, φ)) := by
  obtain ⟨A, hA⟩ := sphericalPoint_cover p (Real.pi / 2, φ)
  refine ⟨A, Subtype.ext hA, ?_⟩
  let D := mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (rotatedSphericalMap A) (Real.pi / 2, φ)
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, ℝ × ℝ) (Real.pi / 2, φ)) := by
    change FiniteDimensional ℝ (ℝ × ℝ)
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) (rotatedSphericalMap A (Real.pi / 2, φ))) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 2))
    infer_instance
  have hinj : Function.Injective D := by
    intro a b hab
    have hh := unitSphereMetric_rotated_pullback A (Real.pi / 2, φ) (a - b) (a - b)
    have hzero : D (a - b) = 0 := by rw [map_sub, hab, sub_self]
    change unitSphereMetric _ (D (a - b)) (D (a - b)) = _ at hh
    rw [hzero] at hh
    simp only [unitSphereMetric, map_zero, inner_zero_left, Real.sin_pi_div_two, one_pow, one_mul] at hh
    change 0 = (a.1 - b.1) * (a.1 - b.1) + (a.2 - b.2) * (a.2 - b.2) at hh
    exact Prod.ext (by nlinarith [sq_nonneg (a.2 - b.2)]) (by nlinarith [sq_nonneg (a.1 - b.1)])
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  change Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))
  simp

noncomputable def sphereSpacetimeMetric (H R : ℝ) (p : UnitSphere)
    (a b : (ℝ × ℝ) × TangentSpace (𝓡 2) p) : ℝ :=
  -(H / 2) * (a.1.1 * b.1.2 + a.1.2 * b.1.1) + R * unitSphereMetric p a.2 b.2

noncomputable def sphericalSpacetimeDifferential (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (y : ℝ × ℝ) (a : Fin 4 → ℝ) : (ℝ × ℝ) × TangentSpace (𝓡 2) (rotatedSphericalMap A y) :=
  ((a 0, a 1), mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (rotatedSphericalMap A) y (a 2, a 3))

theorem sphereSpacetimeMetric_pullback (H R : ℝ) (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (y : ℝ × ℝ) (a b : Fin 4 → ℝ) :
    sphereSpacetimeMetric H R (rotatedSphericalMap A y)
      (sphericalSpacetimeDifferential A y a) (sphericalSpacetimeDifferential A y b) =
        ∑ i, ∑ j, nullMetricMatrix H R (Real.sin y.1 ^ 2) i j * a i * b j := by
  simp only [sphereSpacetimeMetric, sphericalSpacetimeDifferential, unitSphereMetric_rotated_pullback]
  norm_num [nullMetricMatrix, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail]
  ring

end CauchyHorizon
