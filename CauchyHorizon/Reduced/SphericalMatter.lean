import CauchyHorizon.Geometry.SphericalMatter
import CauchyHorizon.Reduced.SphericalEinstein
import CauchyHorizon.Reduced.ScalarDivergence

/-! Intrinsic matter fields and their weak equations in the actual spherical charts. -/

open Set Filter MeasureTheory
open scoped Manifold ContDiff Distributions

namespace CauchyHorizon

noncomputable def sphericalScalar {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (v : ℝ × ℝ) (_p : UnitSphere) : ℝ :=
  x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2) 1

noncomputable def sphericalScalarCovector {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (v : ℝ × ℝ) (p : UnitSphere) :
    ((ℝ × ℝ) × TangentSpace (𝓡 2) p) →ₗ[ℝ] ℝ :=
  sphereNullCovector (x.2.2 v.1 (projIcc 0 V hV v.2) 1)
    (x.2.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2) 1) p

noncomputable def sphericalMaxwell {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e : ℝ) (x : WaveState U V) (v : ℝ × ℝ) (p : UnitSphere) :
    AlternatingMap ℝ ((ℝ × ℝ) × TangentSpace (𝓡 2) p) ℝ (Fin 2) :=
  let z := x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2)
  sphereElectricForm (e * Real.exp (z 2) / (2 * z 0 ^ 2)) p

noncomputable def chartScalar {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  sphericalScalar hU hV x w.1 (c.symm (θ + w.2.1, φ + w.2.2))

noncomputable def chartScalarGradient {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (θ φ : ℝ)
    (w : (ℝ × ℝ) × (ℝ × ℝ)) (i : Fin 4) : ℝ :=
  sphericalScalarCovector hU hV x w.1 (c.symm (θ + w.2.1, φ + w.2.2))
    (sphericalChartDifferential c (θ + w.2.1, φ + w.2.2) (Pi.single i 1))

noncomputable def chartMaxwell {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e : ℝ) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (θ φ : ℝ)
    (w : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => sphericalMaxwell hU hV e x w.1 (c.symm (θ + w.2.1, φ + w.2.2))
    ![sphericalChartDifferential c (θ + w.2.1, φ + w.2.2) (Pi.single i 1),
      sphericalChartDifferential c (θ + w.2.1, φ + w.2.2) (Pi.single j 1)]

noncomputable def chartMaxwellFlux {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e : ℝ) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (θ φ : ℝ)
    (w : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  coordinateVolumeDensity hU hV x θ w •
    raiseTwoForm (coordinateMetricInverse hU hV x θ w) (chartMaxwell hU hV e x c θ φ w)

noncomputable def chartScalarFlux {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (θ φ : ℝ)
    (w : (ℝ × ℝ) × (ℝ × ℝ)) (i : Fin 4) : ℝ :=
  coordinateVolumeDensity hU hV x θ w *
    ∑ j, coordinateMetricInverse hU hV x θ w i j * chartScalarGradient hU hV x c θ φ w j

theorem chartScalarGradient_eq {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    chartScalarGradient hU hV x c θ φ w = coordinateScalarGradient hU hV x w := by
  funext i
  fin_cases i <;> norm_num [chartScalarGradient, sphericalScalarCovector, sphereNullCovector_apply,
    sphericalChartDifferential, coordinateScalarGradient, Pi.single_apply,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem chartMaxwell_eq {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e : ℝ) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    chartMaxwell hU hV e x c θ φ w = coordinateMaxwell hU hV e x w := by
  ext i j
  have h := sphereElectricForm_chart_pullback
    (e * Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2) /
      (2 * x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2))
    c (θ + w.2.1, φ + w.2.2) (Pi.single i 1) (Pi.single j 1)
  simpa [chartMaxwell, sphericalMaxwell, coordinateMaxwell, Pi.single_apply] using h

theorem chartMatterFlux_eq {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e : ℝ) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    chartMaxwellFlux hU hV e x c θ φ w = coordinateMaxwellFlux hU hV e x θ w ∧
      chartScalarFlux hU hV x c θ φ w = coordinateScalarFlux hU hV x θ w := by
  constructor
  · simp only [chartMaxwellFlux, chartMaxwell_eq, coordinateMaxwellFlux]
  · funext i
    simp only [chartScalarFlux, chartScalarGradient_eq, coordinateScalarFlux]

theorem sphericalMatter_transition {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e : ℝ) (x : WaveState U V)
    (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (v y : ℝ × ℝ) (a b : Fin 4 → ℝ) :
    let t := c.symm.trans d
    let T := angularVectorChange (fderiv ℝ t y)
    sphericalScalar hU hV x v (d.symm (t y)) = sphericalScalar hU hV x v (c.symm y) ∧
    sphericalScalarCovector hU hV x v (d.symm (t y)) (sphericalChartDifferential d (t y) (T a)) =
      sphericalScalarCovector hU hV x v (c.symm y) (sphericalChartDifferential c y a) ∧
    sphericalMaxwell hU hV e x v (d.symm (t y))
      ![sphericalChartDifferential d (t y) (T a), sphericalChartDifferential d (t y) (T b)] =
      sphericalMaxwell hU hV e x v (c.symm y)
        ![sphericalChartDifferential c y a, sphericalChartDifferential c y b] := ⟨rfl, rfl, rfl⟩

theorem chartEinsteinSource_matter {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ))
    (hr : x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ≠ 0)
    (hs : Real.sin (θ + w.2.1) ≠ 0) (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hw : (θ + w.2.1, φ + w.2.2) ∈ c.target) (i j : Fin 4) :
    chartEinsteinSource hU hV e Λ x c θ φ w i j =
      2 * chartScalarGradient hU hV x c θ φ w i * chartScalarGradient hU hV x c θ φ w j +
      2 * maxwellStress (coordinateMetric hU hV x θ w) (coordinateMetricInverse hU hV x θ w)
        (chartMaxwell hU hV e x c θ φ w) i j + Λ * coordinateMetric hU hV x θ w i j := by
  rw [coordinateEinsteinSource_spherical_chart hU hV e Λ x θ φ w hr hs A c hc hw i j,
    chartScalarGradient_eq, chartMaxwell_eq]
  rfl

def HasChartMatter {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e : ℝ) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (A B θ φ : ℝ) : Prop :=
  HasL2ProductDerivatives U V A B (chartScalar hU hV x c θ φ)
    (fun i w => chartScalarGradient hU hV x c θ φ w i) ∧
  (∀ i j, Continuous (fun w => chartMaxwell hU hV e x c θ φ w i j) ∧
    MemLp (fun w => chartMaxwell hU hV e x c θ φ w i j) 2 (rectangleProductMeasure U V A B) ∧
    MemLp (fun w => chartMaxwellFlux hU hV e x c θ φ w i j) 2 (rectangleProductMeasure U V A B)) ∧
  (∀ w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B),
    0 < coordinateVolumeDensity hU hV x θ w ∧
    Real.sqrt |(coordinateMetric hU hV x θ w).det| = coordinateVolumeDensity hU hV x θ w) ∧
  (∀ i j k, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate i)
      (rectangleProductDistribution U V A B (fun w => chartMaxwell hU hV e x c θ φ w j k)) +
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate j)
      (rectangleProductDistribution U V A B (fun w => chartMaxwell hU hV e x c θ φ w k i)) +
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate k)
      (rectangleProductDistribution U V A B (fun w => chartMaxwell hU hV e x c θ φ w i j)) = 0) ∧
  (∀ j, (∑ i, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate i)
    (rectangleProductDistribution U V A B (fun w => chartMaxwellFlux hU hV e x c θ φ w i j))) = 0) ∧
  (∀ i, MemLp (fun w => chartScalarFlux hU hV x c θ φ w i) 2 (rectangleProductMeasure U V A B)) ∧
  (∑ i, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate i)
    (rectangleProductDistribution U V A B (fun w => chartScalarFlux hU hV x c θ φ w i))) = 0

theorem spherical_matter_in_chart {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V} {x : WaveState U V}
    (hE : HasCoordinateEinsteinEquation hU hV e Λ x) (hM : HasCoordinateMaxwell hU hV e x)
    (hS : HasCoordinateScalarEquation hU hV x)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (A B θ φ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    HasChartMatter hU hV e x c A B θ φ := by
  have he := hE A B θ hA hB hθ hθA
  have hm := hM A B θ hA hB hθ hθA
  have hs := hS A B θ hA hB hθ hθA
  have hF : chartMaxwellFlux hU hV e x c θ φ = coordinateMaxwellFlux hU hV e x θ :=
    funext fun w => (chartMatterFlux_eq hU hV e x c θ φ w).1
  have hJ : chartScalarFlux hU hV x c θ φ = coordinateScalarFlux hU hV x θ :=
    funext fun w => (chartMatterFlux_eq hU hV e x c θ φ w).2
  simp only [HasChartMatter, chartScalarGradient_eq, chartMaxwell_eq, hF, hJ]
  exact ⟨he.1, hm.1, hm.2.1, hm.2.2.2.1, hm.2.2.2.2, hs⟩

def IsSphericalSolutionChart {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (p : UnitSphere) (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (δ : ℝ) : Prop :=
  0 < δ ∧ δ < Real.pi / 2 ∧ p ∈ c.source ∧ c p = (Real.pi / 2, Real.pi / 2) ∧
    EqOn c.symm (rotatedSphericalMap A) c.target ∧
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω c c.source ∧
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target ∧
    (∀ s ∈ Icc 0 (2 * δ), ∀ t ∈ Icc 0 (2 * δ),
      (Real.pi / 2 - δ + s, Real.pi / 2 - δ + t) ∈ c.target) ∧
    (∀ i j, Integrable (fun w => chartEinsteinSource hU hV e Λ x c
        (Real.pi / 2 - δ) (Real.pi / 2 - δ) w i j) (rectangleProductMeasure U V (2 * δ) (2 * δ)) ∧
      ricciDistribution U V (2 * δ) (2 * δ)
        (coordinateChristoffel hU hV x (Real.pi / 2 - δ)) i j =
          rectangleProductDistribution U V (2 * δ) (2 * δ) (fun w =>
            chartEinsteinSource hU hV e Λ x c (Real.pi / 2 - δ) (Real.pi / 2 - δ) w i j)) ∧
    HasChartMatter hU hV e x c (2 * δ) (2 * δ) (Real.pi / 2 - δ) (Real.pi / 2 - δ)

def HasSphericalFieldEquations {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) : Prop :=
  ∀ p : UnitSphere, ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient,
    ∃ c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ), ∃ δ : ℝ,
      IsSphericalSolutionChart hU hV e Λ x p A c δ

theorem HasSphericalRicci.spherical_field_equations {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {x : WaveState U V} (hR : HasSphericalRicci hU hV e Λ x)
    (hE : HasCoordinateEinsteinEquation hU hV e Λ x) (hM : HasCoordinateMaxwell hU hV e x)
    (hS : HasCoordinateScalarEquation hU hV x) : HasSphericalFieldEquations hU hV e Λ x := by
  intro p
  obtain ⟨A, c, δ, hδ, hδπ, hp, hcenter, hparam, hc, hci, hbox, hsource⟩ := hR p
  refine ⟨A, c, δ, hδ, hδπ, hp, hcenter, hparam, hc, hci, hbox, hsource, ?_⟩
  exact spherical_matter_in_chart hE hM hS c _ _ _ _ (by positivity) (by positivity)
    (sub_pos.2 hδπ) (by linarith)

end CauchyHorizon
