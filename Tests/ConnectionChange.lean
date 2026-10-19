import CauchyHorizon.Reduced.CoordinateConnection
import CauchyHorizon.Geometry.SphericalChart

open CauchyHorizon MeasureTheory Set
open scoped Matrix Manifold ContDiff

-- A nonlinear coordinate change retains the inhomogeneous Hessian term and its factor.
example : connectionChange (fun _ _ _ : Fin 1 => 0) !![2] !![1 / 2] (fun _ => !![3]) 0 0 0 = 3 / 2 ∧
    metricChangeDerivative !![1] (fun _ : Fin 1 => 0) !![2] (fun _ => !![3]) 0 0 0 = 12 ∧
    christoffel !![1 / 4]
      (metricChangeDerivative !![1] (fun _ : Fin 1 => 0) !![2] (fun _ => !![3])) 0 0 0 = 3 / 2 := by
  norm_num [connectionChange, metricChangeDerivative, christoffel, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.of_apply]

example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi)
    {w : (ℝ × ℝ) × (ℝ × ℝ)} (hw : w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B))
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    IsMetricConnection (coordinateMetric hU hV x θ w)
      (fun k => coordinateMetricPartial hU hV x θ k w) Γ ↔
        Γ = coordinateChristoffel hU hV x θ w :=
  hx.coordinate_connection_unique hzin hA hB hθ hθA hw Γ

example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi)
    {w : (ℝ × ℝ) × (ℝ × ℝ)} (hw : w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B))
    {J K : Matrix (Fin 4) (Fin 4) ℝ} (hJK : J * K = 1) (hKJ : K * J = 1)
    {dJ : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ} (hdJ : ∀ i k j, dJ i k j = dJ j k i) :
    connectionChange (coordinateChristoffel hU hV x θ w) J K dJ =
      christoffel (K * coordinateMetricInverse hU hV x θ w * Kᵀ)
        (metricChangeDerivative (coordinateMetric hU hV x θ w)
          (fun k => coordinateMetricPartial hU hV x θ k w) J dJ) :=
  hx.coordinate_connection_change hzin hA hB hθ hθA hw hJK hKJ hdJ

-- Bounded frame coefficients preserve the actual L2 connection and its L1 quadratic products.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi)
    {J K : ((ℝ × ℝ) × (ℝ × ℝ)) → Matrix (Fin 4) (Fin 4) ℝ}
    {dJ : ((ℝ × ℝ) × (ℝ × ℝ)) → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ}
    (hJ : ∀ i j, MemLp (fun w => J w i j) ⊤ (rectangleProductMeasure U V A B))
    (hK : ∀ i j, MemLp (fun w => K w i j) ⊤ (rectangleProductMeasure U V A B))
    (hdJ : ∀ i k j, MemLp (fun w => dJ w i k j) 2 (rectangleProductMeasure U V A B)) :
    let Γ := fun w => connectionChange (coordinateChristoffel hU hV x θ w) (J w) (K w) (dJ w)
    (∀ k i j, MemLp (fun w => Γ w k i j) 2 (rectangleProductMeasure U V A B)) ∧
      ∀ k i j l m n, Integrable (fun w => Γ w k i j * Γ w l m n) (rectangleProductMeasure U V A B) := by
  have h := connectionChange_memLp (hx.coordinate_connection hzin A B θ hA hB hθ hθA).1 hJ hK hdJ
  exact ⟨h, fun k i j l m n => (h k i j).integrable_mul (h l m n)⟩

-- These derivatives belong to the actual overlap map and its actual inverse.
example (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω c c.source)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hd : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    {y : ℝ × ℝ} (hy : y ∈ (c.symm.trans d).source) :
    let t := c.symm.trans d
    (fderiv ℝ t.symm (t y)).comp (fderiv ℝ t y) = ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
      (fderiv ℝ t y).comp (fderiv ℝ t.symm (t y)) = ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
      IsSymmSndFDerivAt ℝ t y :=
  spherical_chart_transition_derivatives c d hc hci hd hdi hy
