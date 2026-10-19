import CauchyHorizon.Reduced.ScalarDivergence

open CauchyHorizon MeasureTheory Set
open scoped Distributions

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
  (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)

-- The current is formed from the actual volume density, inverse metric and scalar gradient.
example {A B θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi)
    (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)) :
    (fun i => Real.sqrt |(coordinateMetric hU hV x θ w).det| *
      ∑ j, coordinateMetricInverse hU hV x θ w i j * coordinateScalarGradient hU hV x w j) =
      ![scalarNullFlux hU hV x 0 w.1 * -Real.sin (θ + w.2.1),
        scalarNullFlux hU hV x 1 w.1 * -Real.sin (θ + w.2.1), 0, 0] := by
  rw [((hx.coordinate_maxwell hzin A B θ hA hB hθ hθA).2.1 w hw).2]
  exact coordinateScalarFlux_eq hU hV x θ w

-- The two mixed radial derivatives are opposite L1 densities, including across V = 0.
example {A B : ℝ} (b : ℝ × ℝ → ℝ) (hb : IntegrableOn b (Icc 0 A ×ˢ Icc 0 B)) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((1, 0), (0, 0))
      (rectangleProductDistribution U V A B (fun w => scalarNullFlux hU hV x 0 w.1 * b w.2)) =
        rectangleProductDistribution U V A B (fun w => scalarNullSource hU hV x w.1 * b w.2) ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 1), (0, 0))
      (rectangleProductDistribution U V A B (fun w => scalarNullFlux hU hV x 1 w.1 * b w.2)) =
        rectangleProductDistribution U V A B (fun w => -scalarNullSource hU hV x w.1 * b w.2) :=
  (hx.scalar_flux_derivatives hzin).2.2 A B b hb

example {A B θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    (∀ i, MemLp (fun w => coordinateScalarFlux hU hV x θ w i) 2 (rectangleProductMeasure U V A B)) ∧
    (∑ i, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate i)
      (rectangleProductDistribution U V A B (fun w => coordinateScalarFlux hU hV x θ w i))) = 0 :=
  hx.coordinate_scalar_equation hzin A B θ hA hB hθ hθA

-- No extra PDE premise is needed for the scalar or Maxwell equation.
example (hnull : HasNullRicciSources hU hV x) :
    HasCoordinateMaxwell hU hV e x ∧ HasCoordinateEinsteinEquation hU hV e Λ x ∧
      HasCoordinateScalarEquation hU hV x :=
  ⟨hx.coordinate_maxwell hzin, hx.coordinate_einstein_equation hzin hnull,
    hx.coordinate_scalar_equation hzin⟩
