import CauchyHorizon.Reduced.CoordinateConnection
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open MeasureTheory Set
open scoped Distributions

namespace CauchyHorizon.Tests

-- The four-dimensional measure is the ordinary coordinate Lebesgue measure.
example (U V A B : ℝ) : rectangleProductMeasure U V A B =
    volume.restrict ((Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)) := by
  simp only [rectangleProductMeasure, Measure.volume_eq_prod, Measure.prod_restrict]

-- Four-dimensional tests may be nonzero at any interior point of the horizon.
example {U V A B : ℝ} {w : (ℝ × ℝ) × (ℝ × ℝ)}
    (hw : w ∈ openRectangleProduct U V A B) :
    ∃ ψ : 𝓓(openRectangleProduct U V A B, ℝ), ψ w = 1 := by
  obtain ⟨f, hs, hc, hd, _hrange, hf⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((openRectangleProduct U V A B).isOpen.mem_nhds hw)
  exact ⟨⟨f, hd, hc, hs⟩, hf⟩

-- The line element -H du dv has off-diagonal coefficient -H/2 and inverse -2/H.
example {H R S : ℝ} (hH : 0 < H) (hR : 0 < R) (hS : 0 < S) :
    nullMetricMatrix H R S 0 1 = -H / 2 ∧
      nullMetricInverse H R S 0 1 = -2 / H ∧
      nullMetricMatrix H R S * nullMetricInverse H R S = 1 := by
  refine ⟨?_, rfl, (nullMetric_geometry hH hR hS).2.2.2.2.1⟩
  simp [nullMetricMatrix]
  ring

-- The angular weak derivative includes the sphere's sin-cos factor in four dimensions.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 0), (1, 0))
      (rectangleProductDistribution U V A B (fun w => coordinateMetric hU hV x θ w 3 3)) =
      rectangleProductDistribution U V A B (fun w =>
        (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0) ^ 2 *
          (2 * Real.sin (θ + w.2.1) * Real.cos (θ + w.2.1))) := by
  have hh := (((hx.coordinate_metric hzin A B θ hA hB hθ hθA).2.2.1 3 3).2 2).2
  simpa [productCoordinate, coordinateMetricPartial, Matrix.diagonal] using hh

-- The rough null derivative of the off-diagonal metric coefficient keeps its sign and factor.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    MemLp (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2) *
        x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 2 * (-1 / 2)) 2
      (rectangleProductMeasure U V A B) := by
  exact (((hx.coordinate_metric hzin A B θ hA hB hθ hθA).2.2.1 0 1).2 0).1

-- The null self-connection is the actual rough log-lapse derivative, with no factor two.
example {U V θ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    coordinateChristoffel hU hV x θ w 0 0 0 = x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 2 := by
  simp [coordinateChristoffel, christoffel, coordinateMetricInverse, coordinateMetricPartial,
    nullMetricInverse, nullMetricMatrix, Fin.sum_univ_succ, Matrix.diagonal]
  field_simp
  ring

-- Pure angular connection coefficients remain present even when the null derivatives vanish.
example {U V θ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (w : (ℝ × ℝ) × (ℝ × ℝ))
    (hr : x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ≠ 0) :
    coordinateChristoffel hU hV x θ w 2 3 3 = -Real.sin (θ + w.2.1) * Real.cos (θ + w.2.1) := by
  simp [coordinateChristoffel, christoffel, coordinateMetricInverse, coordinateMetricPartial,
    nullMetricInverse, nullMetricMatrix, Fin.sum_univ_succ, Matrix.diagonal]
  field_simp

example {U V θ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (w : (ℝ × ℝ) × (ℝ × ℝ))
    (hr : x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ≠ 0)
    (hs : Real.sin (θ + w.2.1) ≠ 0) :
    coordinateChristoffel hU hV x θ w 3 2 3 = Real.cos (θ + w.2.1) / Real.sin (θ + w.2.1) := by
  simp [coordinateChristoffel, christoffel, coordinateMetricInverse, coordinateMetricPartial,
    nullMetricInverse, nullMetricMatrix, Fin.sum_univ_succ, Matrix.diagonal]
  field_simp

-- All actual coefficients are L2 on the same angular box.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) (k i j : Fin 4) :
    MemLp (fun w => coordinateChristoffel hU hV x θ w k i j) 2
      (rectangleProductMeasure U V A B) :=
  (hx.coordinate_connection hzin A B θ hA hB hθ hθA).1 k i j

-- The quadratic curvature terms are genuine L1 functions on that same box.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi)
    (k i j l m n : Fin 4) :
    Integrable (fun w => coordinateChristoffel hU hV x θ w k i j *
      coordinateChristoffel hU hV x θ w l m n) (rectangleProductMeasure U V A B) :=
  (hx.coordinate_connection hzin A B θ hA hB hθ hθA).2.1 k i j l m n

end CauchyHorizon.Tests
