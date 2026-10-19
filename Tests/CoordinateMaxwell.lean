import CauchyHorizon.Reduced.EinsteinEquation

open MeasureTheory Set
open scoped Distributions

namespace CauchyHorizon.Tests

-- The solver order (V,u) reverses the component sign of du wedge dV.
example (H r e : ℝ) : electricTwoForm (e * H / (2 * r ^ 2)) 0 1 = -e * H / (2 * r ^ 2) ∧
    electricTwoForm (e * H / (2 * r ^ 2)) 1 0 = e * H / (2 * r ^ 2) := by
  constructor
  · dsimp [electricTwoForm]
    ring
  · rfl

-- A nonunit lapse, radius and angular factor check the determinant normalization.
example : Real.sqrt |(nullMetricMatrix 3 (2 ^ 2) ((3 / 5) ^ 2)).det| = 18 / 5 := by
  have hh := (null_metric_volume (H := 3) (r := 2) (s := 3 / 5)
    (by norm_num) (by norm_num) (by norm_num)).2
  norm_num at hh ⊢
  exact hh

-- Raising and multiplying by the actual volume density removes H and r exactly.
example {H r s e : ℝ} (hH : H ≠ 0) (hr : r ≠ 0) :
    ((H * r ^ 2 * s / 2) •
      raiseTwoForm (nullMetricInverse H (r ^ 2) (s ^ 2)) (electricTwoForm (e * H / (2 * r ^ 2)))) 0 1 = e * s ∧
    ((H * r ^ 2 * s / 2) •
      raiseTwoForm (nullMetricInverse H (r ^ 2) (s ^ 2)) (electricTwoForm (e * H / (2 * r ^ 2)))) 1 0 = -e * s := by
  rw [electric_density hH hr]
  simp [electricTwoForm]

-- The factor two in the Einstein source and the trace-free Maxwell stress are retained.
example {H r s e : ℝ} (hH : H ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    let g := nullMetricMatrix H (r ^ 2) (s ^ 2)
    let gInv := nullMetricInverse H (r ^ 2) (s ^ 2)
    let F := electricTwoForm (e * H / (2 * r ^ 2))
    2 * maxwellStress g gInv F 0 1 = H * e ^ 2 / (2 * r ^ 4) ∧
    2 * maxwellStress g gInv F 2 2 = e ^ 2 / r ^ 2 ∧
    2 * maxwellStress g gInv F 3 3 = e ^ 2 * s ^ 2 / r ^ 2 ∧
    (∑ i, ∑ j, gInv i j * maxwellStress g gInv F i j) = 0 := by
  have hh := electric_stress (e := e) hH hr hs
  exact ⟨hh.1 0 1, hh.1 2 2, hh.1 3 3, hh.2⟩

-- The actual electric field satisfies all closedness and divergence equations.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasCoordinateMaxwell hU hV e x := hx.coordinate_maxwell hzin

-- The unified source uses the actual Maxwell stress, not an assumed charge density.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hn : HasNullRicciSources hU hV x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hθ : 0 < θ) (hθA : θ + A < Real.pi) (i j : Fin 4) :
    ricciDistribution U V A B (coordinateChristoffel hU hV x θ) i j =
      rectangleProductDistribution U V A B (fun w =>
        2 * coordinateScalarGradient hU hV x w i * coordinateScalarGradient hU hV x w j +
        2 * coordinateMaxwellStress hU hV e x θ w i j + Λ * coordinateMetric hU hV x θ w i j) :=
  ((hx.coordinate_einstein_equation hzin hn A B θ hA hB hθ hθA).2.1 i j).2

end CauchyHorizon.Tests
