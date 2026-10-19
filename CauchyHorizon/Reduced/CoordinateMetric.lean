import CauchyHorizon.Reduced.MetricCoefficients
import CauchyHorizon.Analysis.ProductWeakDerivative
import CauchyHorizon.Geometry.NullMetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The actual spherical coordinate metric is continuous and has four L2 weak derivatives. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

noncomputable def coordinateMetric {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  nullMetricMatrix (Real.exp (z 2)) (z 0 ^ 2) (Real.sin (θ + w.2.1) ^ 2)

noncomputable def coordinateMetricInverse {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  nullMetricInverse (Real.exp (z 2)) (z 0 ^ 2) (Real.sin (θ + w.2.1) ^ 2)

noncomputable def coordinateMetricPartial {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ : ℝ) (k : Fin 4) (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  let p := x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  let q := x.2.2 w.1.1 (projIcc 0 V hV w.1.2)
  ![nullMetricMatrix (Real.exp (z 2) * q 2) (2 * z 0 * q 0) (Real.sin (θ + w.2.1) ^ 2),
    nullMetricMatrix (Real.exp (z 2) * p 2) (2 * z 0 * p 0) (Real.sin (θ + w.2.1) ^ 2),
    Matrix.diagonal ![0, 0, 0, z 0 ^ 2 * (2 * Real.sin (θ + w.2.1) * Real.cos (θ + w.2.1))],
    0] k

def HasL2CoordinateMetric {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi →
    (∀ i j, Continuous (fun w => coordinateMetric hU hV x θ w i j)) ∧
    (∀ i j, ContinuousOn (fun w => coordinateMetricInverse hU hV x θ w i j)
      ((Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B))) ∧
    (∀ i j, HasL2ProductDerivatives U V A B (fun w => coordinateMetric hU hV x θ w i j)
      (fun k w => coordinateMetricPartial hU hV x θ k w i j)) ∧
    ∀ w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B),
      let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
      HasNullMetricGeometry (Real.exp (z 2)) (z 0 ^ 2) (Real.sin (θ + w.2.1) ^ 2)

set_option maxHeartbeats 1500000 in
theorem IsWaveIntegral.coordinate_metric {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasL2CoordinateMetric hU hV x := by
  intro A B θ hA hB hθ hθA
  let μ := volume.restrict (Icc 0 A ×ˢ Icc 0 B)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hLp {f : ℝ × ℝ → ℝ} (hc : Continuous f) : MemLp f 2 μ := by
    let F : C(Icc 0 A × Icc 0 B, ℝ) := ⟨fun w => f (w.1, w.2), by fun_prop⟩
    apply MemLp.of_bound hc.aestronglyMeasurable ‖F‖
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with w hw
    exact F.norm_coe_le_norm (⟨w.1, hw.1⟩, ⟨w.2, hw.2⟩)
  have hconst (d : ℝ) : HasL2FirstDerivatives A B (fun _ => d) (fun _ => 0) (fun _ => 0) := by
    refine l2_first_derivatives_of_sections hA hB (hLp continuous_const)
      (hLp continuous_const) (hLp continuous_const) ?_ ?_ ?_ ?_
    · intro v
      exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => d)).contDiffOn.absolutelyContinuousOnInterval
    · intro v
      exact Eventually.of_forall fun u => hasDerivWithinAt_const u _ d
    · intro u
      exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => d)).contDiffOn.absolutelyContinuousOnInterval
    · intro u
      exact Eventually.of_forall fun v => hasDerivWithinAt_const v _ d
  have hsin : HasL2FirstDerivatives A B (fun w => Real.sin (θ + w.1) ^ 2)
      (fun w => 2 * Real.sin (θ + w.1) * Real.cos (θ + w.1)) (fun _ => 0) := by
    refine l2_first_derivatives_of_sections hA hB (hLp (by fun_prop))
      (hLp (by fun_prop)) (hLp continuous_const) ?_ ?_ ?_ ?_
    · intro v
      exact (show ContDiff ℝ 1 (fun u : ℝ => Real.sin (θ + u) ^ 2) by
        fun_prop).contDiffOn.absolutelyContinuousOnInterval
    · intro v
      apply Eventually.of_forall
      intro u
      convert (((hasDerivAt_id u).const_add θ).sin.pow 2).hasDerivWithinAt (s := Icc 0 A) using 1 <;>
        first | rfl | (ring_nf; rfl)
    · intro u
      exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => Real.sin (θ + u) ^ 2)).contDiffOn.absolutelyContinuousOnInterval
    · intro u
      exact Eventually.of_forall fun v => hasDerivWithinAt_const v (Icc 0 B) (Real.sin (θ + u) ^ 2)
  have hm := hx.metric_coefficients hzin
  have hH := l2_product_derivatives hm.2.2.2.1 (hconst (-1 / 2))
  have hR := l2_product_derivatives hm.2.2.2.2 (hconst 1)
  have hS := l2_product_derivatives hm.2.2.2.2 hsin
  have hzero := l2_product_derivatives hm.2.2.2.1 (hconst 0)
  have hr (w : (ℝ × ℝ) × (ℝ × ℝ)) :
      x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ≠ 0 := hx.choose _ _
  have hs (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)) :
      0 < Real.sin (θ + w.2.1) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hw.2.1.1]) (by linarith [hw.2.1.2])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    have hcH : Continuous (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2) * (-1 / 2)) := by
      fun_prop
    have hcR : Continuous (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2) := by fun_prop
    have hcS : Continuous (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2 * Real.sin (θ + w.2.1) ^ 2) := by
      fun_prop
    fin_cases i <;> fin_cases j <;> first
      | exact hcH
      | exact hcR
      | exact hcS
      | exact continuous_const (y := (0 : ℝ))
  · intro i j
    have hiH : ContinuousOn (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        -2 / Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2))
        ((Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)) :=
      continuousOn_const.div (by fun_prop) (fun _ _ => Real.exp_ne_zero _)
    have hiR : ContinuousOn (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2)⁻¹)
        ((Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)) :=
      (show ContinuousOn (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2) _ by fun_prop).inv₀
          (fun w _ => pow_ne_zero _ (hr w))
    have hiS : ContinuousOn (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2 * Real.sin (θ + w.2.1) ^ 2)⁻¹)
        ((Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)) :=
      (show ContinuousOn (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2 * Real.sin (θ + w.2.1) ^ 2) _ by
          fun_prop).inv₀ (fun w hw =>
            mul_ne_zero (pow_ne_zero _ (hr w)) (pow_ne_zero _ (ne_of_gt (hs w hw))))
    fin_cases i <;> fin_cases j <;> first
      | exact hiH
      | exact hiR
      | exact hiS
      | exact continuousOn_const (c := (0 : ℝ))
  · intro i j
    fin_cases i <;> fin_cases j <;> first
      | simpa [coordinateMetric, coordinateMetricPartial, nullMetricMatrix, Matrix.diagonal,
          HasL2ProductDerivatives, Fin.forall_fin_succ] using hzero
      | simpa [coordinateMetric, coordinateMetricPartial, nullMetricMatrix, Matrix.diagonal,
          HasL2ProductDerivatives, Fin.forall_fin_succ] using hH
      | simpa [coordinateMetric, coordinateMetricPartial, nullMetricMatrix, Matrix.diagonal,
          HasL2ProductDerivatives, Fin.forall_fin_succ] using hR
      | simpa [coordinateMetric, coordinateMetricPartial, nullMetricMatrix, Matrix.diagonal,
          HasL2ProductDerivatives, Fin.forall_fin_succ] using hS
  · intro w hw
    exact nullMetric_geometry (Real.exp_pos _) (sq_pos_of_ne_zero (hr w)) (sq_pos_of_pos (hs w hw))

end CauchyHorizon
