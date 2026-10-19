import CauchyHorizon.Reduced.CoordinateMaxwell
import CauchyHorizon.Reduced.NullRicciSources
import CauchyHorizon.Reduced.MixedRicciSources
import CauchyHorizon.Reduced.AngularRicciSources
import CauchyHorizon.Reduced.OffDiagonalRicciSources

/-! The actual scalar gradient and Maxwell stress give every weak trace-reversed Einstein equation. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

noncomputable def coordinateScalarGradient {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (w : (ℝ × ℝ) × (ℝ × ℝ)) : Fin 4 → ℝ :=
  ![x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 1,
    x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 1, 0, 0]

noncomputable def coordinateEinsteinSource {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => 2 * coordinateScalarGradient hU hV x w i * coordinateScalarGradient hU hV x w j +
    2 * coordinateMaxwellStress hU hV e x θ w i j + Λ * coordinateMetric hU hV x θ w i j

def HasCoordinateEinsteinEquation {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi →
    HasL2ProductDerivatives U V A B
      (fun w => x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 1)
      (fun i w => coordinateScalarGradient hU hV x w i) ∧
    (∀ i j, Integrable (fun w => coordinateEinsteinSource hU hV e Λ x θ w i j)
      (rectangleProductMeasure U V A B) ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) i j =
        rectangleProductDistribution U V A B (fun w => coordinateEinsteinSource hU hV e Λ x θ w i j)) ∧
    ∀ w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B),
      (∑ i, ∑ j, coordinateMetricInverse hU hV x θ w i j * coordinateMaxwellStress hU hV e x θ w i j) = 0

set_option maxHeartbeats 2500000 in
theorem IsWaveIntegral.coordinate_einstein_equation {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hnull : HasNullRicciSources hU hV x) : HasCoordinateEinsteinEquation hU hV e Λ x := by
  intro A B θ hA hB hθ hθA
  let μ := rectangleProductMeasure U V A B
  let K := (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)
  let : IsFiniteMeasure μ := by
    simp only [μ, rectangleProductMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hAe : ∀ᵐ w ∂μ, w ∈ K := by
    have he : μ = volume.restrict K := by
      simp only [μ, K, rectangleProductMeasure, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [he]
    exact ae_restrict_mem ((measurableSet_Icc.prod measurableSet_Icc).prod
      (measurableSet_Icc.prod measurableSet_Icc))
  have hgeom (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) :=
    electric_stress (H := Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2))
      (e := e) (Real.exp_ne_zero _)
      (hx.choose (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2))
      (show Real.sin (θ + w.2.1) ≠ 0 from ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hw.2.1.1]) (by linarith [hw.2.1.2])))
  let S := fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
    !![2 * (nullScalarDerivative hU hV x 0 w) ^ 2, mixedRicciSource hU hV e Λ x w, 0, 0;
      mixedRicciSource hU hV e Λ x w, 2 * (nullScalarDerivative hU hV x 1 w) ^ 2, 0, 0;
      0, 0, angularRicciSource hU hV e Λ x θ 0 w, 0;
      0, 0, 0, angularRicciSource hU hV e Λ x θ 1 w]
  have hsource (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) (i j : Fin 4) :
      coordinateEinsteinSource hU hV e Λ x θ w i j = S w i j := by
    let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
    have he : 2 * coordinateMaxwellStress hU hV e x θ w i j =
        !![0, Real.exp (z 2) * e ^ 2 / (2 * z 0 ^ 4), 0, 0;
          Real.exp (z 2) * e ^ 2 / (2 * z 0 ^ 4), 0, 0, 0;
          0, 0, e ^ 2 / z 0 ^ 2, 0;
          0, 0, 0, e ^ 2 * Real.sin (θ + w.2.1) ^ 2 / z 0 ^ 2] i j := (hgeom w hw).1 i j
    dsimp only [coordinateEinsteinSource]
    rw [he]
    fin_cases i <;> fin_cases j <;>
      norm_num [S, z, nullScalarDerivative, mixedRicciSource, angularRicciSource,
        coordinateScalarGradient, coordinateMetric, nullMetricMatrix,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring
  have hpair {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f μ)
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B f ψ = ∫ w, f w * ψ w ∂μ := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ f ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hzero : rectangleProductDistribution U V A B (fun _ => 0) = 0 := by
    ext ψ
    rw [hpair (integrable_const 0)]
    simp only [zero_mul, integral_zero, zero_apply]
  have hn := hnull A B θ hA hB hθ hθA
  have hm := hx.mixed_ricci_sources hzin A B θ hA hB hθ hθA
  have ha := hx.angular_ricci_sources hzin A B θ hA hB hθ hθA
  have ho := hx.off_diagonal_ricci_sources hzin A B θ hA hB hθ hθA
  have hz {i j : Fin 4} (hr : ricciDistribution U V A B (coordinateChristoffel hU hV x θ) i j = 0) :
      Integrable (fun _ : (ℝ × ℝ) × (ℝ × ℝ) => (0 : ℝ)) μ ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) i j =
        rectangleProductDistribution U V A B (fun _ => 0) :=
    ⟨integrable_const 0, hr.trans hzero.symm⟩
  have hS (i j : Fin 4) : Integrable (fun w => S w i j) μ ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) i j =
        rectangleProductDistribution U V A B (fun w => S w i j) := by
    fin_cases i <;> fin_cases j
    · exact hn 0
    · exact ⟨hm.1, hm.2 0⟩
    · exact hz (ho.1 0 0).1
    · exact hz (ho.1 0 1).1
    · exact ⟨hm.1, hm.2 1⟩
    · exact hn 1
    · exact hz (ho.1 1 0).1
    · exact hz (ho.1 1 1).1
    · exact hz (ho.1 0 0).2
    · exact hz (ho.1 1 0).2
    · exact ha 0
    · exact hz ho.2.1
    · exact hz (ho.1 0 1).2
    · exact hz (ho.1 1 1).2
    · exact hz ho.2.2
    · exact ha 1
  refine ⟨?_, ?_, ?_⟩
  · have hh := hx.weak_first_derivatives hzin 1
    have hd : HasL2FirstDerivatives U V
        (fun y => x.1 (projIcc 0 U hU y.1) (projIcc 0 V hV y.2) 1)
        (fun y => x.2.2 y.1 (projIcc 0 V hV y.2) 1)
        (fun y => x.2.1 (projIcc 0 U hU y.1) (projIcc 0 V hV y.2) 1) :=
      ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2⟩
    have hp := l2_product_derivatives hd (l2_constant_derivatives hA hB 1)
    refine ⟨?_, ?_⟩
    · simpa only [mul_one] using hp.1
    · intro i
      fin_cases i
      · simpa [coordinateScalarGradient] using hp.2 0
      · simpa [coordinateScalarGradient] using hp.2 1
      · simpa [coordinateScalarGradient, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using hp.2 2
      · simpa [coordinateScalarGradient, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] using hp.2 3
  · intro i j
    have hi : Integrable (fun w => coordinateEinsteinSource hU hV e Λ x θ w i j) μ :=
      (hS i j).1.congr (hAe.mono fun w hw => (hsource w hw i j).symm)
    refine ⟨hi, (hS i j).2.trans ?_⟩
    ext ψ
    rw [hpair (hS i j).1, hpair hi]
    exact integral_congr_ae (hAe.mono fun w hw => congrArg (· * ψ w) (hsource w hw i j).symm)
  · intro w hw
    exact (hgeom w hw).2

end CauchyHorizon
