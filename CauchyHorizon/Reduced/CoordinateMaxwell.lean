import CauchyHorizon.Reduced.CoordinateMetric
import CauchyHorizon.Geometry.ElectricField

/-! The actual electric field obeys both weak Maxwell equations through the horizon. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

noncomputable def coordinateMaxwell {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e : ℝ) (x : WaveState U V) (w : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  electricTwoForm (e * Real.exp (z 2) / (2 * z 0 ^ 2))

noncomputable def coordinateVolumeDensity {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  Real.exp (z 2) * z 0 ^ 2 * Real.sin (θ + w.2.1) / 2

noncomputable def coordinateMaxwellFlux {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e : ℝ) (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  coordinateVolumeDensity hU hV x θ w •
    raiseTwoForm (coordinateMetricInverse hU hV x θ w) (coordinateMaxwell hU hV e x w)

noncomputable def coordinateMaxwellStress {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e : ℝ) (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  maxwellStress (coordinateMetric hU hV x θ w) (coordinateMetricInverse hU hV x θ w)
    (coordinateMaxwell hU hV e x w)

def HasCoordinateMaxwell {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e : ℝ) (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi →
    (∀ i j, Continuous (fun w => coordinateMaxwell hU hV e x w i j) ∧
      MemLp (fun w => coordinateMaxwell hU hV e x w i j) 2 (rectangleProductMeasure U V A B) ∧
      MemLp (fun w => coordinateMaxwellFlux hU hV e x θ w i j) 2 (rectangleProductMeasure U V A B)) ∧
    (∀ w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B),
      0 < coordinateVolumeDensity hU hV x θ w ∧
      Real.sqrt |(coordinateMetric hU hV x θ w).det| = coordinateVolumeDensity hU hV x θ w) ∧
    (∀ w i j, coordinateMaxwell hU hV e x w i j = -coordinateMaxwell hU hV e x w j i) ∧
    (∀ i j k, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate i)
        (rectangleProductDistribution U V A B (fun w => coordinateMaxwell hU hV e x w j k)) +
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate j)
        (rectangleProductDistribution U V A B (fun w => coordinateMaxwell hU hV e x w k i)) +
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate k)
        (rectangleProductDistribution U V A B (fun w => coordinateMaxwell hU hV e x w i j)) = 0) ∧
    ∀ j, (∑ i, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate i)
      (rectangleProductDistribution U V A B (fun w => coordinateMaxwellFlux hU hV e x θ w i j))) = 0

set_option maxHeartbeats 2000000 in
theorem IsWaveIntegral.coordinate_maxwell {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasCoordinateMaxwell hU hV e x := by
  intro A B θ hA hB hθ hθA
  let μ := rectangleProductMeasure U V A B
  let ν := volume.restrict (Icc 0 A ×ˢ Icc 0 B)
  let : IsFiniteMeasure μ := by
    simp only [μ, rectangleProductMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let z := fun y : ℝ × ℝ => x.1 (projIcc 0 U hU y.1) (projIcc 0 V hV y.2)
  let f := fun y => e * Real.exp (z y 2) / (2 * z y 0 ^ 2)
  let g := fun y : ℝ × ℝ => -e * Real.sin (θ + y.1)
  have hF := hx.weak_composition hzin (fun z => e * Real.exp (z 2) / (2 * z 0 ^ 2))
    (fun u v => by
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (hx.choose u v)))
  have hFP := l2_product_derivatives hF (l2_constant_derivatives hA hB 1)
  have hLp {a : ℝ × ℝ → ℝ} (ha : Continuous a) : MemLp a 2 ν := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn ha.continuousOn
    exact MemLp.of_bound ha.aestronglyMeasurable C
      ((ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)).mono fun y hy => hC y hy)
  have hG : HasL2FirstDerivatives A B g (fun y => -e * Real.cos (θ + y.1)) (fun _ => 0) := by
    refine l2_first_derivatives_of_sections hA hB (hLp (by fun_prop)) (hLp (by fun_prop))
      (hLp continuous_const) ?_ ?_ ?_ ?_
    · intro v
      exact (show ContDiff ℝ 1 (fun u : ℝ => -e * Real.sin (θ + u)) by
        fun_prop).contDiffOn.absolutelyContinuousOnInterval
    · intro v
      apply Eventually.of_forall
      intro u
      change HasDerivWithinAt (fun t => -e * Real.sin (θ + t)) (-e * Real.cos (θ + u)) (Icc 0 A) u
      simpa only [mul_one, id_eq] using
        (((hasDerivAt_id u).const_add θ).sin.const_mul (-e)).hasDerivWithinAt (s := Icc 0 A)
    · intro u
      exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => -e * Real.sin (θ + u))).contDiffOn.absolutelyContinuousOnInterval
    · exact fun u => Eventually.of_forall fun v => hasDerivWithinAt_const v (Icc 0 B) (-e * Real.sin (θ + u))
  have hGP := l2_product_derivatives (l2_constant_derivatives hU hV 1) hG
  have hfi : MemLp (fun w : (ℝ × ℝ) × (ℝ × ℝ) => f w.1) 2 μ := by
    simpa only [mul_one, f, z, μ] using hFP.1
  have hgi : MemLp (fun w : (ℝ × ℝ) × (ℝ × ℝ) => g w.2) 2 μ := by
    simpa only [one_mul] using hGP.1
  have hfcont : Continuous (fun w : (ℝ × ℝ) × (ℝ × ℝ) => f w.1) := by
    have hr (w : (ℝ × ℝ) × (ℝ × ℝ)) : 2 * z w.1 0 ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero _ (hx.choose _ _))
    exact (by fun_prop : Continuous (fun w : (ℝ × ℝ) × (ℝ × ℝ) => e * Real.exp (z w.1 2))).div
      (by fun_prop) hr
  have hflux (w : (ℝ × ℝ) × (ℝ × ℝ)) :
      coordinateMaxwellFlux hU hV e x θ w = electricTwoForm (g w.2) :=
    electric_density (Real.exp_ne_zero _) (hx.choose _ _)
  have hpair {a : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (ha : Integrable a μ)
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B a ψ = ∫ w, a w * ψ w ∂μ := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ a ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (ha.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hzero : rectangleProductDistribution U V A B (fun _ => 0) = 0 := by
    ext ψ
    rw [hpair (integrable_const 0)]
    simp only [zero_mul, integral_zero, zero_apply]
  have helectric {a : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (ha : Integrable a μ) (i j : Fin 4) :
      rectangleProductDistribution U V A B (fun w => electricTwoForm (a w) i j) =
        electricTwoForm (rectangleProductDistribution U V A B a) i j := by
    have hneg : rectangleProductDistribution U V A B (fun w => -a w) =
        -rectangleProductDistribution U V A B a := by
      ext ψ
      have han : Integrable (fun w => -a w) μ := ha.neg
      rw [hpair han, neg_apply, hpair ha]
      simp only [neg_mul, integral_neg]
    fin_cases i <;> fin_cases j <;> first | exact hzero | exact hneg | rfl
  have hf2 : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 2)
      (rectangleProductDistribution U V A B (fun w => f w.1)) = 0 := by
    simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, hzero, f, z]
      using (hFP.2 2).2
  have hf3 : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 3)
      (rectangleProductDistribution U V A B (fun w => f w.1)) = 0 := by
    simpa [Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, hzero, f, z]
      using (hFP.2 3).2
  have hg0 : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 0)
      (rectangleProductDistribution U V A B (fun w => g w.2)) = 0 := by
    have hh := (hGP.2 0).2
    change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 0)
      (rectangleProductDistribution U V A B (fun w => 1 * g w.2)) =
        rectangleProductDistribution U V A B (fun w => 0 * g w.2) at hh
    simpa only [one_mul, zero_mul, hzero] using hh
  have hg1 : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 1)
      (rectangleProductDistribution U V A B (fun w => g w.2)) = 0 := by
    have hh := (hGP.2 1).2
    change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 1)
      (rectangleProductDistribution U V A B (fun w => 1 * g w.2)) =
        rectangleProductDistribution U V A B (fun w => 0 * g w.2) at hh
    simpa only [one_mul, zero_mul, hzero] using hh
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    have hFC : Continuous (fun w => coordinateMaxwell hU hV e x w i j) := by
      fin_cases i <;> fin_cases j <;> first | exact continuous_const | exact hfcont.neg | exact hfcont
    have hFL : MemLp (fun w => coordinateMaxwell hU hV e x w i j) 2 μ := by
      fin_cases i <;> fin_cases j <;> first | exact memLp_const 0 | exact hfi.neg | exact hfi
    refine ⟨hFC, hFL, ?_⟩
    simp_rw [hflux]
    fin_cases i <;> fin_cases j <;> first | exact memLp_const 0 | exact hgi.neg | exact hgi
  · intro w hw
    exact null_metric_volume (Real.exp_pos _) (hx.choose _ _) (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hw.2.1.1]) (by linarith [hw.2.1.2]))
  · intro w i j
    fin_cases i <;> fin_cases j <;> simp [coordinateMaxwell, electricTwoForm]
  · intro i j k
    change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate i)
        (rectangleProductDistribution U V A B (fun w => electricTwoForm (f w.1) j k)) +
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate j)
        (rectangleProductDistribution U V A B (fun w => electricTwoForm (f w.1) k i)) +
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate k)
        (rectangleProductDistribution U V A B (fun w => electricTwoForm (f w.1) i j)) = 0
    simp_rw [helectric (hfi.integrable (by norm_num))]
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [electricTwoForm, map_neg, hf2, hf3]
  · intro j
    simp_rw [hflux, helectric (hgi.integrable (by norm_num))]
    rw [Fin.sum_univ_four]
    fin_cases j <;> simp [electricTwoForm, map_neg, hg0, hg1]

end CauchyHorizon
