import CauchyHorizon.Reduced.EinsteinEquation
import CauchyHorizon.Reduced.ScalarTransport

/-! The actual scalar current has zero weak covariant divergence through the horizon. -/

open MeasureTheory Set Filter
open scoped Distributions ENNReal

namespace CauchyHorizon

noncomputable def scalarNullFlux {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (i : Fin 2) (w : ℝ × ℝ) : ℝ :=
  let r := x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) 0
  ![r ^ 2 * x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) 1,
    r ^ 2 * x.2.2 w.1 (projIcc 0 V hV w.2) 1] i

noncomputable def scalarNullSource {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (w : ℝ × ℝ) : ℝ :=
  let z := x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let p := x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let q := x.2.2 w.1 (projIcc 0 V hV w.2)
  z 0 * (q 0 * p 1 - p 0 * q 1)

set_option maxHeartbeats 1500000 in
theorem IsWaveIntegral.scalar_flux_derivatives {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    (∀ i, MemLp (scalarNullFlux hU hV x i) 2 (volume.restrict (Icc 0 U ×ˢ Icc 0 V))) ∧
    IntegrableOn (scalarNullSource hU hV x) (Icc 0 U ×ˢ Icc 0 V) ∧
    ∀ (A B : ℝ) (b : ℝ × ℝ → ℝ), IntegrableOn b (Icc 0 A ×ˢ Icc 0 B) →
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((1, 0), (0, 0))
        (rectangleProductDistribution U V A B (fun w => scalarNullFlux hU hV x 0 w.1 * b w.2)) =
          rectangleProductDistribution U V A B (fun w => scalarNullSource hU hV x w.1 * b w.2) ∧
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 1), (0, 0))
        (rectangleProductDistribution U V A B (fun w => scalarNullFlux hU hV x 1 w.1 * b w.2)) =
          rectangleProductDistribution U V A B (fun w => -scalarNullSource hU hV x w.1 * b w.2) := by
  let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let p := fun w : ℝ × ℝ => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let q := fun w : ℝ × ℝ => x.2.2 w.1 (projIcc 0 V hV w.2)
  let f₀ := scalarNullFlux hU hV x 0
  let f₁ := scalarNullFlux hU hV x 1
  let g := scalarNullSource hU hV x
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hz (i : Fin 3) : Continuous (fun w => z w i) := by fun_prop
  have hp (i : Fin 3) : Continuous (fun w => p w i) := by fun_prop
  have hLp {f : ℝ × ℝ → ℝ} {a : ℝ≥0∞} (hf : Continuous f) : MemLp f a μ := by
    obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
    exact MemLp.of_bound hf.aestronglyMeasurable K
      ((ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)).mono fun w hw => hK w hw)
  have hq (i : Fin 3) : MemLp (fun w => q w i) 2 μ := (hx.weak_first_derivatives hzin i).2.2.1
  have hF₀ : MemLp f₀ 2 μ := hLp (((hz 0).pow 2).mul (hp 1))
  have hF₁ : MemLp f₁ 2 μ := (hq 1).mul' (hLp ((hz 0).pow 2) : MemLp _ ∞ μ)
  have hG : Integrable g μ := by
    have hh := ((hq 0).integrable_mul (hLp ((hz 0).mul (hp 1)) : MemLp _ 2 μ)).sub
      ((hq 1).integrable_mul (hLp ((hz 0).mul (hp 0)) : MemLp _ 2 μ))
    apply hh.congr
    exact Eventually.of_forall fun w => by dsimp only [g, scalarNullSource, z, p, q, Pi.mul_apply, Pi.sub_apply]; ring
  have hAC₀ (v : ℝ) : AbsolutelyContinuousOnInterval (fun u => f₀ (u, v)) 0 U := by
    let v' := projIcc 0 V hV v
    let E (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v')
    have hR := absolutelyContinuous_comp_contDiffAt (g := fun y => (E 0 y) ^ 2)
      (hx.horizontal_absolutelyContinuous hzin) (fun _ _ => (E 0).contDiff.contDiffAt.pow 2)
    have hP := absolutelyContinuous_comp_contDiffAt (g := E 1)
      hx.velocity_horizontal_absolutelyContinuous (fun _ _ => (E 1).contDiff.contDiffAt)
    exact hR.mul hP
  have hd₀ (v : ℝ) : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (fun t => f₀ (t, v)) (g (u, v)) (Icc 0 U) u := by
    filter_upwards [hx.horizontal_derivative hzin, hx.wave_equation] with u hz' hp'
    let v' := projIcc 0 V hV v
    let E (i : Fin 3) : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj i
    let R : C(Icc 0 V, WaveVector) →L[ℝ] ℝ := (E 0).comp (ContinuousMap.evalCLM ℝ v')
    have hZ := R.hasFDerivAt.comp_hasDerivWithinAt u hz'
    have hP := (E 1).hasFDerivAt.comp_hasDerivWithinAt u (hp' v')
    apply ((hZ.pow 2).mul hP).congr_deriv
    simp only [E, R, Pi.pow_apply, Function.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply,
      ContinuousMap.evalCLM_apply, intervalExtension_apply, g, scalarNullSource, v', waveSource,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp [hx.choose (projIcc 0 U hU u) (projIcc 0 V hV v)]
    ring
  have hsecond : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      AbsolutelyContinuousOnInterval (fun v => f₁ (u, v)) 0 V ∧
        ∀ v ∈ Icc 0 V, HasDerivWithinAt (fun t => f₁ (u, t)) (-g (u, v)) (Icc 0 V) v := by
    filter_upwards [hx.transverse_longitudinal_derivative] with u ht
    let u' := projIcc 0 U hU u
    have hd (v : ℝ) (hv : v ∈ Icc 0 V) :
        HasDerivWithinAt (fun t => f₁ (u, t)) (-g (u, v)) (Icc 0 V) v := by
      let E (i : Fin 3) : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj i
      have hZ := (E 0).hasFDerivAt.comp_hasDerivWithinAt v (hx.longitudinal_derivative u' hv)
      have hQ := (E 1).hasFDerivAt.comp_hasDerivWithinAt v (ht ⟨v, hv⟩)
      apply ((hZ.pow 2).mul hQ).congr_deriv
      simp only [E, Pi.pow_apply, Function.comp_apply, ContinuousLinearMap.proj_apply, intervalExtension_apply,
        g, scalarNullSource, u', projIcc_of_mem hV hv, waveSource, Matrix.cons_val_one, Matrix.cons_val_zero]
      field_simp [hx.choose (projIcc 0 U hU u) ⟨v, hv⟩]
      ring
    refine ⟨?_, hd⟩
    let d : C(Icc 0 V, ℝ) := ⟨fun v => -g (u, v), by dsimp only [g, scalarNullSource]; fun_prop⟩
    have hl : LipschitzOnWith ‖d‖₊ (fun v => f₁ (u, v)) (Icc 0 V) :=
      (convex_Icc (0 : ℝ) V).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hd
        (fun v hv => show ‖d ⟨v, hv⟩‖₊ ≤ ‖d‖₊ from d.norm_coe_le_norm ⟨v, hv⟩)
    have hl' : LipschitzOnWith ‖d‖₊ (fun v => f₁ (u, v)) (uIcc 0 V) := by
      simpa only [uIcc_of_le hV] using hl
    exact hl'.absolutelyContinuousOnInterval
  refine ⟨?_, hG, ?_⟩
  · intro i
    fin_cases i
    · exact hF₀
    · exact hF₁
  · intro A B b hb
    exact null_weighted_derivatives_of_sections hU hV (hF₀.integrable (by norm_num))
      (hF₁.integrable (by norm_num)) hG hG.neg (Eventually.of_forall hAC₀)
      (Eventually.of_forall hd₀) (hsecond.mono fun _ h => h.1)
      (hsecond.mono fun _ h => (ae_restrict_mem measurableSet_Icc).mono fun v hv => h.2 v hv) b hb

noncomputable def coordinateScalarFlux {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) (i : Fin 4) : ℝ :=
  coordinateVolumeDensity hU hV x θ w *
    ∑ j, coordinateMetricInverse hU hV x θ w i j * coordinateScalarGradient hU hV x w j

theorem coordinateScalarFlux_eq {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    coordinateScalarFlux hU hV x θ w =
      ![scalarNullFlux hU hV x 0 w.1 * -Real.sin (θ + w.2.1),
        scalarNullFlux hU hV x 1 w.1 * -Real.sin (θ + w.2.1), 0, 0] := by
  funext i
  fin_cases i <;>
    norm_num [coordinateScalarFlux, coordinateVolumeDensity, coordinateMetricInverse, nullMetricInverse,
      coordinateScalarGradient, scalarNullFlux, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
    field_simp [Real.exp_ne_zero]

def HasCoordinateScalarEquation {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi →
    (∀ i, MemLp (fun w => coordinateScalarFlux hU hV x θ w i) 2 (rectangleProductMeasure U V A B)) ∧
    (∑ i, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate i)
      (rectangleProductDistribution U V A B (fun w => coordinateScalarFlux hU hV x θ w i))) = 0

set_option maxHeartbeats 1500000 in
theorem IsWaveIntegral.coordinate_scalar_equation {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasCoordinateScalarEquation hU hV x := by
  intro A B θ hA hB hθ hθA
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  let ν := volume.restrict (Icc 0 A ×ˢ Icc 0 B)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let b := fun w : ℝ × ℝ => -Real.sin (θ + w.1)
  let : IsFiniteMeasure (rectangleProductMeasure U V A B) :=
    (inferInstance : IsFiniteMeasure (μ.prod ν))
  have hb : MemLp b 2 ν := by
    have hc : Continuous b := by fun_prop
    obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc.continuousOn
    exact MemLp.of_bound hc.aestronglyMeasurable K
      ((ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)).mono fun w hw => hK w hw)
  have hF := hx.scalar_flux_derivatives hzin
  have hLp (i : Fin 2) : MemLp (fun w : (ℝ × ℝ) × (ℝ × ℝ) => scalarNullFlux hU hV x i w.1 * b w.2)
      2 (μ.prod ν) := by
    apply (memLp_two_iff_integrable_sq ((hF.1 i).1.comp_fst.mul hb.1.comp_snd)).2
    simpa only [Pi.mul_apply, mul_pow] using
      ((memLp_two_iff_integrable_sq (hF.1 i).1).1 (hF.1 i)).mul_prod
        ((memLp_two_iff_integrable_sq hb.1).1 hb)
  have he (w : (ℝ × ℝ) × (ℝ × ℝ)) : coordinateScalarFlux hU hV x θ w =
      ![scalarNullFlux hU hV x 0 w.1 * b w.2, scalarNullFlux hU hV x 1 w.1 * b w.2, 0, 0] :=
    coordinateScalarFlux_eq hU hV x θ w
  have hpair {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B f ψ = ∫ w, f w * ψ w ∂(μ.prod ν) := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) (μ.prod ν) f ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hzero : rectangleProductDistribution U V A B (fun _ => 0) = 0 := by
    ext ψ
    rw [hpair (integrable_const 0)]
    simp only [zero_mul, integral_zero, zero_apply]
  have hn : rectangleProductDistribution U V A B (fun w => -scalarNullSource hU hV x w.1 * b w.2) =
      -rectangleProductDistribution U V A B (fun w => scalarNullSource hU hV x w.1 * b w.2) := by
    ext ψ
    have hi : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => -scalarNullSource hU hV x w.1 * b w.2)
        (μ.prod ν) := hF.2.1.neg.mul_prod (hb.integrable (by norm_num))
    rw [hpair hi, neg_apply,
      hpair (hF.2.1.mul_prod (hb.integrable (by norm_num)))]
    simp only [neg_mul, integral_neg]
  refine ⟨?_, ?_⟩
  · intro i
    simp_rw [he]
    fin_cases i
    · exact hLp 0
    · exact hLp 1
    · exact memLp_const 0
    · exact memLp_const 0
  · have hd := hF.2.2 A B b (hb.integrable (by norm_num))
    have hn' : rectangleProductDistribution U V A B (fun w => -(scalarNullSource hU hV x w.1 * b w.2)) =
        -rectangleProductDistribution U V A B (fun w => scalarNullSource hU hV x w.1 * b w.2) := by
      simpa only [neg_mul] using hn
    simp_rw [he]
    rw [Fin.sum_univ_four]
    simp [productCoordinate, hzero, hd.1, hd.2, hn']

end CauchyHorizon
