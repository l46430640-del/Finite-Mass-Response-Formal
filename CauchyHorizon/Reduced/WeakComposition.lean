import CauchyHorizon.Reduced.LongitudinalFlux
import CauchyHorizon.Analysis.RectangleLp
import CauchyHorizon.Analysis.RectangleWeakDerivative

/-! A local C1 observable of the actual integral field obeys the weak chain rule. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.weak_composition {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (G : WaveVector → ℝ) (hG : ∀ u v, ContDiffAt ℝ 1 G (x.1 u v)) :
    let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
    let p := fun w : ℝ × ℝ => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
    let q := fun w : ℝ × ℝ => x.2.2 w.1 (projIcc 0 V hV w.2)
    HasL2FirstDerivatives U V (fun w => G (z w))
      (fun w => fderiv ℝ G (z w) (q w)) (fun w => fderiv ℝ G (z w) (p w)) := by
  let : IsFiniteMeasure (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let p := fun w : ℝ × ℝ => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let q := fun w : ℝ × ℝ => x.2.2 w.1 (projIcc 0 V hV w.2)
  have hcx : Continuous (fun w : Icc 0 U × Icc 0 V => x.1 w.1 w.2) := by fun_prop
  let g : C(Icc 0 U × Icc 0 V, ℝ) := ⟨fun w => G (x.1 w.1 w.2),
    continuous_iff_continuousAt.2 (fun w =>
      (hG w.1 w.2).continuousAt.comp
        (f := fun w : Icc 0 U × Icc 0 V => x.1 w.1 w.2) hcx.continuousAt)⟩
  let A : C(Icc 0 U × Icc 0 V, WaveVector →L[ℝ] ℝ) := ⟨fun w => fderiv ℝ G (x.1 w.1 w.2),
    continuous_iff_continuousAt.2 (fun w =>
      ((hG w.1 w.2).continuousAt_fderiv (by norm_num)).comp
        (f := fun w : Icc 0 U × Icc 0 V => x.1 w.1 w.2) hcx.continuousAt)⟩
  have hcg : Continuous (fun w => G (z w)) := by
    change Continuous (fun w : ℝ × ℝ => g (projIcc 0 U hU w.1, projIcc 0 V hV w.2))
    fun_prop
  have hcA : Continuous (fun w => fderiv ℝ G (z w)) := by
    change Continuous (fun w : ℝ × ℝ => A (projIcc 0 U hU w.1, projIcc 0 V hV w.2))
    fun_prop
  have hg : MemLp (fun w => G (z w)) 2 (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) :=
    MemLp.of_bound hcg.aestronglyMeasurable ‖g‖ (Eventually.of_forall fun w =>
      g.norm_coe_le_norm (projIcc 0 U hU w.1, projIcc 0 V hV w.2))
  have hp : MemLp p 2 (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) := by
    apply MemLp.of_bound (by dsimp only [p]; fun_prop) ‖x.2.1‖
    exact Eventually.of_forall fun w =>
      ((x.2.1 (projIcc 0 U hU w.1)).norm_coe_le_norm _).trans (x.2.1.norm_coe_le_norm _)
  have hq := memLp_rectangle_evaluation hV x.2.2
  have hLp {f : ℝ × ℝ → WaveVector} (hf : MemLp f 2 (volume.restrict (Icc 0 U ×ˢ Icc 0 V))) :
      MemLp (fun w => fderiv ℝ G (z w) (f w)) 2 (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) := by
    have hc : Continuous (fun w : (WaveVector →L[ℝ] ℝ) × WaveVector => w.1 w.2) := by fun_prop
    apply (hf.norm.const_smul ‖A‖).mono'
      (hc.comp_aestronglyMeasurable (hcA.aestronglyMeasurable.prodMk hf.1))
    exact Eventually.of_forall fun w => ((fderiv ℝ G (z w)).le_opNorm (f w)).trans
      (mul_le_mul_of_nonneg_right
        (A.norm_coe_le_norm (projIcc 0 U hU w.1, projIcc 0 V hV w.2)) (norm_nonneg _))
  apply l2_first_derivatives_of_sections hU hV hg (hLp hq) (hLp hp)
  · intro v
    let E : C(Icc 0 V, WaveVector) →L[ℝ] WaveVector := ContinuousMap.evalCLM ℝ (projIcc 0 V hV v)
    have hAC : AbsolutelyContinuousOnInterval (fun u => z (u, v)) 0 U :=
      absolutelyContinuous_comp_contDiffAt (g := E) (hx.horizontal_absolutelyContinuous hzin)
        (fun _ _ => E.contDiff.contDiffAt)
    apply absolutelyContinuous_comp_contDiffAt (g := G) hAC
    rintro _ ⟨u, _hu, rfl⟩
    exact hG _ _
  · intro v
    let E : C(Icc 0 V, WaveVector) →L[ℝ] WaveVector := ContinuousMap.evalCLM ℝ (projIcc 0 V hV v)
    filter_upwards [hx.horizontal_derivative hzin] with u hu
    have hd : HasDerivWithinAt (fun t => z (t, v)) (q (u, v)) (Icc 0 U) u :=
      E.hasFDerivAt.comp_hasDerivWithinAt u hu
    exact ((hG _ _).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivWithinAt u hd
  · intro u
    have he : ContinuousMap.const _ (zIn (projIcc 0 U hU u)) +
        continuousPrimitive hV (x.2.1 (projIcc 0 U hU u)) = x.1 (projIcc 0 U hU u) :=
      congrArg (fun y : WaveState U V => y.1 (projIcc 0 U hU u)) hx.choose_spec
    have hAC : AbsolutelyContinuousOnInterval (fun v => z (u, v)) 0 V := by
      change AbsolutelyContinuousOnInterval (intervalExtension hV (x.1 (projIcc 0 U hU u))) 0 V
      rw [← he, map_add, ← horizontalPrimitive_intervalToLp]
      exact horizontalPrimitive_absolutelyContinuous hV _ _
    apply absolutelyContinuous_comp_contDiffAt (g := G) hAC
    rintro _ ⟨v, _hv, rfl⟩
    exact hG _ _
  · intro u
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hd := hx.longitudinal_derivative (projIcc 0 U hU u) hv
    have hh := ((hG (projIcc 0 U hU u) (projIcc 0 V hV v)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivWithinAt v hd
    change HasDerivWithinAt (fun t => G (z (u, t)))
      (fderiv ℝ G (z (u, v)) (x.2.1 (projIcc 0 U hU u) ⟨v, hv⟩)) (Icc 0 V) v at hh
    simpa only [p, projIcc_of_mem hV hv] using hh

end CauchyHorizon
