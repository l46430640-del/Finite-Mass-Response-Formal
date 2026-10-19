import CauchyHorizon.Analysis.IntervalOperators

/-! An L2 input and a continuous two-variable coefficient have a jointly continuous primitive. -/

open Set MeasureTheory

namespace CauchyHorizon

theorem continuous_kernel_primitive {U V : ℝ} (hU : 0 ≤ U)
    (K : C(Icc 0 U, C(Icc 0 V, ℝ))) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Icc 0 U))) :
    Continuous (fun q : Icc 0 U × Icc 0 V =>
      ∫ t in (0 : ℝ)..q.1, K (projIcc 0 U hU t) q.2 * f t) := by
  have hF : MemLp (fun t => f t • K (projIcc 0 U hU t)) 2 (volume.restrict (Icc 0 U)) :=
    (intervalExtension hU K).memLp_top.smul hf
  let F := hF.toLp (fun t => f t • K (projIcc 0 U hU t))
  let P := horizontalPrimitive hU F
  apply P.uncurry.continuous.congr
  intro q
  have hi : IntegrableOn (fun t => F t) (Icc 0 U) := (Lp.memLp F).integrable (by norm_num)
  have hiq : IntervalIntegrable (fun t => F t) volume 0 q.1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le q.1.property.1).2
    (hi.mono_set (Icc_subset_Icc le_rfl q.1.property.2))
  have he := (ContinuousMap.evalCLM ℝ q.2 : C(Icc 0 V, ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm hiq
  simp only [ContinuousMap.evalCLM_apply] at he
  change (∫ t in (0 : ℝ)..q.1, F t) q.2 = _
  rw [← he]
  simp only [intervalIntegral.integral_of_le q.1.property.1]
  apply integral_congr_ae
  have hs : Ioc (0 : ℝ) q.1 ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans q.1.property.2⟩
  filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) hF.coeFn_toLp] with t ht
  rw [ht]
  change f t * K (projIcc 0 U hU t) q.2 = _
  exact mul_comm _ _

end CauchyHorizon
