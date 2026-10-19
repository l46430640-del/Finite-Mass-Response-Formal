import CauchyHorizon.Analysis.IntervalOperators
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! Evaluation converts the mixed continuous L2 space to L2 on the product rectangle. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

theorem memLp_rectangle_evaluation {E : Type*} [NormedAddCommGroup E]
    {U V : ℝ} (hV : 0 ≤ V) (F : Lp C(Icc 0 V, E) 2 (volume.restrict (Icc 0 U))) :
    MemLp (fun w : ℝ × ℝ => F w.1 (projIcc 0 V hV w.2)) 2
      (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hc : Continuous (fun p : C(Icc 0 V, E) × ℝ => p.1 (projIcc 0 V hV p.2)) := by
    fun_prop
  have hm : AEStronglyMeasurable (fun w : ℝ × ℝ => F w.1 (projIcc 0 V hV w.2))
      ((volume.restrict (Icc 0 U)).prod (volume.restrict (Icc 0 V))) :=
    hc.comp_aestronglyMeasurable ((Lp.memLp F).1.comp_fst.prodMk continuous_snd.aestronglyMeasurable)
  exact ((Lp.memLp F).norm.comp_fst (volume.restrict (Icc 0 V))).mono' hm
    (Eventually.of_forall fun w => (F w.1).norm_coe_le_norm _)

end CauchyHorizon
