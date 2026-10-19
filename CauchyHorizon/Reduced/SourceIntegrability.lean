import CauchyHorizon.Reduced.IntegralMap
import CauchyHorizon.Analysis.RectangleLp

/-! The actual nonlinear source is integrable on the full characteristic rectangle. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

theorem wave_source_integrable {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (x : WaveState U V) (hr : ∀ u v, x.1 u v 0 ≠ 0) (i : Fin 3) :
    IntegrableOn (fun q : ℝ × ℝ => waveSource e Λ
      (x.1 (projIcc 0 U hU q.1) (projIcc 0 V hV q.2))
      (x.2.2 q.1 (projIcc 0 V hV q.2))
      (x.2.1 (projIcc 0 U hU q.1) (projIcc 0 V hV q.2)) i) (Icc 0 U ×ˢ Icc 0 V) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  let F := rectangleSource hU e Λ x hr
  have hp := (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ).comp_memLp'
    (memLp_rectangle_evaluation hV F)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hp
  have hi : Integrable (fun q : ℝ × ℝ => F q.1 (projIcc 0 V hV q.2) i)
      ((volume.restrict (Icc 0 U)).prod (volume.restrict (Icc 0 V))) := hp.integrable (by norm_num)
  apply hi.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (rectangleSource_ae hU e Λ x hr)] with q hq
  exact congrArg (fun z : WaveVector => z i) (hq (projIcc 0 V hV q.2))

end CauchyHorizon
