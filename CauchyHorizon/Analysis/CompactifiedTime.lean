import CauchyHorizon.Analysis.CompatibleHalfline
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Piecewise
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Continuous traces on the compact extended observation half-line, including its endpoint. -/

open Set Filter
open scoped Topology ENNReal

namespace CauchyHorizon

theorem continuousOn_halfline_of_prefixes {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : ∀ T : Ici (0 : ℝ), ContinuousOn f (Icc 0 (T : ℝ))) : ContinuousOn f (Ici 0) := by
  obtain ⟨g, hg, he⟩ := exists_continuous_compatible_halfline (fun _ => f) hf
    (fun _ _ _ _ _ => rfl)
  apply hg.congr
  intro t ht
  exact (he ⟨t, ht⟩ ⟨ht, le_rfl⟩).symm

theorem ennreal_toReal_tendsto_at_top : Tendsto ENNReal.toReal (𝓝[≠] (⊤ : ℝ≥0∞)) atTop := by
  apply tendsto_atTop.2
  intro r
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (ENNReal.ofReal_lt_top (r := r)))] with t ht hr
  exact (ENNReal.ofReal_le_iff_le_toReal ht).1 hr.le

noncomputable def compactifiedTimeTrace {E : Type*} [TopologicalSpace E] {f : ℝ → E} {z : E}
    (hf : ContinuousOn f (Ici 0)) (hz : Tendsto f atTop (𝓝 z)) : C(ℝ≥0∞, E) := by
  classical
  refine ⟨Function.update (fun t : ℝ≥0∞ => f t.toReal) ⊤ z, ?_⟩
  apply continuous_iff_continuousAt.2
  intro t
  by_cases ht : t = ⊤
  · subst t
    exact continuousAt_update_same.2 (hz.comp ennreal_toReal_tendsto_at_top)
  · rw [continuousAt_update_of_ne ht]
    exact Filter.Tendsto.comp (hf t.toReal ENNReal.toReal_nonneg)
      (tendsto_nhdsWithin_iff.2 ⟨ENNReal.tendsto_toReal ht, Eventually.of_forall fun _ => ENNReal.toReal_nonneg⟩)

theorem compactifiedTimeTrace_top {E : Type*} [TopologicalSpace E] {f : ℝ → E} {z : E}
    (hf : ContinuousOn f (Ici 0)) (hz : Tendsto f atTop (𝓝 z)) : compactifiedTimeTrace hf hz ⊤ = z := by
  simp [compactifiedTimeTrace]

theorem compactifiedTimeTrace_finite {E : Type*} [TopologicalSpace E] {f : ℝ → E} {z : E}
    (hf : ContinuousOn f (Ici 0)) (hz : Tendsto f atTop (𝓝 z)) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    compactifiedTimeTrace hf hz t = f t.toReal := by
  simp [compactifiedTimeTrace, Function.update_of_ne ht]

theorem compactifiedTimeTrace_ofReal {E : Type*} [TopologicalSpace E] {f : ℝ → E} {z : E}
    (hf : ContinuousOn f (Ici 0)) (hz : Tendsto f atTop (𝓝 z)) {t : ℝ} (ht : 0 ≤ t) :
    compactifiedTimeTrace hf hz (ENNReal.ofReal t) = f t := by
  rw [compactifiedTimeTrace_finite hf hz ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ht]

theorem compactifiedTimeTrace_tendsto {ι E : Type*} [NormedAddCommGroup E] {l : Filter ι}
    {F : ι → ℝ → E} {Z : ι → E} {f : ℝ → E} {z : E}
    (hF : ∀ i, ContinuousOn (F i) (Ici 0)) (hZ : ∀ i, Tendsto (F i) atTop (𝓝 (Z i)))
    (hf : ContinuousOn f (Ici 0)) (hz : Tendsto f atTop (𝓝 z))
    (hseq : TendstoUniformlyOn F f l (Ici 0)) (hseqZ : Tendsto Z l (𝓝 z)) :
    Tendsto (fun i => compactifiedTimeTrace (hF i) (hZ i)) l (𝓝 (compactifiedTimeTrace hf hz)) := by
  apply Metric.tendsto_nhds.2
  intro d hd
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hseq (d / 2) (half_pos hd),
    Metric.tendsto_nhds.1 hseqZ (d / 2) (half_pos hd)] with i hi hz
  apply lt_of_le_of_lt ((ContinuousMap.dist_le (half_pos hd).le).2 ?_) (half_lt_self hd)
  intro t
  by_cases ht : t = ⊤
  · subst t
    simpa only [compactifiedTimeTrace_top] using hz.le
  · rw [compactifiedTimeTrace_finite _ _ ht, compactifiedTimeTrace_finite _ _ ht, dist_comm]
    exact (hi t.toReal ENNReal.toReal_nonneg).le

end CauchyHorizon
