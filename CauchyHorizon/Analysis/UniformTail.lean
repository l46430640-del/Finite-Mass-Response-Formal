import CauchyHorizon.Analysis.TailLimit
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! A common tail upgrades convergence on finite time intervals to uniform half-line convergence. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

theorem uniform_convergence_of_common_tail {ι E : Type*} [PseudoMetricSpace E] {l : Filter ι}
    {F : ι → ℝ → E} {f : ℝ → E} {Z : ι → E} {z : E} {b : ℝ → ℝ} {T₀ : ℝ}
    (hb : Tendsto b atTop (𝓝 0))
    (hF : ∀ i t, T₀ ≤ t → dist (F i t) (Z i) ≤ b t)
    (hf : ∀ t, T₀ ≤ t → dist (f t) z ≤ b t)
    (hfinite : ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn F f l (Icc 0 T)) :
    Tendsto Z l (𝓝 z) ∧ TendstoUniformlyOn F f l (Ici 0) := by
  have hcut (ε : ℝ) (hε : 0 < ε) : ∃ T : ℝ, 0 ≤ T ∧ T₀ ≤ T ∧ ∀ t ≥ T, b t < ε / 3 := by
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hb.eventually_lt_const (by positivity : 0 < ε / 3))
    exact ⟨max 0 (max T₀ T), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      fun t ht => hT t (((le_max_right _ _).trans (le_max_right _ _)).trans ht)⟩
  have hZ : Tendsto Z l (𝓝 z) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨T, hT, hT₀, htail⟩ := hcut ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hfinite T hT) (ε / 3) (by positivity)] with i hi
    have he := hi T ⟨hT, le_rfl⟩
    have htri := dist_triangle4 (Z i) (F i T) (f T) z
    rw [dist_comm (Z i) (F i T), dist_comm (F i T) (f T)] at htri
    linarith [hF i T hT₀, hf T hT₀, htail T le_rfl]
  refine ⟨hZ, Metric.tendstoUniformlyOn_iff.2 ?_⟩
  intro ε hε
  obtain ⟨T, hT, hT₀, htail⟩ := hcut ε hε
  filter_upwards [Metric.tendsto_nhds.1 hZ (ε / 3) (by positivity),
    Metric.tendstoUniformlyOn_iff.1 (hfinite T hT) ε hε] with i hi hhead
  intro t ht
  by_cases htT : t ≤ T
  · exact hhead t ⟨ht, htT⟩
  have hTt := (not_le.1 htT).le
  have htri := dist_triangle4 (f t) z (Z i) (F i t)
  rw [dist_comm z (Z i), dist_comm (Z i) (F i t)] at htri
  linarith [hF i t (hT₀.trans hTt), hf t (hT₀.trans hTt), htail t hTt]

end CauchyHorizon
