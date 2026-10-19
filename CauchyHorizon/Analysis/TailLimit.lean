import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Instances.Real.Lemmas

/-! Completeness preserves the quantitative bound on every finite tail. -/

open Filter
open scoped Topology

namespace CauchyHorizon

theorem exists_limit_of_tail_bound {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
    {f : ℝ → E} {b : ℝ → ℝ} {T : ℝ} (hb : Tendsto b atTop (𝓝 0))
    (htail : ∀ s ≥ T, ∀ t ≥ s, dist (f s) (f t) ≤ b s) :
    ∃ z : E, Tendsto f atTop (𝓝 z) ∧ ∀ s ≥ T, dist (f s) z ≤ b s := by
  have hc : CauchySeq f := Metric.cauchySeq_iff'.2 (by
    intro ε hε
    obtain ⟨s, hsT, hsε⟩ := ((eventually_ge_atTop T).and (hb.eventually_lt_const hε)).exists
    refine ⟨s, fun t hst => ?_⟩
    rw [dist_comm]
    exact (htail s hsT t hst).trans_lt hsε)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨z, hz, fun s hs => ?_⟩
  exact le_of_tendsto (tendsto_const_nhds.dist hz)
    ((eventually_ge_atTop s).mono (fun t ht => htail s hs t ht))

end CauchyHorizon
