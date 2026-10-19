import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-! Strict improvement on every prefix prevents a first contact with zero. -/

open Set

namespace CauchyHorizon

theorem continuous_prefix_bootstrap {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {U : ℝ} {f : ℝ × K → ℝ} (hf : Continuous f) (hzero : ∀ k, f (0, k) < 0)
    (himprove : ∀ t ∈ Icc (0 : ℝ) U,
      (∀ q ∈ Icc (0 : ℝ) t, ∀ k, f (q, k) ≤ 0) → ∀ k, f (t, k) < 0) :
    ∀ t ∈ Icc (0 : ℝ) U, ∀ k, f (t, k) < 0 := by
  intro t ht k
  by_contra hbad
  let S := (Icc (0 : ℝ) U ×ˢ (univ : Set K)) ∩ {z | 0 ≤ f z}
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_univ).inter_right
    (isClosed_le continuous_const hf)
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn ⟨(t, k), ⟨⟨ht, mem_univ _⟩, not_lt.1 hbad⟩⟩
    continuous_fst.continuousOn
  have hprefix : ∀ q ∈ Icc (0 : ℝ) z.1, ∀ j, f (q, j) ≤ 0 := by
    intro q hq j
    by_contra hqbad
    have hpos := lt_of_not_ge hqbad
    obtain ⟨w, hw, heq⟩ := intermediate_value_Icc hq.1
      (hf.comp (continuous_id.prodMk continuous_const)).continuousOn
      (show 0 ∈ Icc (f (0, j)) (f (q, j)) from ⟨(hzero j).le, hpos.le⟩)
    have hwq : w < q := lt_of_le_of_ne hw.2 (by intro he; subst q; exact hpos.ne' heq)
    have hwS : (w, j) ∈ S := ⟨⟨⟨hw.1, hw.2.trans (hq.2.trans hz.1.1.2)⟩, mem_univ _⟩, heq.ge⟩
    exact (hwq.trans_le hq.2).not_ge (hmin hwS)
  exact (himprove z.1 hz.1.1 hprefix z.2).not_ge hz.2

end CauchyHorizon
