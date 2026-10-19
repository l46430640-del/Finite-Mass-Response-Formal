import CauchyHorizon.Characteristic.BandMatching

/-! Restrict an actual decreasing arrival function to a closed entered row. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

theorem exists_compact_arrival_chart {ε z u V : ℝ} {arrival slope : ℝ → ℝ}
    (hz : 0 < z) (hu : u < ε) (hzu : z ≤ u)
    (hc : ContinuousOn arrival (Ioo 0 ε)) (ha : StrictAntiOn arrival (Ioo 0 ε))
    (hpos : ∀ t ∈ Ioo 0 ε, 0 < arrival t)
    (hd : ∀ t ∈ Ioo z u, HasDerivAt arrival (slope t) t)
    (b : Icc 0 V) (hb : arrival z = b) :
    ∃ T : C(Icc z u, Icc 0 V),
      (∀ t, (T t : ℝ) = arrival t) ∧
      let τ := fun t => T (projIcc z u hzu t)
      τ z = b ∧
      (∀ t ∈ Ioo z u, HasDerivAt (fun t => (τ t : ℝ)) (slope t) t) ∧
      ∀ t ∈ Icc z u, arrival u ≤ (τ t : ℝ) ∧ τ t ≤ b := by
  have hsub : Icc z u ⊆ Ioo 0 ε := fun t ht => ⟨hz.trans_le ht.1, ht.2.trans_lt hu⟩
  have hzmem : z ∈ Ioo 0 ε := hsub (left_mem_Icc.2 hzu)
  have humem : u ∈ Ioo 0 ε := hsub (right_mem_Icc.2 hzu)
  have hmem (t : Icc z u) : arrival t ∈ Icc 0 V := by
    refine ⟨(hpos t (hsub t.property)).le, ?_⟩
    have hh := ha.antitoneOn hzmem (hsub t.property) t.property.1
    exact hh.trans (hb ▸ b.property.2)
  let T : C(Icc z u, Icc 0 V) :=
    ⟨fun t => ⟨arrival t, hmem t⟩, (continuousOn_iff_continuous_domRestrict.1 (hc.mono hsub)).subtype_mk _⟩
  refine ⟨T, fun _ => rfl, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change arrival (projIcc z u hzu z) = (b : ℝ)
    rw [projIcc_of_mem hzu (left_mem_Icc.2 hzu)]
    exact hb
  · intro t ht
    apply (hd t ht).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with q hq
    change arrival (projIcc z u hzu q) = arrival q
    rw [projIcc_of_mem hzu ⟨hq.1.le, hq.2.le⟩]
  · intro t ht
    change arrival (projIcc z u hzu t) ≥ arrival u ∧ arrival (projIcc z u hzu t) ≤ (b : ℝ)
    rw [projIcc_of_mem hzu ht]
    exact ⟨ha.antitoneOn (hsub ht) humem ht.2, (ha.antitoneOn hzmem (hsub ht) ht.1).trans_eq hb⟩

end CauchyHorizon
