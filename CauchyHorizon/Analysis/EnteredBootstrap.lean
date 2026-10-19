import CauchyHorizon.Analysis.PrefixBootstrap

/-! First contact on a compact family of intervals with different entry times. -/

open Set

namespace CauchyHorizon

theorem continuous_entered_bootstrap {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {V : ℝ} {f : ℝ × K → ℝ} {entry : K → ℝ}
    (hf : Continuous f) (he : Continuous entry) (he0 : ∀ k, 0 ≤ entry k)
    (hstart : ∀ k, entry k ≤ V → f (entry k, k) < 0)
    (himprove : ∀ t ∈ Icc (0 : ℝ) V,
      (∀ q ∈ Icc (0 : ℝ) t, ∀ k, entry k ≤ q → f (q, k) ≤ 0) →
      ∀ k, entry k ≤ t → f (t, k) < 0) :
    ∀ t ∈ Icc (0 : ℝ) V, ∀ k, entry k ≤ t → f (t, k) < 0 := by
  intro t ht k hkt
  by_contra hbad
  let S := (Icc (0 : ℝ) V ×ˢ (univ : Set K)) ∩
    ({z | entry z.2 ≤ z.1} ∩ {z | 0 ≤ f z})
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_univ).inter_right
    ((isClosed_le (he.comp continuous_snd) continuous_fst).inter (isClosed_le continuous_const hf))
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn
    ⟨(t, k), ⟨⟨ht, mem_univ _⟩, hkt, not_lt.1 hbad⟩⟩ continuous_fst.continuousOn
  have hprefix : ∀ q ∈ Icc (0 : ℝ) z.1, ∀ j, entry j ≤ q → f (q, j) ≤ 0 := by
    intro q hq j hjq
    by_contra hqbad
    have hpos := lt_of_not_ge hqbad
    obtain ⟨w, hw, heq⟩ := intermediate_value_Icc hjq
      (hf.comp (continuous_id.prodMk continuous_const)).continuousOn
      (show 0 ∈ Icc (f (entry j, j)) (f (q, j)) from
        ⟨(hstart j (hjq.trans (hq.2.trans hz.1.1.2))).le, hpos.le⟩)
    have hwq : w < q := lt_of_le_of_ne hw.2 (by intro h; subst q; exact hpos.ne' heq)
    have hwS : (w, j) ∈ S :=
      ⟨⟨⟨(he0 j).trans hw.1, hw.2.trans (hq.2.trans hz.1.1.2)⟩, mem_univ _⟩, hw.1, heq.ge⟩
    exact (hwq.trans_le hq.2).not_ge (hmin hwS)
  exact (himprove z.1 hz.1.1 hprefix z.2 hz.2.1).not_ge hz.2.2

open Filter
open scoped Topology

theorem continuous_entered_bootstrap_of_tendsto {U V : ℝ} (hU : 0 < U)
    {f : ℝ × Icc 0 U → ℝ} {γ : ℝ → ℝ} (hf : Continuous f)
    (hγc : ContinuousOn γ (Ioc 0 U)) (hγa : StrictAntiOn γ (Ioc 0 U))
    (hγl : Tendsto γ (𝓝[>] (0 : ℝ)) atTop) (hγ0 : ∀ u ∈ Ioc 0 U, 0 ≤ γ u)
    (hstart : ∀ u : Icc 0 U, 0 < (u : ℝ) → γ u ≤ V → f (γ u, u) < 0)
    (himprove : ∀ t ∈ Icc (0 : ℝ) V,
      (∀ s ∈ Icc (0 : ℝ) t, ∀ u : Icc 0 U, 0 < (u : ℝ) → γ u ≤ s → f (s, u) ≤ 0) →
      ∀ u : Icc 0 U, 0 < (u : ℝ) → γ u ≤ t → f (t, u) < 0) :
    ∀ t ∈ Icc (0 : ℝ) V, ∀ u : Icc 0 U, 0 < (u : ℝ) → γ u ≤ t → f (t, u) < 0 := by
  have hnear : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 U :=
    (show ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u from self_mem_nhdsWithin).and
      ((eventually_lt_nhds hU).filter_mono nhdsWithin_le_nhds)
  obtain ⟨z, hz, hzV⟩ := (hnear.and (hγl.eventually (eventually_gt_atTop V))).exists
  have hzu (u : Icc 0 U) (hu : 0 < (u : ℝ)) {t : ℝ} (htV : t ≤ V) (hut : γ u ≤ t) : z ≤ (u : ℝ) := by
    by_contra hn
    have hh := hγa ⟨hu, u.property.2⟩ ⟨hz.1, hz.2.le⟩ (not_le.1 hn)
    exact (hzV.trans hh).not_ge (hut.trans htV)
  let embed : Icc z U → Icc 0 U := fun u => ⟨u, hz.1.le.trans u.property.1, u.property.2⟩
  have hembed : Continuous embed := continuous_subtype_val.subtype_mk _
  have he : Continuous (fun u : Icc z U => γ u) :=
    (hγc.mono (fun _ hu => ⟨hz.1.trans_le hu.1, hu.2⟩)).domRestrict
  have hh := continuous_entered_bootstrap
    (hf.comp (continuous_fst.prodMk (hembed.comp continuous_snd))) he
    (fun u => hγ0 u ⟨hz.1.trans_le u.property.1, u.property.2⟩)
    (fun u hu => hstart (embed u) (hz.1.trans_le u.property.1) hu)
    (fun t ht hpre u hut => himprove t ht (by
      intro s hs w hw hws
      exact hpre s hs ⟨w, hzu w hw (hs.2.trans ht.2) hws, w.property.2⟩ hws)
      (embed u) (hz.1.trans_le u.property.1) hut)
  intro t ht u hu hut
  exact hh t ht ⟨u, hzu u hu ht.2 hut, u.property.2⟩ hut

end CauchyHorizon
