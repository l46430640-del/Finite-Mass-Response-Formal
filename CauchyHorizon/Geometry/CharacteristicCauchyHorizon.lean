import CauchyHorizon.Geometry.CausalEndpoints
import CauchyHorizon.Geometry.LocalCauchyHorizon

/-! Dependence on the two characteristic initial sides in a spherical crossing spacetime. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

def characteristicInitialSides (vi U : ℝ) : Set SphericalSpacetime :=
  {p | (p.1.1 = vi ∧ 0 ≤ p.1.2 ∧ p.1.2 < U) ∨
    (vi ≤ p.1.1 ∧ p.1.1 < 0 ∧ p.1.2 = 0)}

def characteristicCrossingRegion (vm U va vb ua ub : ℝ) : Set SphericalSpacetime :=
  sphericalOpenRectangle vm 0 (-1) U ∪ sphericalOpenRectangle va vb ua ub

theorem exists_past_curve_before_characteristic_horizon {vm U va vb ua ub : ℝ}
    (hva : vm < va) (hua : 0 < ua) (huU : ub < U)
    (H R : SphericalSpacetime → ℝ) {p : SphericalSpacetime}
    (hp : p ∈ sphericalOpenRectangle va vb ua ub) (hp0 : p.1.1 < 0) :
    ∃ γ : ℝ → SphericalSpacetime,
      IsPastInextendibleCausalCurve (characteristicCrossingRegion vm U va vb ua ub) H R γ ∧
        γ 0 = p := by
  have hin (q : SphericalSpacetime) (hq : q ∈ sphericalOpenRectangle va vb ua ub)
      (hq0 : q.1.1 < 0) : q ∈ sphericalOpenRectangle vm 0 (-1) U :=
    ⟨⟨⟨hva.trans hq.1.1.1, hq0⟩, ⟨by linarith [hq.1.2.1], hq.1.2.2.trans huU⟩⟩, hq.2⟩
  obtain ⟨γ, hγ, hstart, hV⟩ := exists_past_radial_null_curve H R (hin p hp hp0)
  refine ⟨γ, ⟨hγ.1, (fun _ ht => Or.inl (hγ.2.1 ht)), hγ.2.2.1, hγ.2.2.2.1, ?_⟩, hstart⟩
  intro q hq hlim
  rcases hq with hleft | hright
  · exact hγ.2.2.2.2 q hleft hlim
  · have hvq : Tendsto (fun t => (γ t).1.1) atBot (𝓝 q.1.1) :=
      (continuous_fst.fst.tendsto q).comp hlim
    have hpv : Tendsto (fun t => (γ t).1.1) atBot (𝓝 p.1.1) := by
      simpa only [hV] using (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => p.1.1) atBot (𝓝 p.1.1))
    have he := tendsto_nhds_unique hpv hvq
    exact hγ.2.2.2.2 q (hin q hright (he ▸ hp0)) hlim

theorem mem_characteristic_future_domain {vi U : ℝ}
    {M : Set SphericalSpacetime} {H R : SphericalSpacetime → ℝ} {p : SphericalSpacetime}
    (hH : ∀ q ∈ M, 0 < H q) (hR : ∀ q ∈ M, 0 < R q)
    (hcH : ContinuousOn H M) (hcR : ContinuousOn R M)
    (hvi : vi < p.1.1) (hv0 : p.1.1 < 0) (hu0 : 0 < p.1.2) (huU : p.1.2 < U)
    (hbox : ((Icc vi p.1.1 ×ˢ Icc 0 p.1.2) ×ˢ (univ : Set UnitSphere)) ⊆ M) :
    p ∈ futureDomainOfDependence M H R (characteristicInitialSides vi U) := by
  have hpK : p ∈ ((Icc vi p.1.1 ×ˢ Icc 0 p.1.2) ×ˢ (univ : Set UnitSphere)) :=
    ⟨⟨⟨hvi.le, le_rfl⟩, ⟨hu0.le, le_rfl⟩⟩, mem_univ _⟩
  refine ⟨hbox hpK, ?_⟩
  intro γ hγ hstart
  by_contra hmiss
  have havoid : ∀ t ≤ 0, γ t ∉ characteristicInitialSides vi U := by
    intro t ht hh
    exact hmiss ⟨t, ht, hh⟩
  obtain ⟨hvm, hum⟩ := hγ.null_coordinates_monotone hH (fun q hq => (hR q hq).le)
  have hvup (t : ℝ) (ht : t ≤ 0) : (γ t).1.1 ≤ p.1.1 := by
    simpa only [hstart] using hvm ht (by simp) ht
  have huup (t : ℝ) (ht : t ≤ 0) : (γ t).1.2 ≤ p.1.2 := by
    simpa only [hstart] using hum ht (by simp) ht
  have hlower (t : ℝ) (ht : t ≤ 0) : 0 < min ((γ t).1.1 - vi) (γ t).1.2 := by
    by_contra hn
    have hf : ContinuousOn (fun s => min ((γ s).1.1 - vi) (γ s).1.2) (Icc t 0) :=
      ((hγ.1.fst.fst.sub continuousOn_const).inf hγ.1.fst.snd).mono
        (fun _ hs => hs.2)
    have hf0 : 0 < min ((γ 0).1.1 - vi) (γ 0).1.2 := by
      rw [hstart]
      exact lt_min (sub_pos.mpr hvi) hu0
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc ht hf ⟨le_of_not_gt hn, hf0.le⟩
    change min ((γ s).1.1 - vi) (γ s).1.2 = 0 at he
    apply havoid s hs.2
    rcases le_total ((γ s).1.1 - vi) (γ s).1.2 with hh | hh
    · rw [min_eq_left hh] at he
      exact Or.inl ⟨by linarith, by linarith, (huup s hs.2).trans_lt huU⟩
    · rw [min_eq_right hh] at he
      exact Or.inr ⟨by linarith, (hvup s hs.2).trans_lt hv0, he⟩
  apply hγ.not_trapped_in_compact_of_continuous hH hR
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_univ) hbox
    (hcH.mono hbox) (hcR.mono hbox)
  intro t ht
  have hh := lt_min_iff.mp (hlower t ht)
  exact ⟨⟨⟨(sub_pos.mp hh.1).le, hvup t ht⟩, ⟨hh.2.le, huup t ht⟩⟩, mem_univ _⟩

theorem characteristic_domain_regular_time_neg {vm vi U va vb ua ub : ℝ}
    (hvi : vi < 0) (H R : SphericalSpacetime → ℝ) {p : SphericalSpacetime}
    (hp : p ∈ futureDomainOfDependence (characteristicCrossingRegion vm U va vb ua ub)
      H R (characteristicInitialSides vi U)) : p.1.1 < 0 := by
  by_contra hn
  have hp0 : 0 ≤ p.1.1 := le_of_not_gt hn
  have hpN : p ∈ sphericalOpenRectangle va vb ua ub := by
    rcases hp.1 with hleft | hright
    · exact (not_lt_of_ge hp0 hleft.1.1.2).elim
    · exact hright
  obtain ⟨γ, hγ, hstart, hV⟩ := exists_past_radial_null_curve H R hpN
  have hγM : IsPastInextendibleCausalCurve
      (characteristicCrossingRegion vm U va vb ua ub) H R γ := by
    refine ⟨hγ.1, (fun _ ht => Or.inr (hγ.2.1 ht)), hγ.2.2.1, hγ.2.2.2.1, ?_⟩
    intro q hq hlim
    rcases hq with hleft | hright
    · have hvq : Tendsto (fun t => (γ t).1.1) atBot (𝓝 q.1.1) :=
        (continuous_fst.fst.tendsto q).comp hlim
      have hpv : Tendsto (fun t => (γ t).1.1) atBot (𝓝 p.1.1) := by
        simpa only [hV] using (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => p.1.1) atBot (𝓝 p.1.1))
      have he := tendsto_nhds_unique hpv hvq
      exact not_lt_of_ge hp0 (he ▸ hleft.1.1.2)
    · exact hγ.2.2.2.2 q hright hlim
  obtain ⟨t, _ht, hside⟩ := hp.2 γ hγM hstart
  rcases hside with hleft | hright
  · have he : p.1.1 = vi := (hV t).symm.trans hleft.1
    exact not_lt_of_ge hp0 (he ▸ hvi)
  · exact not_lt_of_ge hp0 (by simpa only [hV] using hright.2.1)

theorem characteristic_future_domain_on_crossing {vm vi U va vb ua ub : ℝ}
    {H R : SphericalSpacetime → ℝ} (hmi : vm < vi) (hia : vi < va) (ha : va < 0)
    (hu : 0 < ua) (huU : ub < U)
    (hH : ∀ p ∈ characteristicCrossingRegion vm U va vb ua ub, 0 < H p)
    (hR : ∀ p ∈ characteristicCrossingRegion vm U va vb ua ub, 0 < R p)
    (hcH : ContinuousOn H (characteristicCrossingRegion vm U va vb ua ub))
    (hcR : ContinuousOn R (characteristicCrossingRegion vm U va vb ua ub)) :
    sphericalOpenRectangle va vb ua ub ∩
      futureDomainOfDependence (characteristicCrossingRegion vm U va vb ua ub)
        H R (characteristicInitialSides vi U) =
      sphericalOpenRectangle va (min vb 0) ua ub := by
  ext p
  constructor
  · rintro ⟨hp, hd⟩
    exact ⟨⟨⟨hp.1.1.1, lt_min hp.1.1.2
      (characteristic_domain_regular_time_neg (hia.trans ha) H R hd)⟩, hp.1.2⟩, hp.2⟩
  · intro hp
    have hv0 : p.1.1 < 0 := hp.1.1.2.trans_le (min_le_right _ _)
    have hpu : 0 < p.1.2 := hu.trans hp.1.2.1
    have hpU : p.1.2 < U := hp.1.2.2.trans huU
    refine ⟨⟨⟨⟨hp.1.1.1, hp.1.1.2.trans_le (min_le_left _ _)⟩, hp.1.2⟩, hp.2⟩,
      mem_characteristic_future_domain hH hR hcH hcR (hia.trans hp.1.1.1) hv0 hpu hpU ?_⟩
    intro q hq
    exact Or.inl ⟨⟨⟨hmi.trans_le hq.1.1.1, hq.1.1.2.trans_lt hv0⟩,
      ⟨by linarith [hq.1.2.1], hq.1.2.2.trans_lt hpU⟩⟩, hq.2⟩

theorem TimelikeSegment.mono_region {M N : Set SphericalSpacetime}
    {H R : SphericalSpacetime → ℝ} {p q : SphericalSpacetime}
    (h : TimelikeSegment M H R p q) (hMN : M ⊆ N) : TimelikeSegment N H R p q := by
  obtain ⟨γ, hp, hq, hc, hm, hd, hv⟩ := h
  exact ⟨γ, hp, hq, hc, (fun _ ht => hMN (hm ht)), hd, hv⟩

theorem ChronologicalPrecedes.mono_region {M N : Set SphericalSpacetime}
    {H R : SphericalSpacetime → ℝ} {p q : SphericalSpacetime}
    (h : ChronologicalPrecedes M H R p q) (hMN : M ⊆ N) :
    ChronologicalPrecedes N H R p q :=
  Relation.TransGen.mono (fun _ _ hh => TimelikeSegment.mono_region hh hMN) p q h

theorem characteristic_cauchy_horizon_on_crossing {vm vi U va vb ua ub : ℝ}
    {H R : SphericalSpacetime → ℝ} (hmi : vm < vi) (hia : vi < va) (ha : va < 0)
    (hb : 0 < vb) (hu : 0 < ua) (hab : ua < ub) (huU : ub < U)
    (hH : ∀ p ∈ characteristicCrossingRegion vm U va vb ua ub, 0 < H p)
    (hR : ∀ p ∈ characteristicCrossingRegion vm U va vb ua ub, 0 < R p)
    (hcH : ContinuousOn H (characteristicCrossingRegion vm U va vb ua ub))
    (hcR : ContinuousOn R (characteristicCrossingRegion vm U va vb ua ub)) :
    sphericalOpenRectangle va vb ua ub ∩
      futureCauchyHorizon (characteristicCrossingRegion vm U va vb ua ub)
        H R (characteristicInitialSides vi U) = ({0} ×ˢ Ioo ua ub) ×ˢ univ := by
  let M := characteristicCrossingRegion vm U va vb ua ub
  let N := sphericalOpenRectangle va vb ua ub
  let S := sphericalOpenRectangle va 0 ua ub
  let D := futureDomainOfDependence M H R (characteristicInitialSides vi U)
  have hNM : N ⊆ M := fun _ hp => Or.inr hp
  have hDN : N ∩ D = S := by
    simpa only [min_eq_right hb.le] using
      characteristic_future_domain_on_crossing hmi hia ha hu huU hH hR hcH hcR
  have hSD : S ⊆ D := fun _ hp => ((Set.ext_iff.mp hDN _).mpr hp).2
  have hIpast : N ∩ chronologicalPast M H R D = S := by
    ext p
    constructor
    · rintro ⟨hp, _hpm, q, hq, htim⟩
      have hv : q.1.1 < 0 := characteristic_domain_regular_time_neg (hia.trans ha) H R hq
      exact ⟨⟨⟨hp.1.1.1, (htim.regular_time_lt hH (fun q hq => (hR q hq).le)).trans hv⟩,
        hp.1.2⟩, hp.2⟩
    · intro hp
      have hh : p ∈ chronologicalPast N H R S := by
        rw [sphericalRectangle_chronological_past hb
          (fun q hq => hH q (hNM hq)) (fun q hq => (hR q (hNM hq)).le)]
        exact hp
      obtain ⟨hpN, q, hq, htim⟩ := hh
      exact ⟨hpN, hNM hpN, q, hSD hq, htim.mono_region hNM⟩
  have hDclosed : closure D ⊆ {p : SphericalSpacetime | p.1.1 ≤ 0} := by
    apply closure_minimal
    · intro p hp
      exact (characteristic_domain_regular_time_neg (hia.trans ha) H R hp).le
    · exact isClosed_le (continuous_fst.fst) continuous_const
  have hSclosure : closure S = (Icc va 0 ×ˢ Icc ua ub) ×ˢ (univ : Set UnitSphere) := by
    simp only [S, sphericalOpenRectangle, closure_prod_eq, closure_Ioo ha.ne,
      closure_Ioo hab.ne, closure_univ]
  ext p
  constructor
  · rintro ⟨hpN, ⟨_hpM, hpcl⟩, hpnot⟩
    have hp0 := hDclosed hpcl
    have hpEq : p.1.1 = 0 := by
      by_contra he
      have hpS : p ∈ S := ⟨⟨⟨hpN.1.1.1, lt_of_le_of_ne hp0 he⟩, hpN.1.2⟩, hpN.2⟩
      exact hpnot (((Set.ext_iff.mp hIpast p).mpr hpS).2)
    exact ⟨⟨hpEq, hpN.1.2⟩, hpN.2⟩
  · rintro ⟨⟨hp0, hpu⟩, hps⟩
    have he : p.1.1 = 0 := hp0
    have hpN : p ∈ N := ⟨⟨⟨by simpa only [he] using ha,
      by simpa only [he] using hb⟩, hpu⟩, hps⟩
    have hpcl : p ∈ closure S := by
      rw [hSclosure]
      exact ⟨⟨⟨by simpa only [he] using ha.le, by simp only [he, le_refl]⟩,
        ⟨hpu.1.le, hpu.2.le⟩⟩, hps⟩
    refine ⟨hpN, ⟨hNM hpN, closure_mono hSD hpcl⟩, ?_⟩
    intro hbad
    have hpS := (Set.ext_iff.mp hIpast p).mp ⟨hpN, hbad⟩
    exact (ne_of_lt hpS.1.1.2) he

end CauchyHorizon
