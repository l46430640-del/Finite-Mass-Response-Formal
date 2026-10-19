import CauchyHorizon.Characteristic.CompactArrival
import CauchyHorizon.Analysis.ArrivalInverse

/-! A compact gamma row uses the same inverse radius curve and its continuous Jacobian. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

def RadiationGammaCharts {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (g : ℝ → ℝ) (T α η C Y : ℝ) : Prop :=
  ∀ (u : Icc 0 U) (b : Icc 0 V), T < (b : ℝ) / α → g ((b : ℝ) / α) ≤ u →
    ∃ (z : Icc 0 U) (hzu : z ≤ u)
      (Q : C(Icc (z : ℝ) u, Icc 0 V)) (J : C(Icc (z : ℝ) u, ℝ)),
      (z : ℝ) = g ((b : ℝ) / α) ∧ 0 < (z : ℝ) ∧
      let τ := fun t => Q (projIcc (z : ℝ) u hzu t)
      let j := fun t => J (projIcc (z : ℝ) u hzu t)
      τ z = b ∧
      (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ)) (-j t) t) ∧
      ∀ t ∈ Icc (z : ℝ) u,
        T < (τ t : ℝ) / α ∧ g ((τ t : ℝ) / α) = t ∧
        x.1 (projIcc 0 U hU t) (projIcc 0 V hV ((τ t : ℝ) / α)) 0 = Y ∧
        τ t ≤ b ∧ 0 < j t ∧ α / (C * t) ≤ j t ∧ j t ≤ α / (η * t)

theorem exists_radiation_gamma_chart {U V T α η C Y : ℝ} {g : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hT : 0 ≤ T) (hα : 1 ≤ α) (hη : 0 < η) (hC : 0 < C)
    (hc : ContinuousOn g (Ici T)) (ha : StrictAntiOn g (Ici T)) (hl : Tendsto g atTop (𝓝 0))
    (hdc : ContinuousOn (deriv g) (Ici T)) (hstart : U < g T)
    (hp : ∀ t ∈ Ici T, 0 < g t ∧ DifferentiableAt ℝ g t ∧
      η ≤ -deriv g t / g t ∧ -deriv g t / g t ≤ C)
    (x : WaveState U V)
    (hlevel : ∀ v : Icc 0 V, T ≤ v → g v ≤ U → x.1 (projIcc 0 U hU (g v)) v 0 = Y) :
    RadiationGammaCharts hU hV x g T α η C Y := by
  intro u b hb hgu
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hd (t : ℝ) (ht : t ∈ Ici T) : DifferentiableAt ℝ g t ∧ deriv g t < 0 := by
    have hh := (mul_pos hη (hp t ht).1).trans_le ((le_div_iff₀ (hp t ht).1).1 (hp t ht).2.2.1)
    exact ⟨(hp t ht).2.1, neg_pos.1 hh⟩
  obtain ⟨v, hvc, _hvl, hv, hleft⟩ := exists_arrival_inverse_closed hc ha hl
    (fun t ht => (hp t ht).1) hd
  have hva : StrictAntiOn v (Ioo 0 (g T)) := by
    intro q hq w hw hqw
    by_contra hn
    have hh := ha.antitoneOn (hv q hq).1.le (hv w hw).1.le (not_lt.1 hn)
    rw [(hv q hq).2.1, (hv w hw).2.1] at hh
    exact (not_le_of_gt hqw) hh
  let z : Icc 0 U := ⟨g ((b : ℝ) / α), (hp _ hb.le).1.le, hgu.trans u.property.2⟩
  have hz : 0 < (z : ℝ) := (hp _ hb.le).1
  have hzu : z ≤ u := hgu
  have hzuR : (z : ℝ) ≤ (u : ℝ) := hzu
  have humem : (u : ℝ) < g T := u.property.2.trans_lt hstart
  have hsub : Icc (z : ℝ) u ⊆ Ioo 0 (g T) := fun _ ht =>
    ⟨hz.trans_le ht.1, ht.2.trans_lt humem⟩
  have hpos (q : ℝ) (hq : q ∈ Ioo 0 (g T)) : 0 < α * v q :=
    mul_pos hα0 (hT.trans_lt (hv q hq).1)
  have hγz : α * v z = b := by
    change α * v (g ((b : ℝ) / α)) = b
    rw [hleft _ hb]
    field_simp
  obtain ⟨Q, hQ, hQz, hQd, hQr⟩ := exists_compact_arrival_chart hz humem hzu
    (hvc.const_mul α) (fun q hq w hw hqw => mul_lt_mul_of_pos_left (hva hq hw hqw) hα0)
    hpos (fun q hq => ((hv q (hsub ⟨hq.1.le, hq.2.le⟩)).2.2.const_mul α)) b hγz
  have hvcc : Continuous (fun q : Icc (z : ℝ) u => v q) :=
    continuousOn_iff_continuous_domRestrict.1 (hvc.mono hsub)
  have hdcc : Continuous (fun q : Icc (z : ℝ) u => deriv g (v q)) :=
    hdc.comp_continuous hvcc (fun q => (hv q (hsub q.property)).1.le)
  let J : C(Icc (z : ℝ) u, ℝ) := ⟨fun q => -(α * (deriv g (v q))⁻¹),
    ((hdcc.inv₀ (fun q => (hd _ (hv q (hsub q.property)).1.le).2.ne)).const_mul α).neg⟩
  refine ⟨z, hzu, Q, J, rfl, hz, hQz, ?_, ?_⟩
  · intro t ht
    simpa only [J, ContinuousMap.coe_mk, projIcc_of_mem hzuR ⟨ht.1.le, ht.2.le⟩, neg_neg]
      using hQd t ht
  intro t ht
  have hvt := hv t (hsub ht)
  have hτ : (Q (projIcc (z : ℝ) u hzu t) : ℝ) = α * v t := by
    rw [hQ, projIcc_of_mem hzuR ht]
  have hbase : (Q (projIcc (z : ℝ) u hzu t) : ℝ) / α = v t := by
    rw [hτ]
    field_simp
  have htv : v t ∈ Icc 0 V := by
    refine ⟨(hT.trans_lt hvt.1).le, ?_⟩
    have hh : v t ≤ α * v t := by nlinarith only [hα, hT.trans_lt hvt.1]
    exact (hh.trans (hτ ▸ (hQr t ht).2)).trans b.property.2
  have htu : t ∈ Icc 0 U := ⟨(hsub ht).1.le, ht.2.trans u.property.2⟩
  have hrad := hlevel ⟨v t, htv⟩ hvt.1.le (hvt.2.1.trans_le htu.2)
  have hJac := arrival_inverse_jacobian_bounds (hsub ht).1 hα0.le hη hvt.2.1 hvt.2.2
    (hp _ hvt.1.le).2.2.1 (hp _ hvt.1.le).2.2.2
  rw [(hvt.2.2.const_mul α).deriv] at hJac
  have hJval : J (projIcc (z : ℝ) u hzu t) = -(α * (deriv g (v t))⁻¹) := by
    simp only [J, ContinuousMap.coe_mk, projIcc_of_mem hzuR ht]
  refine ⟨by rw [hbase]; exact hvt.1, by rw [hbase]; exact hvt.2.1,
    ?_, (hQr t ht).2, ?_, ?_, ?_⟩
  · rw [hbase, projIcc_of_mem hV htv]
    simpa only [hvt.2.1] using hrad
  · change 0 < J (projIcc (z : ℝ) u hzu t)
    rw [hJval]
    exact (div_pos hα0 (mul_pos hC (hsub ht).1)).trans_le hJac.1
  · change α / (C * t) ≤ J (projIcc (z : ℝ) u hzu t)
    rw [hJval]; exact hJac.1
  · change J (projIcc (z : ℝ) u hzu t) ≤ α / (η * t)
    rw [hJval]; exact hJac.2

end CauchyHorizon
