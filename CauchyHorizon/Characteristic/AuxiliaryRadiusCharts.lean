import CauchyHorizon.Characteristic.BandRow
import CauchyHorizon.Characteristic.NestedRadiusSections
import CauchyHorizon.Analysis.ArrivalInverse

/-! Auxiliary radius charts inside the fixed early region of an actual common family. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon

def AuxiliaryRadiationCharts (B : Background) {U V : ℝ} (hU : 0 ≤ U)
    (x : WaveState U V) (ν : C(Icc 0 U, C(Icc 0 V, ℝ)))
    (g : ℝ → ℝ) (T₀ β Y L S : ℝ) : Prop :=
  ∀ b : Icc 0 V, S ≤ b →
    g ((b : ℝ) / (1 + β)) ∈ Ioo 0 U ∧
    let w := projIcc 0 U hU (g ((b : ℝ) / (1 + β)))
    ∃ z : Icc 0 U, 0 < (z : ℝ) ∧ z ≤ w ∧
      ∀ (u : Icc 0 U) (hzu : z ≤ u), u ≤ w →
      ∃ Q : C(Icc (z : ℝ) u, Icc 0 V),
        let τ := fun t => Q (projIcc (z : ℝ) u hzu t)
        τ z = b ∧
        (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
          (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) ∧
        ∀ t ∈ Icc (z : ℝ) u,
          let q := projIcc 0 U hU t
          x.1 q (τ t) 0 = Y ∧ ν q (τ t) < 0 ∧
            Real.exp (-1) * (-B.F Y) / B.outerRate ≤ t * (-ν q (τ t)) ∧
            t * (-ν q (τ t)) ≤ Real.exp 1 * (-B.F Y) / B.outerRate ∧
            0 < -x.2.1 q (τ t) 0 ∧ -x.2.1 q (τ t) 0 ≤ L * (Y - B.inner) ∧
            (∃ a : ℝ, T₀ < a ∧ (b : ℝ) / (1 + β) ≤ a ∧ g a = t ∧
              a < τ t ∧ τ t ≤ b ∧ (τ t : ℝ) ≤ (1 + β) * a) ∧
            ∀ a' b' : Icc 0 V, τ t ≤ a' → a' ≤ b' → b' ≤ b →
              B.inner / 2 ≤ x.1 q b' 0 ∧
              |ν q b'| ≤ (2 * Real.exp 2) * (-ν q a') *
                Real.exp (-2 * B.innerRate * ((b' : ℝ) - a')) ∧
              |x.2.1 q b' 0| ≤ (Real.exp (2 + 1 / 16) * (-x.2.1 q a' 0)) *
                Real.exp (-2 * B.innerRate * ((b' : ℝ) - a'))

namespace Background

set_option maxHeartbeats 2400000 in
theorem exists_auxiliary_radius_charts (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R L : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧ 0 < L ∧
      ∀ Y Z β U T₀ D : ℝ, B.inner < Y → Y < Z → Z ≤ R → 0 < β → ∀ hU : 0 < U, 0 ≤ T₀ →
        ∃ S : ℝ, 0 < S ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
            MemLp f p (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (hUR : U < r 0) (hfU : MemLp f p (volume.restrict (Icc 0 U)))
              (X : (V : Ici (0 : ℝ)) → WaveState U V)
              (hX : ∀ V : Ici (0 : ℝ), IsWaveIntegral hU.le V.property B.charge B.cosmological
                (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) (X V)) (g : ℝ → ℝ),
              ContinuousOn g (Ici T₀) → StrictAntiOn g (Ici T₀) → Tendsto g atTop (𝓝 0) → U < g T₀ →
              (∀ t ∈ Ici T₀, 0 < g t ∧ DifferentiableAt ℝ g t ∧ deriv g t < 0 ∧
                g t * Real.exp (B.outerRate * t) ≤ D) →
              (∀ (V : Ici (0 : ℝ)) t, T₀ ≤ t → g t ≤ U → t ≤ V →
                (X V).1 (projIcc 0 U hU.le (g t)) (projIcc 0 (V : ℝ) V.property t) 0 = Z) →
              ∀ (V : Ici (0 : ℝ)) (b : Icc 0 (V : ℝ)), S ≤ b →
                g ((b : ℝ) / (1 + β)) ∈ Ioo 0 U ∧
                let w := projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))
                ∃ z : Icc 0 U, 0 < (z : ℝ) ∧ z ≤ w ∧
                  ∀ (u : Icc 0 U) (hzu : z ≤ u), u ≤ w →
                  ∃ Q : C(Icc (z : ℝ) u, Icc 0 (V : ℝ)),
                  let τ := fun t => Q (projIcc (z : ℝ) u hzu t)
                  let ν := radialNuField V.property B.charge B.cosmological
                    (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) (X V).1 (hX V).choose
                  τ z = b ∧
                  (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
                    (-ν (projIcc 0 U hU.le t) (τ t) /
                      (X V).2.1 (projIcc 0 U hU.le t) (τ t) 0) t) ∧
                  ∀ t ∈ Icc (z : ℝ) u,
                    let q := projIcc 0 U hU.le t
                    (X V).1 q (τ t) 0 = Y ∧ ν q (τ t) < 0 ∧
                      Real.exp (-1) * (-B.F Y) / B.outerRate ≤ t * (-ν q (τ t)) ∧
                      t * (-ν q (τ t)) ≤ Real.exp 1 * (-B.F Y) / B.outerRate ∧
                      0 < -(X V).2.1 q (τ t) 0 ∧ -(X V).2.1 q (τ t) 0 ≤ L * (Y - B.inner) ∧
                      ∃ a : ℝ, T₀ < a ∧ (b : ℝ) / (1 + β) ≤ a ∧ g a = t ∧
                        a < τ t ∧ τ t ≤ b ∧ (τ t : ℝ) ≤ (1 + β) * a := by
  classical
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (half_le_self hs.le)
  obtain ⟨δb, Rb, hδb, _hδbr, hRb, _hRbr, hband⟩ := B.exists_band_row_charts
    hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δa, Ra, L, _hδa, _hδar, hRa, hL, hsections⟩ := B.exists_nested_radius_sections
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨max δb δa, min Rb Ra, L, hδb.trans_le (le_max_left _ _),
    ⟨lt_min hRb.1 hRa.1, (min_le_left _ _).trans_lt hRb.2⟩, hL, ?_⟩
  intro Y Z β U T₀ D hY hYZ hZR hβ hU hT₀
  obtain ⟨σ, _j, _Db, _n, _N, _Lb, _E, _l, _C, K,
    hσ, _hσδ, _hj, _hDb, _hn, _hN, _hLb, _hE, _hl, _hC, _hK, hsolve⟩ :=
    hband Y hY ((hYZ.le.trans hZR).trans (min_le_left _ _))
  obtain ⟨Te, hTe, hentry⟩ := hsections Y Z β U hY hYZ (hZR.trans (min_le_right _ _)) hβ hU
  have hlim : Tendsto (fun t : ℝ => D * Real.exp (-B.outerRate * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (neg_neg_of_pos B.outerRate_pos))).const_mul D
  obtain ⟨Sw, hSw⟩ := eventually_atTop.1 (hlim.eventually_lt_const (lt_min hU hσ))
  let Ht := max 0 (max T₀ (max Te (max Sw K))) + 1
  have hHt : 0 < Ht := by dsimp only [Ht]; linarith only [le_max_left 0 (max T₀ (max Te (max Sw K)))]
  have hTt : T₀ < Ht := by dsimp only [Ht]; linarith only [le_max_left T₀ (max Te (max Sw K)), le_max_right 0 (max T₀ (max Te (max Sw K)))]
  have htet : Te ≤ Ht := by dsimp only [Ht]; linarith only [le_max_left Te (max Sw K), le_max_right T₀ (max Te (max Sw K)), le_max_right 0 (max T₀ (max Te (max Sw K)))]
  have hswt : Sw ≤ Ht := by dsimp only [Ht]; linarith only [le_max_left Sw K, le_max_right Te (max Sw K), le_max_right T₀ (max Te (max Sw K)), le_max_right 0 (max T₀ (max Te (max Sw K)))]
  have hKt : K ≤ Ht := by dsimp only [Ht]; linarith only [le_max_right Sw K, le_max_right Te (max Sw K), le_max_right T₀ (max Te (max Sw K)), le_max_right 0 (max T₀ (max Te (max Sw K)))]
  have hα : 0 < 1 + β := by linarith only [hβ]
  refine ⟨(1 + β) * Ht, mul_pos hα hHt, ?_⟩
  intro p hp f hf hfn hUR hfU X hX g hgc hga hgl hstart hgp hlevel
  have hcp : c ≤ B.outerRate * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 B.outerRate_pos.le
    have hcHalf : c ≤ B.outerRate / 2 := min_le_right _ _
    linarith only [hh, hcHalf, B.outerRate_pos]
  obtain ⟨arrival, _hac, haa, _hal, _hscale, _hpre, hidentify, hrow⟩ := hsolve p hp f
    (hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_left δb δa)) le_rfl))
    ((scalar_prefix_norm_le (le_max_left δb δa) hf).trans hfn) hcp
  obtain ⟨ψ, _hψc, hψb, hψp⟩ := hentry p hp f
    (hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_right δb δa)) le_rfl))
    ((scalar_prefix_norm_le (le_max_right δb δa) hf).trans hfn)
  obtain ⟨a, _hac, _hal, ha, hai⟩ := exists_arrival_inverse_closed hgc hga hgl
    (fun t ht => (hgp t ht).1) (fun t ht => ⟨(hgp t ht).2.1, (hgp t ht).2.2.1⟩)
  -- Identify the entry in a containing time prefix, then use it on the original row.
  have hentryTime (q : Icc 0 U) (hq : 0 < (q : ℝ)) (hqσ : (q : ℝ) < σ) (hta : Te ≤ a q) :
      arrival q = ψ (a q) := by
    have haq := ha q ⟨hq, q.property.2.trans_lt hstart⟩
    have hψ := hψb (a q) hta
    let V : Ici (0 : ℝ) := ⟨ψ (a q), (hT₀.trans_lt (haq.1.trans hψ.1)).le⟩
    have hrad := hlevel V (a q) haq.1.le (haq.2.1.trans_le q.property.2) hψ.1.le
    rw [haq.2.1, projIcc_of_mem hU.le q.property] at hrad
    have hh := hψp U V hU.le V.property hUR hfU (X V) (hX V) le_rfl (a q) hta le_rfl q hrad
    have htop : ψ (a q) ∈ Icc 0 (V : ℝ) := ⟨V.property, le_rfl⟩
    simp only [projIcc_of_mem V.property htop] at hh
    exact hidentify hU.le V.property hUR hfU (hX V) q ⟨ψ (a q), htop⟩ ⟨hq, hqσ⟩ hh.1
      (neg_pos.1 (hh.2 (hX V).choose).2.2.1)
  intro V b hSb
  have htb : Ht ≤ (b : ℝ) / (1 + β) := (le_div_iff₀ hα).2 (by simpa only [mul_comm] using hSb)
  have hbase : T₀ < (b : ℝ) / (1 + β) := hTt.trans_le htb
  have hbb : (b : ℝ) / (1 + β) ≤ b := by
    apply (div_le_iff₀ hα).2
    nlinarith only [b.property.1, hβ]
  have hgb : g ((b : ℝ) / (1 + β)) < min U σ := by
    have hh := (le_div_iff₀ (Real.exp_pos _)).2 (hgp _ hbase.le).2.2.2
    have hh' : g ((b : ℝ) / (1 + β)) ≤ D * Real.exp (-B.outerRate * ((b : ℝ) / (1 + β))) := by
      simpa only [Real.exp_neg, div_eq_mul_inv, neg_mul] using hh
    exact hh'.trans_lt (hSw _ (hswt.trans htb))
  have hgw : g ((b : ℝ) / (1 + β)) ∈ Ioo 0 U := ⟨(hgp _ hbase.le).1, hgb.trans_le (min_le_left _ _)⟩
  let w := projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))
  have hw : (w : ℝ) = g ((b : ℝ) / (1 + β)) := by
    simp only [w, projIcc_of_mem hU.le ⟨hgw.1.le, hgw.2.le⟩]
  have hw0 : 0 < (w : ℝ) := hw ▸ hgw.1
  have hwσ : (w : ℝ) < σ := by rw [hw]; exact hgb.trans_le (min_le_right _ _)
  have haw : a w = (b : ℝ) / (1 + β) := by rw [hw]; exact hai _ hbase
  have hwb : arrival w ≤ b := by
    rw [hentryTime w hw0 hwσ (by rw [haw]; exact htet.trans htb), haw]
    exact (hψb _ (htet.trans htb)).2.trans_eq (by field_simp)
  obtain ⟨z, hzw, Q₀, hz, hQ₀z, _hQ₀d, hQ₀p⟩ := hrow hU.le V.property hUR hfU (hX V) w b hw0 hwσ
    (hKt.trans (htb.trans hbb)) hwb
  have haz : arrival z = b := by
    have hh := hQ₀p z (left_mem_Icc.2 (show (z : ℝ) ≤ w from hzw))
    rw [hQ₀z] at hh
    exact hh.2.2.2.2.2.2.2.2.2.symm
  have hzσ : (z : ℝ) < σ := (show (z : ℝ) ≤ w from hzw).trans_lt hwσ
  refine ⟨hgw, z, hz, hzw, ?_⟩
  intro u hzu huw
  have hu0 : 0 < (u : ℝ) := hz.trans_le hzu
  have huσ : (u : ℝ) < σ := (show (u : ℝ) ≤ w from huw).trans_lt hwσ
  have hub : arrival u ≤ b := (haa.antitoneOn ⟨hz, hzσ⟩ ⟨hu0, huσ⟩ hzu).trans_eq haz
  obtain ⟨z', hz'u, Q, hz', hQz', hQd, hQp⟩ := hrow hU.le V.property hUR hfU (hX V) u b hu0 huσ
    (hKt.trans (htb.trans hbb)) hub
  have heq : z' = z := by
    have hh := hQp z' (left_mem_Icc.2 (show (z' : ℝ) ≤ u from hz'u))
    rw [hQz'] at hh
    exact Subtype.ext (haa.injOn ⟨hz', (show (z' : ℝ) ≤ u from hz'u).trans_lt huσ⟩ ⟨hz, hzσ⟩
      (hh.2.2.2.2.2.2.2.2.2.symm.trans haz.symm))
  subst z'
  refine ⟨Q, hQz', hQd, ?_⟩
  let τ := fun t => Q (projIcc (z : ℝ) u hzu t)
  intro t ht
  have htw : t ≤ w := ht.2.trans huw
  have htU : t ∈ Icc 0 U := ⟨hz.le.trans ht.1, ht.2.trans u.property.2⟩
  let q := projIcc 0 U hU.le t
  have hqt : (q : ℝ) = t := by simp only [q, projIcc_of_mem hU.le htU]
  have ht0 : 0 < t := hz.trans_le ht.1
  have htσ : t < σ := htw.trans_lt hwσ
  have hat := ha t ⟨ht0, htU.2.trans_lt hstart⟩
  have hba : (b : ℝ) / (1 + β) ≤ a t := by
    by_contra hn
    have hh := hga hat.1.le hbase.le (not_le.1 hn)
    rw [hat.2.1] at hh
    exact (not_lt_of_ge (htw.trans_eq hw)) hh
  have hta : Te ≤ a t := htet.trans (htb.trans hba)
  have heq : arrival t = ψ (a t) := by
    simpa only [hqt] using hentryTime q (by rw [hqt]; exact ht0) (by rw [hqt]; exact htσ)
      (by rw [hqt]; exact hta)
  obtain ⟨_hlo, hτb, hrad, _hll, _hlh, _hn, _hD, _hpre, _herr, hτa⟩ := hQp t ht
  have hτψ : ψ (a t) = (τ t : ℝ) := heq.symm.trans hτa.symm
  have haV : a t ≤ V := (hψb _ hta).1.le.trans (hτψ.trans_le ((show (τ t : ℝ) ≤ b from hτb).trans b.property.2))
  have hbaseRad := hlevel V (a t) hat.1.le (hat.2.1.trans_le htU.2) haV
  rw [hat.2.1] at hbaseRad
  have hpnt := hψp U V hU.le V.property hUR hfU (X V) (hX V) le_rfl (a t) hta
    (hτψ.trans_le ((show (τ t : ℝ) ≤ b from hτb).trans b.property.2)) q hbaseRad
  rw [hτψ, projIcc_of_mem V.property (τ t).property] at hpnt
  have hcoeff := hpnt.2 (hX V).choose
  rw [hqt] at hcoeff
  refine ⟨hrad, ((hX V).interior_gauge hU.le V.property hUR hc hi hrc hr0 hφ hrd hp hfU q (τ t)).2.2.1,
    hcoeff.1, hcoeff.2.1, hcoeff.2.2.1, hcoeff.2.2.2, a t, hat.1, hba, hat.2.1, ?_, hτb, ?_⟩
  · exact (hψb _ hta).1.trans_eq hτψ
  · exact hτψ ▸ (hψb _ hta).2

end Background

end CauchyHorizon
