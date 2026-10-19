import CauchyHorizon.Characteristic.CompactArrival

/-! The entered part of an actual row carries the compact chart and pre-entry budgets. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1200000 in
theorem exists_band_row_charts (B : Background) {s H dH A c : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧ R < r 0 ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ σ j D n N L E l C K : ℝ,
        0 < σ ∧ σ ≤ δ ∧ 0 < j ∧ 0 < D ∧ 0 < n ∧ 0 < N ∧
        0 ≤ L ∧ 0 ≤ E ∧ 0 < l ∧ 0 ≤ C ∧ 0 < K ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A → c ≤ B.outerRate * (1 - 1 / p.toReal) →
          ∃ arrival : ℝ → ℝ, ContinuousOn arrival (Ioo 0 σ) ∧ StrictAntiOn arrival (Ioo 0 σ) ∧
            Tendsto arrival (𝓝[>] (0 : ℝ)) atTop ∧
            (∀ u ∈ Ioo 0 σ, 0 < arrival u ∧ j ≤ u * Real.exp (B.outerRate * arrival u) ∧
              u * Real.exp (B.outerRate * arrival u) ≤ D) ∧
            (∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
              (hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x) (u : ℝ), u ∈ Ioo 0 σ →
              ∀ q : Icc 0 U, (q : ℝ) ≤ u → ∀ v : Icc 0 V, (v : ℝ) ≤ arrival u →
                Y ≤ x.1 q v 0 ∧
                |radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose q v| ≤
                    N * Real.exp (B.outerRate * v) ∧ |x.2.1 q v 1| ≤ E * Real.exp (-c * v)) ∧
            (∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
              (_hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x) (u : Icc 0 U) (v : Icc 0 V),
              (u : ℝ) ∈ Ioo 0 σ → x.1 u v 0 = Y → x.2.1 u v 0 < 0 → arrival u = v) ∧
            ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
              (hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x)
              (u : Icc 0 U) (b : Icc 0 V), 0 < (u : ℝ) → (u : ℝ) < σ → K ≤ b → arrival u ≤ b →
                ∃ (z : Icc 0 U) (hzu : z ≤ u) (T : C(Icc (z : ℝ) u, Icc 0 V)),
                  0 < (z : ℝ) ∧
                  let τ := fun t => T (projIcc (z : ℝ) u hzu t)
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                  τ z = b ∧
                  (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
                    (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) ∧
                  ∀ t ∈ Icc (z : ℝ) u,
                    let w := projIcc 0 U hU t
                    arrival u ≤ (τ t : ℝ) ∧ τ t ≤ b ∧ x.1 w (τ t) 0 = Y ∧
                    l ≤ -x.2.1 w (τ t) 0 ∧ -x.2.1 w (τ t) 0 ≤ L ∧
                    n ≤ t * (-ν w (τ t)) ∧ t * Real.exp (B.outerRate * τ t) ≤ D ∧
                    (∀ q ≤ w, ∀ v ≤ τ t, Y ≤ x.1 q v 0 ∧ |ν q v| ≤ N * Real.exp (B.outerRate * v) ∧
                      |x.2.1 q v 1| ≤ E * Real.exp (-c * v)) ∧
                    |(-Real.exp (x.1 w (τ t) 2) / (4 * ν w (τ t))) - 1| +
                      |massField B.charge B.cosmological x.1 x.2.1 ν hx.choose w (τ t) - B.mass| ≤
                        C * Real.exp (-(min B.outerRate (2 * c)) * τ t) ∧ (τ t : ℝ) = arrival t := by
  dsimp only
  obtain ⟨δ, R, hδ, hδr, hR, hRr, hsolve⟩ :=
    B.exists_band_matching hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, hRr, ?_⟩
  intro Y hY hYR
  obtain ⟨ε, j, D, n, N, L, E, l, σ, C, K,
    hε, hεδ, hj, hD, hn, hN, hL, hE, hl, hσ, hσε, hC, hK, hglobal⟩ := hsolve Y hY hYR
  have hσε' : σ < ε := hσε.trans (half_lt_self hε)
  refine ⟨σ, j, D, n, N, L, E, l, C, K,
    hσ, hσε'.le.trans hεδ, hj, hD, hn, hN, hL, hE, hl, hC, hK, ?_⟩
  intro p hp f hf hfn hcb
  obtain ⟨arrival, g, hac, haa, hal, _htime, hright, _hleft, hpre, hidentify, hmatch⟩ := hglobal p hp f hf hfn hcb
  have hsub : Ioo 0 σ ⊆ Ioo 0 ε := Ioo_subset_Ioo le_rfl hσε'.le
  refine ⟨arrival, hac.mono hsub, haa.mono hsub, hal, fun u hu => ?_,
    fun {U V} hU hV hUR hfU {x} hx u hu => hpre hU hV hUR hfU hx u (hsub hu),
    fun {U V} hU hV hUR hfU {x} hx u v hu => hidentify hU hV hUR hfU hx u v (hsub hu), ?_⟩
  · have hh := hmatch u ⟨hu.1, hu.2.trans hσε'⟩
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
  · intro U V hU hV hUR hfU x hx u b hu huσ hKb hub
    obtain ⟨hgb, hgbt⟩ := hright b hKb
    have huε : (u : ℝ) ∈ Ioo 0 ε := ⟨hu, huσ.trans hσε'⟩
    have hzε : g b ∈ Ioo 0 ε := ⟨hgb.1, hgb.2.trans hσε'⟩
    have hzu : g b ≤ u := by
      by_contra hnot
      have hh := haa huε hzε (not_le.1 hnot)
      rw [hgbt] at hh
      exact (not_lt_of_ge hub) hh
    let z : Icc 0 U := ⟨g b, hgb.1.le, hzu.trans u.property.2⟩
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
    let slope := fun t => -ν (projIcc 0 U hU t) (projIcc 0 V hV (arrival t)) /
      x.2.1 (projIcc 0 U hU t) (projIcc 0 V hV (arrival t)) 0
    have hmem (t : ℝ) (ht : t ∈ Icc (z : ℝ) u) : t ∈ Ioo 0 ε :=
      ⟨hgb.1.trans_le ht.1, ht.2.trans_lt huε.2⟩
    have htime (t : ℝ) (ht : t ∈ Icc (z : ℝ) u) : arrival t ∈ Icc 0 V := by
      refine ⟨(hmatch t (hmem t ht)).1.le, ?_⟩
      exact (haa.antitoneOn hzε (hmem t ht) ht.1).trans (hgbt.trans_le b.property.2)
    have hd (t : ℝ) (ht : t ∈ Ioo (z : ℝ) u) : HasDerivAt arrival (slope t) t := by
      have htU : t ∈ Icc 0 U := ⟨hgb.1.le.trans ht.1.le, ht.2.le.trans u.property.2⟩
      have htV := htime t ⟨ht.1.le, ht.2.le⟩
      have hh := (hmatch t (hmem t ⟨ht.1.le, ht.2.le⟩)).2.2.2 hU hV hUR hfU hx htU htV
      simpa only [slope, projIcc_of_mem hU htU, projIcc_of_mem hV htV] using hh.2.2.2.2.2.1.hasDerivAt
    obtain ⟨T, hval, hTb, hdT, hbound⟩ := exists_compact_arrival_chart hgb.1 huε.2 hzu hac haa
      (fun t ht => (hmatch t ht).1) hd b hgbt
    have htau (t : ℝ) (ht : t ∈ Icc (z : ℝ) u) :
        T (projIcc (z : ℝ) u hzu t) = projIcc 0 V hV (arrival t) := by
      apply Subtype.ext
      rw [hval, projIcc_of_mem hzu ht, projIcc_of_mem hV (htime t ht)]
    refine ⟨z, hzu, T, hgb.1, hTb, ?_, ?_⟩
    · intro t ht
      have hh := hdT t ht
      dsimp only [slope] at hh
      rwa [← htau t ⟨ht.1.le, ht.2.le⟩] at hh
    · intro t ht
      have htU : t ∈ Icc 0 U := ⟨hgb.1.le.trans ht.1, ht.2.trans u.property.2⟩
      have htV := htime t ht
      have hh := (hmatch t (hmem t ht)).2.2.2 hU hV hUR hfU hx htU htV
      refine ⟨(hbound t ht).1, (hbound t ht).2, ?_⟩
      rw [htau t ht, projIcc_of_mem hU htU, projIcc_of_mem hV htV]
      exact ⟨hh.1, hh.2.2.2.1, hh.2.2.2.2.1, hh.2.2.1,
        (hmatch t (hmem t ht)).2.2.1, hh.2.2.2.2.2.2.1,
        hh.2.2.2.2.2.2.2 (ht.2.trans huσ.le), rfl⟩

end CauchyHorizon.Background
