import CauchyHorizon.Characteristic.BandArrival

/-! Uniform arrival data and their entire pre-entry history on every physical overlap. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1200000 in
theorem exists_band_matching (B : Background) {s H dH A c : ℝ}
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
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ ε j D n N L E l σ C K : ℝ,
        0 < ε ∧ ε ≤ δ ∧ 0 < j ∧ 0 < D ∧ 0 < n ∧ 0 < N ∧
        0 ≤ L ∧ 0 ≤ E ∧ 0 < l ∧ 0 < σ ∧ σ < ε / 2 ∧ 0 ≤ C ∧ 0 < K ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A → c ≤ B.outerRate * (1 - 1 / p.toReal) →
          ∃ arrival g : ℝ → ℝ, ContinuousOn arrival (Ioo 0 ε) ∧ StrictAntiOn arrival (Ioo 0 ε) ∧
            Tendsto arrival (𝓝[>] (0 : ℝ)) atTop ∧ arrival σ < K ∧
            (∀ t ∈ Ici K, g t ∈ Ioo 0 σ ∧ arrival (g t) = t) ∧
            (∀ u ∈ Ioo 0 (ε / 2), g (arrival u) = u) ∧
            (∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
              (hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x) (u : ℝ), u ∈ Ioo 0 ε →
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
              (u : ℝ) ∈ Ioo 0 ε → x.1 u v 0 = Y → x.2.1 u v 0 < 0 → arrival u = v) ∧
            ∀ u ∈ Ioo 0 ε, 0 < arrival u ∧ j ≤ u * Real.exp (B.outerRate * arrival u) ∧
              u * Real.exp (B.outerRate * arrival u) ≤ D ∧
              ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
                (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x),
                ∀ (huU : u ∈ Icc 0 U) (htV : arrival u ∈ Icc 0 V),
                  let w : Icc 0 U := ⟨u, huU⟩
                  let t : Icc 0 V := ⟨arrival u, htV⟩
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                  x.1 w t 0 = Y ∧ x.2.1 w t 0 < 0 ∧ n ≤ u * (-ν w t) ∧
                  l ≤ -x.2.1 w t 0 ∧ -x.2.1 w t 0 ≤ L ∧
                  HasStrictDerivAt arrival (-ν w t / x.2.1 w t 0) u ∧
                  (∀ q ≤ w, ∀ v ≤ t, Y ≤ x.1 q v 0 ∧ |ν q v| ≤ N * Real.exp (B.outerRate * v) ∧
                    |x.2.1 q v 1| ≤ E * Real.exp (-c * v)) ∧
                  (u ≤ σ → |(-Real.exp (x.1 w t 2) / (4 * ν w t)) - 1| +
                    |massField B.charge B.cosmological x.1 x.2.1 ν hx.choose w t - B.mass| ≤
                      C * Real.exp (-(min B.outerRate (2 * c)) * arrival u)) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, hδr, hR, hRr, hsolve⟩ :=
    B.exists_band_arrival hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, hRr, ?_⟩
  intro Y hY hYR
  obtain ⟨ε, j, D, _b, _C, K, n, N, L, E, l, σ, Cerr,
    hε, hεδ, hj, hD, _hb, _hC, hK, hn, hN, hL, hE, hl, hσ, hσε, hCerr, hglobal⟩ := hsolve Y hY hYR
  refine ⟨ε, j, D, n * j, N, L, E, l, σ, Cerr, K,
    hε, hεδ, hj, hD, mul_pos hn hj, hN, hL, hE, hl, hσ, hσε, hCerr, hK, ?_⟩
  intro p hp f hf hfn hcb
  obtain ⟨arrival, g, hac, haa, hal, htime, htimeσ, _hgc, _hga, _hgl, hright, hleft, hphysical⟩ :=
    hglobal p hp f hf hfn hcb
  have hpreall {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU hV B.charge B.cosmological
        (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x) (u : ℝ) (hu : u ∈ Ioo 0 ε)
      (q : Icc 0 U) (hqu : (q : ℝ) ≤ u) (v : Icc 0 V) (hvt : (v : ℝ) ≤ arrival u) :
      Y ≤ x.1 q v 0 ∧
      |radialNuField hV B.charge B.cosmological
        (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose q v| ≤
          N * Real.exp (B.outerRate * v) ∧ |x.2.1 q v 1| ≤ E * Real.exp (-c * v) := by
    obtain ⟨_hT, _hjT, _hDT, _hbl, _hCh, W, S, hW, hS, hWR, hfW, z, hz, huW, htS,
      _hWε, _hfloor, _hhit, _hlneg, _hnlo, _hnhi, _hlow, _hhigh, _hk, _hscalar, hpre, _rest⟩ := hphysical u hu
    have hqW : (q : ℝ) ∈ Icc 0 W := ⟨q.property.1, hqu.trans huW.le⟩
    have hvS : (v : ℝ) ∈ Icc 0 S := ⟨v.property.1, hvt.trans htS.le⟩
    have hh := hpre ⟨q, hqW⟩ hqu ⟨v, hvS⟩ hvt
    have heq := hz.horizon_overlap hW hS hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
      hqW q.property hvS v.property
    have hnq := hz.horizon_overlap_nu hW hS hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
      hqW q.property hvS v.property
    rw [heq.1, heq.2, hnq] at hh
    exact hh
  refine ⟨arrival, g, hac, haa, hal, htimeσ, ?_, hleft, hpreall, ?_, ?_⟩
  · intro t ht
    obtain ⟨hgt, hrt, _rest⟩ := hright t (htime.trans_le ht)
    have hgtσ : g t < σ := by
      by_contra hnot
      have hh := haa.antitoneOn ⟨hσ, hσε.trans (half_lt_self hε)⟩
        ⟨hgt.1, hgt.2.trans (half_lt_self hε)⟩ (not_lt.1 hnot)
      rw [hrt] at hh
      exact (not_le_of_gt (htimeσ.trans_le ht)) hh
    exact ⟨⟨hgt.1, hgtσ⟩, hrt⟩
  · intro U V hU hV hUR hfU x hx u v hu hrad hlam
    obtain ⟨ha, _hj, _hD, _hb, _hC, W, S, hW, hS, hWR, hfW, z, hz, huW, haS,
      _hWε, _hfloor, hhit, hlneg, _⟩ := hphysical u hu
    exact hz.trapped_level_time_unique hW hS hWR hU hV hUR hc hi hrc hr0 hφ hrd
      hp hfW hfU hx ⟨hu.1.le, huW.le⟩ u.property ⟨ha.le, haS.le⟩ v.property hhit hrad hlneg hlam
  · intro u hu
    obtain ⟨hT, hjT, hDT, _hbl, _hCh, W, S, hW, hS, hWR, hfW, z, hz, huW, htS,
      _hWε, _hfloor, hhit, hlneg, hnlo, _hnhi, hlow, hhigh, _hk, _hscalar, _hpre, hda, _hjac, _hgd, herr⟩ := hphysical u hu
    refine ⟨hT, hjT, hDT, ?_⟩
    intro U V hU hV hUR hfU x hx huU htV
    let uw : Icc 0 W := ⟨u, hu.1.le, huW.le⟩
    let ts : Icc 0 S := ⟨arrival u, hT.le, htS.le⟩
    have he := hz.horizon_overlap hW hS hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
      uw.property huU ts.property htV
    have hne := hz.horizon_overlap_nu hW hS hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
      uw.property huU ts.property htV
    have hupper : -z.2.1 uw ts 0 ≤ L := (neg_le_abs _).trans hhigh
    rw [he.1] at hhit
    rw [he.2] at hlneg hlow hupper
    rw [hne] at hnlo
    rw [he.2, hne] at hda
    refine ⟨hhit, hlneg, hnlo, hlow, hupper, hda, ?_, ?_⟩
    · intro q hqu v hvt
      exact hpreall hU hV hUR hfU hx u hu q hqu v hvt
    · intro huσ
      have hh := herr huσ
      simp only [massField_apply] at hh ⊢
      rw [he.1, he.2, hne] at hh
      exact hh

end CauchyHorizon.Background
