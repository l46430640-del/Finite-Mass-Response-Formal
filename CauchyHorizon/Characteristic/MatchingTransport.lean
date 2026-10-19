import CauchyHorizon.Characteristic.BandArrival
import CauchyHorizon.Characteristic.TrappedTransport

/-! Matching data give a time-independent conformal weight on every existing trapped prefix. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1200000 in
theorem exists_matching_q_control (B : Background) {s H dH A c : ℝ}
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
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ ε cq Cq : ℝ,
        0 < ε ∧ ε ≤ δ ∧ 0 < cq ∧ 0 < Cq ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A → c ≤ B.outerRate * (1 - 1 / p.toReal) →
          ∃ arrival : ℝ → ℝ, ContinuousOn arrival (Ioo 0 ε) ∧ StrictAntiOn arrival (Ioo 0 ε) ∧
            Tendsto arrival (𝓝[>] (0 : ℝ)) atTop ∧ ∀ u ∈ Ioo 0 ε, 0 < arrival u ∧
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
                (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V),
                IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x →
                ∀ (huU : u ∈ Icc 0 U) (htV : arrival u ∈ Icc 0 V),
                  let q := fun v => Real.exp (x.1 ⟨u, huU⟩ v 2) / (4 * (-x.2.1 ⟨u, huU⟩ v 0))
                  x.1 ⟨u, huU⟩ ⟨arrival u, htV⟩ 0 = Y ∧
                  cq ≤ u * q ⟨arrival u, htV⟩ ∧ u * q ⟨arrival u, htV⟩ ≤ Cq ∧
                  ∀ v : Icc 0 V, arrival u ≤ (v : ℝ) →
                    x.2.1 ⟨u, huU⟩ v 0 < 0 ∧ x.1 ⟨u, huU⟩ v 0 ≤ Y ∧
                    0 < q v ∧ q v ≤ Cq / u ∧
                    Real.exp (x.1 ⟨u, huU⟩ v 2) ≤ (4 * Cq / u) * (-x.2.1 ⟨u, huU⟩ v 0) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, hδr, hR, _hRr, hsolve⟩ :=
    B.exists_band_arrival hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨ε, j, D, _b, _C, _K, n, N, L, _E, τ, _σ, _Cerr,
    hε, hεδ, hj, hD, _hb, _hC, _hK, hn, hN, hL, _hE, hτ, _hσ, _hσε, _hCerr, hglobal⟩ := hsolve Y hY hYR
  let cq := 3 * (n * j) / (4 * (L + 1))
  let Cq := N * D / τ
  have hcq : 0 < cq := div_pos (by positivity) (by positivity)
  have hCq : 0 < Cq := div_pos (mul_pos hN hD) hτ
  refine ⟨ε, cq, Cq, hε, hεδ, hcq, hCq, ?_⟩
  intro p hp f hf hfn hcb
  obtain ⟨arrival, _g, hac, haa, hal, _hK, _hKσ, _hgc, _hga, _hgl, _hright, _hleft, hphysical⟩ :=
    hglobal p hp f hf hfn hcb
  refine ⟨arrival, hac, haa, hal, ?_⟩
  intro u hu
  obtain ⟨hT, _hjT, _hDT, _hbl, _hCh, W, S, hW, hS, hWR, hfW, z, hz, huW, htS,
    _hWε, _hfloor, hhit, hlneg, hnlo, hnhi, hl, hLabs, hklo, _hscalar, _hpre, _hda, _hjac, _hgd, _herr⟩ := hphysical u hu
  let uw : Icc 0 W := ⟨u, hu.1.le, huW.le⟩
  let ts : Icc 0 S := ⟨arrival u, hT.le, htS.le⟩
  let ν := radialNuField hS B.charge B.cosmological
    (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose
  have hg := hz.interior_gauge hW hS hWR hc hi hrc hr0 hφ hrd hp hfW uw ts
  have hν : ν uw ts < 0 := hg.2.2.1
  have hehi : Real.exp (z.1 uw ts 2) ≤ 4 * (-ν uw ts) := by
    have hh := (div_le_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hν)).1 hg.2.2.2.2
    linarith only [hh]
  have helo : 3 * (-ν uw ts) ≤ Real.exp (z.1 uw ts 2) := by
    have hh := (le_div_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hν)).1 hklo
    linarith only [hh]
  have hscaledlo : 3 * (n * j) ≤ u * Real.exp (z.1 uw ts 2) := by
    have hh := mul_le_mul_of_nonneg_left helo hu.1.le
    nlinarith only [hh, hnlo]
  have hscaledhi : u * Real.exp (z.1 uw ts 2) ≤ 4 * (N * D) := by
    have hh := mul_le_mul_of_nonneg_left hehi hu.1.le
    nlinarith only [hh, hnhi]
  have hden : 0 < 4 * (-z.2.1 uw ts 0) := mul_pos (by norm_num) (neg_pos.2 hlneg)
  have hscale : u * (Real.exp (z.1 uw ts 2) / (4 * (-z.2.1 uw ts 0))) =
      u * Real.exp (z.1 uw ts 2) / (4 * (-z.2.1 uw ts 0)) := by ring
  have hqlo : cq ≤ u * (Real.exp (z.1 uw ts 2) / (4 * (-z.2.1 uw ts 0))) := by
    rw [hscale]
    apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ 3 * (n * j)) hden
      (by linarith only [neg_le_abs (z.2.1 uw ts 0), hLabs] : 4 * (-z.2.1 uw ts 0) ≤ 4 * (L + 1))).trans
    exact div_le_div_of_nonneg_right hscaledlo hden.le
  have hqhi : u * (Real.exp (z.1 uw ts 2) / (4 * (-z.2.1 uw ts 0))) ≤ Cq := by
    rw [hscale]
    calc
      _ ≤ (4 * (N * D)) / (4 * (-z.2.1 uw ts 0)) := div_le_div_of_nonneg_right hscaledhi hden.le
      _ ≤ (4 * (N * D)) / (4 * τ) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hl])
      _ = Cq := by dsimp only [Cq]; ring
  refine ⟨hT, ?_⟩
  intro U V hU hV hUR hfU x hx huU htV
  have he := hz.horizon_overlap hW hS hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
    uw.property huU ts.property htV
  have hhit' : x.1 ⟨u, huU⟩ ⟨arrival u, htV⟩ 0 = Y := by rw [← he.1]; exact hhit
  have hneg' : x.2.1 ⟨u, huU⟩ ⟨arrival u, htV⟩ 0 < 0 := by rw [← he.2]; exact hlneg
  have hqlo' : cq ≤ u * (Real.exp (x.1 ⟨u, huU⟩ ⟨arrival u, htV⟩ 2) /
      (4 * (-x.2.1 ⟨u, huU⟩ ⟨arrival u, htV⟩ 0))) := by rw [← he.1, ← he.2]; exact hqlo
  have hqhi' : u * (Real.exp (x.1 ⟨u, huU⟩ ⟨arrival u, htV⟩ 2) /
      (4 * (-x.2.1 ⟨u, huU⟩ ⟨arrival u, htV⟩ 0))) ≤ Cq := by rw [← he.1, ← he.2]; exact hqhi
  refine ⟨hhit', hqlo', hqhi', ?_⟩
  intro v htv
  have htrap := hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hfU
    ⟨u, huU⟩ ⟨arrival u, htV⟩ v htv hneg'
  obtain ⟨_hJi, _hJ0, _heq, hqpos, hqanti, _hlfac⟩ :=
    hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hfU ⟨u, huU⟩ ⟨arrival u, htV⟩ v htv hneg'
  have hqu : Real.exp (x.1 ⟨u, huU⟩ v 2) / (4 * (-x.2.1 ⟨u, huU⟩ v 0)) ≤ Cq / u :=
    hqanti.trans ((le_div_iff₀ hu.1).2 (by simpa only [mul_comm] using hqhi'))
  refine ⟨htrap.1, htrap.2.trans_eq hhit', hqpos, hqu, ?_⟩
  have hh := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (neg_pos.2 htrap.1))).1 hqu
  calc
    _ ≤ Cq / u * (4 * (-x.2.1 ⟨u, huU⟩ v 0)) := hh
    _ = _ := by ring

end CauchyHorizon.Background
