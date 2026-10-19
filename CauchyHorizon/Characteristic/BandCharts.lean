import CauchyHorizon.Characteristic.BandCrossing
import CauchyHorizon.Characteristic.ContactNeighborhood
import CauchyHorizon.Characteristic.PhysicalOverlapNu
import CauchyHorizon.Reduced.RadialArrival

/-! Actual interior matching charts with uniform scales, speed bounds and exact Jacobian. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1200000 in
theorem exists_band_charts (B : Background) {s H dH A c : ℝ}
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
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ U₀ j D n N L E τ : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ 0 < j ∧ 0 < D ∧ 0 < n ∧ 0 < N ∧ 0 ≤ L ∧ 0 ≤ E ∧ 0 < τ ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A → c ≤ B.outerRate * (1 - 1 / p.toReal) →
          ∀ (U : ℝ) (hU : 0 < U),
            U < U₀ → ∃ T : ℝ, ∃ hT : 0 < T,
              j ≤ U * Real.exp (B.outerRate * T) ∧ U * Real.exp (B.outerRate * T) ≤ D ∧
              ∃ W V : ℝ, ∃ hW : 0 ≤ W, ∃ hV : 0 ≤ V, ∃ hWR : W < r 0,
              ∃ hfW : MemLp f p (volume.restrict (Icc 0 W)), ∃ z : WaveState W V,
              ∃ hz : IsWaveIntegral hW hV B.charge B.cosmological
                (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hWR hp hfW) z,
              ∃ hUW : U < W, ∃ hTV : T < V,
              let u : Icc 0 W := ⟨U, hU.le, hUW.le⟩
              let v : Icc 0 V := ⟨T, hT.le, hTV.le⟩
              let ν := radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose
              W ≤ U₀ ∧ (∀ u v, Y / 2 ≤ z.1 u v 0) ∧ z.1 u v 0 = Y ∧
              n * j ≤ U * (-ν u v) ∧ U * (-ν u v) ≤ N * D ∧
              τ ≤ -z.2.1 u v 0 ∧ |z.2.1 u v 0| ≤ L ∧
              (3 / 4 : ℝ) ≤ -Real.exp (z.1 u v 2) / (4 * ν u v) ∧ |z.2.1 u v 1| ≤ E * Real.exp (-c * T) ∧
              (∀ w ≤ u, ∀ t ≤ v, Y ≤ z.1 w t 0 ∧ |ν w t| ≤ N * Real.exp (B.outerRate * t) ∧
                |z.2.1 w t 1| ≤ E * Real.exp (-c * t)) ∧
              ∃ ψ : ℝ → ℝ, ψ T = U ∧ HasStrictDerivAt ψ (-z.2.1 u v 0 / ν u v) T ∧
                (-ν u v) * (-deriv ψ T) = -z.2.1 u v 0 ∧
                τ / (N * D) ≤ -deriv ψ T / U ∧ -deriv ψ T / U ≤ L / (n * j) ∧
                ∀ᶠ t in 𝓝 T, ψ t ∈ Ioo 0 W ∧ t ∈ Ioo 0 V ∧
                  intervalExtension hV (intervalExtension hW z.1 (ψ t)) t 0 = Y := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, hδr, hR, hRr, hcross⟩ :=
    B.exists_band_crossing hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, hRr, ?_⟩
  intro Y hY hYR
  obtain ⟨U₀, j, D, n, N, L, E, τ, hU₀, hU₀δ, hU₀1, hU₀r, hj, hD, hn, hN, hL, hE, hτ, hsolve⟩ :=
    hcross Y hY hYR
  refine ⟨U₀, j, D, n, N, L, E, τ, hU₀, hU₀δ, hj, hD, hn, hN, hL, hE, hτ, ?_⟩
  intro p hp f hf hfn hcb U hU hUU
  have hUR : U < r 0 := hUU.trans hU₀r
  let hfU := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (hUU.le.trans hU₀δ)) le_rfl)
  obtain ⟨T, hT, x, hx, hxlo, hhit, hfirst, hjT, hDT, hnlo, hnhi, hlam, hg, _hscalar⟩ :=
    hsolve p hp f hf hfn hcb U hU hUR hfU hUU.le
  let hfmax := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hU₀δ) le_rfl)
  have hfmaxnorm := (scalar_prefix_norm_le hU₀δ hf).trans hfn
  obtain ⟨W, V, hW, hV, hWR, hfW, z, hz, hUW, hWU₀, hTV, hzfloor⟩ :=
    hx.exists_contact_neighborhood hU hT hUR hUU hU₀1 hU₀r (B.inner_pos.trans hY) hA
      B.outerRate_pos.le hN hc hi hrc hr0 hφ hrd hp hfmax hfmaxnorm hfU hhit hfirst (by
        intro W hW hWR hfW hWrange
        obtain ⟨S, hS, y, hy, hlo, hhit, hfirst, _hjS, _hDS, _hnlo, _hnhi, _hlam, hg, _hscalar⟩ :=
          hsolve p hp f hf hfn hcb W (hU.trans hWrange.1) hWR hfW hWrange.2
        exact ⟨S, hS, y, hy, hlo, hhit, hfirst, fun u => (hg u ⟨S, hS.le, le_rfl⟩).2.2.2.1⟩)
  let u : Icc 0 W := ⟨U, hU.le, hUW.le⟩
  let v : Icc 0 V := ⟨T, hT.le, hTV.le⟩
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose
  have he := hz.horizon_overlap hW hV hWR hU.le hT.le hUR hc hi hrc hr0 hp hfW hfU hx
    u.property ⟨hU.le, le_rfl⟩ v.property ⟨hT.le, le_rfl⟩
  have hne := hz.horizon_overlap_nu hW hV hWR hU.le hT.le hUR hc hi hrc hr0 hp hfW hfU hx
    u.property ⟨hU.le, le_rfl⟩ v.property ⟨hT.le, le_rfl⟩
  have hrY : z.1 u v 0 = Y := (congrArg (fun z : WaveVector => z 0) he.1).trans hhit
  have hνneg : ν u v < 0 := (hz.interior_gauge hW hV hWR hc hi hrc hr0 hφ hrd hp hfW u v).2.2.1
  have hνn : ν u v ≠ 0 := hνneg.ne
  have hzlo : n * j ≤ U * (-ν u v) := by rw [hne]; exact hnlo
  have hzhi : U * (-ν u v) ≤ N * D := by rw [hne]; exact hnhi
  have hzlam : τ ≤ -z.2.1 u v 0 := by rw [he.2]; exact hlam
  have hzL : |z.2.1 u v 0| ≤ L := by rw [he.2]; exact (hg _ _).2.1
  have hzk : (3 / 4 : ℝ) ≤ -Real.exp (z.1 u v 2) / (4 * ν u v) := by
    rw [he.1, hne]
    exact (hg _ _).2.2.2.2.1
  have hzscalar : |z.2.1 u v 1| ≤ E * Real.exp (-c * T) := by rw [he.2]; exact (hg _ _).2.2.2.2.2
  obtain ⟨ψ, hψ, hdψ, hgraph⟩ := hz.exists_radial_level_chart hz.choose rfl
    (incomingWave_constraint_data hW hWR hp hfW (horizonPhi h r 0)).1 u v ⟨hU, hUW⟩ ⟨hT, hTV⟩ hνn
  change HasStrictDerivAt ψ (-z.2.1 u v 0 / ν u v) T at hdψ
  have hjac : (-ν u v) * (-deriv ψ T) = -z.2.1 u v 0 := by
    rw [hdψ.hasDerivAt.deriv]
    field_simp [hνn]
  have hspeed : -deriv ψ T / U = (-z.2.1 u v 0) / (U * (-ν u v)) := by
    rw [hdψ.hasDerivAt.deriv]
    field_simp [hνn]
  refine ⟨T, hT, hjT, hDT, W, V, hW, hV, hWR, hfW, z, hz, hUW, hTV,
    hWU₀, hzfloor, hrY, hzlo, hzhi, hzlam, hzL, hzk, hzscalar, ?_, ψ, hψ, hdψ, hjac, ?_, ?_, ?_⟩
  · intro w hwu t htv
    have hwU : (w : ℝ) ∈ Icc 0 U := ⟨w.property.1, hwu⟩
    have htT : (t : ℝ) ∈ Icc 0 T := ⟨t.property.1, htv⟩
    have hew := hz.horizon_overlap hW hV hWR hU.le hT.le hUR hc hi hrc hr0 hp hfW hfU hx
      w.property hwU t.property htT
    have hnw := hz.horizon_overlap_nu hW hV hWR hU.le hT.le hUR hc hi hrc hr0 hp hfW hfU hx
      w.property hwU t.property htT
    rw [hew.1, hew.2, hnw]
    have hg' := hg ⟨w, hwU⟩ ⟨t, htT⟩
    have hnneg := (hx.interior_gauge hU.le hT.le hUR hc hi hrc hr0 hφ hrd hp hfU ⟨w, hwU⟩ ⟨t, htT⟩).2.2.1
    rw [abs_of_neg hnneg]
    exact ⟨hxlo _ _, hg'.2.2.2.1, hg'.2.2.2.2.2⟩
  · rw [hspeed]
    exact div_le_div₀ (hτ.le.trans hzlam) hzlam (mul_pos hU (neg_pos.2 hνneg)) hzhi
  · rw [hspeed]
    exact div_le_div₀ hL ((neg_le_abs _).trans hzL) (mul_pos hn hj) hzlo
  · simpa only [hrY] using hgraph

end CauchyHorizon.Background
