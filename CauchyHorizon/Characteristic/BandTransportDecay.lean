import CauchyHorizon.Characteristic.PrefixTransportDecay
import CauchyHorizon.Characteristic.BandRadiationDomain

/-! Actual lapse and inverse-speed derivative decay on any fixed compact radius band. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_band_transport_decay (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ C d γ T : ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧ 0 ≤ C ∧ 0 < d ∧ 0 < γ ∧ 0 < T ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
            MemLp f p (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x),
                ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ∈ Ioo 0 U → (v : ℝ) ∈ Ioo 0 V →
                  T ≤ (v : ℝ) → x.1 u v 0 ∈ Icc Y Z →
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                  let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) /
                    (4 * intervalExtension hV (ν u) t)
                  let cv := (deriv κ v / κ v) / x.2.1 u v 0 -
                    (x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2)
                  x.2.1 u v 0 ≤ -d ∧
                    |deriv κ v / κ v| + |cv| ≤ C * Real.exp (-γ * v) ∧
                    ∀ (S : Set ℝ) (g : ℝ → ℝ), g v = u →
                      HasDerivWithinAt g (-x.2.1 u v 0 / ν u v) S v →
                      HasDerivWithinAt
                        (fun t => -1 / intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 0) cv S v := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let c := min s a / 2
  have hc0 : 0 < c := half_pos (lt_min hs ha)
  have hca : c < a := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  have hcs : c ≤ s := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (half_le_self hs.le)
  have hcHalf : c ≤ a / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨δ, R, hδ, hδr, hR, _hRr, hdomain⟩ := B.exists_band_radiation_domain
    hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨UY, TY, _j, D, _η, _Cg, _N, _L,
    hUY, hUYδ, hTY, _hj, hD, _hη, _hCg, _hN, _hL, hsolve⟩ := hdomain Y hY hYR
  obtain ⟨Up, C, d, Tp, hUp, _hUpr, hC, hd, _hTp, hdecay⟩ := B.exists_compact_prefix_transport_decay
    hs hH hdH hdHR hA hY hYZ.le hZ hD.le hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  let γ := min a (2 * c)
  have hγ : 0 < γ := lt_min ha (by positivity)
  refine ⟨min UY Up, C, d, γ, max TY Tp, lt_min hUY hUp, (min_le_left _ _).trans hUYδ,
    hC, hd, hγ, hTY.trans_le (le_max_left _ _), ?_⟩
  intro p hp f hf hfn
  have hcp : c ≤ a * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le
    linarith only [hcHalf, hh, ha]
  obtain ⟨gY, _hgc, hga, _hgl, _hgdc, _hgstart, hpoint, hphysical⟩ := hsolve p hp f hf hfn hcp
  intro U V hU hV hUR hUU hfU x hx u v hu hv hTv hrband
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
  let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) / (4 * intervalExtension hV (ν u) t)
  have hvY : TY ≤ (v : ℝ) := (le_max_left _ _).trans hTv
  have hphys := hphysical U V hU hV hUR (hUU.trans (min_le_left _ _)) hfU x hx
  have hug : (u : ℝ) ≤ gY v := by
    by_cases hgU : gY v ≤ U
    · have hg : gY v ∈ Icc 0 U := ⟨(hpoint v hvY).1.1.le, hgU⟩
      have hhit := hphys.2.1 v ⟨hvY, v.property.2⟩ hgU
      simp only [intervalExtension_apply, projIcc_of_mem hU hg, projIcc_of_mem hV v.property] at hhit
      by_contra hn
      have hanti := hx.radial_strictAnti hx.choose rfl
        (incomingWave_constraint_data hU hUR hp hfU (horizonPhi h r 0)).1 v
        (fun q => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU q v).2.2.1)
      have hh := hanti (show (⟨gY v, hg⟩ : Icc 0 U) < u from lt_of_not_ge hn)
      change x.1 u v 0 < x.1 ⟨gY v, hg⟩ v 0 at hh
      rw [hhit] at hh
      exact (not_lt_of_ge hrband.1) hh
    · exact u.property.2.trans (lt_of_not_ge hgU).le
  let hf' := hfU.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
  let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (v : ℝ))
    le_rfl (by simpa only [zero_add] using u.property.2) le_rfl (by simpa only [zero_add] using v.property.2) x
  have hy := hx.horizon_prefix hU hV hUR u.property.1 v.property.1 u.property.2 v.property.2 hc hi hrc hr0 hp hfU
  let uu : Icc 0 (u : ℝ) := ⟨u, u.property.1, le_rfl⟩
  let vv : Icc 0 (v : ℝ) := ⟨v, v.property.1, le_rfl⟩
  have hpre := hphysical u v u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    (u.property.2.trans (hUU.trans (min_le_left _ _))) hf' y hy
  have hfloor (q : Icc 0 (u : ℝ)) (w : Icc 0 (v : ℝ)) : Y ≤ y.1 q w 0 :=
    (hpre.1 q w (q.property.2.trans (hug.trans
      (hga.antitoneOn (le_max_left TY (w : ℝ)) hvY (max_le hvY w.property.2))))).1
  have he := hy.horizon_overlap u.property.1 v.property.1 (u.property.2.trans_lt hUR) hU hV hUR
    hc hi hrc hr0 hp hf' hfU hx uu.property u.property vv.property v.property
  have hne := hy.horizon_overlap_nu u.property.1 v.property.1 (u.property.2.trans_lt hUR) hU hV hUR
    hc hi hrc hr0 hp hf' hfU hx uu.property u.property vv.property v.property
  have hnorm := (scalar_prefix_norm_le
    (u.property.2.trans (hUU.trans ((min_le_left _ _).trans hUYδ))) hf).trans hfn
  have hwidth := (mul_le_mul_of_nonneg_right hug (Real.exp_pos _).le).trans (hpoint v hvY).2.1
  have hhit : y.1 uu vv 0 ≤ Z := by rw [he.1]; exact hrband.2
  have hbound := hdecay u v u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    p hp f hf' y hy hnorm hcp (u.property.2.trans (hUU.trans (min_le_right _ _)))
    hfloor hwidth ((le_max_right _ _).trans hTv) uu hhit
  simp only [massField_apply] at hbound
  rw [he.1, he.2, hne] at hbound
  have hlneg : x.2.1 u v 0 < 0 := hbound.1.trans_lt (neg_neg_of_pos hd)
  have htransport := hx.horizon_radius_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hfU u v hu hv hlneg.ne
  have hκv : κ v = -Real.exp (x.1 u v 2) / (4 * ν u v) := by
    simp only [κ, intervalExtension_apply, projIcc_of_mem hV v.property]
  have hn : ν u v ≠ 0 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU u v).2.2.1.ne
  have hκn : κ v ≠ 0 := by
    rw [hκv]
    exact div_ne_zero (neg_ne_zero.2 (Real.exp_ne_zero _)) (mul_ne_zero (by norm_num) hn)
  refine ⟨hbound.1, ?_, htransport.2⟩
  change |deriv κ v / κ v| + |_ - _| ≤ C * Real.exp (-γ * (v : ℝ))
  rw [htransport.1.deriv, mul_div_cancel_left₀ _ hκn]
  simpa only [intervalExtension_apply, projIcc_of_mem hV v.property, massField_apply] using hbound.2

end CauchyHorizon.Background
