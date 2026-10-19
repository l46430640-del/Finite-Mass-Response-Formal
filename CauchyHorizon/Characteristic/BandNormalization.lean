import CauchyHorizon.Characteristic.PrearrivalNormalization
import CauchyHorizon.Characteristic.BandRadiationDomain

/-! Uniform phase and Jacobian normalization on the constructed radius curves. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

theorem exists_band_normalization (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧ R < r 0 ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ U₀ T : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ (∀ ε, T ≤ τ ε) ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
          MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧
            Tendsto g atTop (𝓝 0) ∧ ContinuousOn (deriv g) (Ici T) ∧
            (∀ t ∈ Ici T, g t ∈ Ioo 0 (r 0)) ∧
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x),
                ∀ t ∈ Icc T V, g t ≤ U →
                  let u := projIcc 0 U hU (g t)
                  let v := projIcc 0 V hV t
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                  x.1 u v 0 = Y ∧ ∀ ε : Ioi (0 : ℝ), τ ε ≤ t →
                    |Real.log (B.outerRate * (g t * ν u v / B.F Y))| +
                      |Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t))))| < ε := by
  dsimp only
  let a := B.outerRate
  let c := min s a / 2
  have ha : 0 < a := B.outerRate_pos
  have hc0 : 0 < c := half_pos (lt_min hs ha)
  have hca : c < a := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  have hcs : c ≤ s := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (half_le_self hs.le)
  have hcHalf : c ≤ a / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨δ, R, hδ, hδr, hR, hRr, hdomain⟩ := B.exists_band_radiation_domain
    hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, hRr, ?_⟩
  intro Y hY hYR
  obtain ⟨U₀, T, j, D, η, C, N, L, hU₀, hUδ, hT, hj, hD, _hη, _hC, _hN, _hL, hsolve⟩ :=
    hdomain Y hY hYR
  have hnorm (ε : Ioi (0 : ℝ)) := B.exists_prearrival_normalization
    hs hH hdH hdHR hA hY (hYR.trans_lt hR.2) hj hD hc hb hrc hrb hrd hrdec hOut ε ε.property
  choose τ₀ _hτ₀ hnorm using hnorm
  let τ := fun ε => max T (τ₀ ε)
  refine ⟨U₀, T, τ, hU₀, hUδ, hT, fun _ => le_max_left _ _, ?_⟩
  intro p hp f hf hfn
  have hcp : c ≤ a * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le
    linarith only [hcHalf, hh, ha]
  obtain ⟨g, hgc, hga, hgl, hgdc, _hgT, hpoint, hphysical⟩ := hsolve p hp f hf hfn hcp
  refine ⟨g, hgc, hga, hgl, hgdc, fun t ht => (hpoint t ht).1, ?_⟩
  intro U V hU hV hUR hUU hfU x hx t ht hgtU
  have hgt : g t ∈ Icc 0 U := ⟨(hpoint t ht.1).1.1.le, hgtU⟩
  have htv : t ∈ Icc 0 V := ⟨hT.le.trans ht.1, ht.2⟩
  let u : Icc 0 U := ⟨g t, hgt⟩
  let v : Icc 0 V := ⟨t, htv⟩
  have hphys := hphysical U V hU hV hUR hUU hfU x hx
  have hhit : x.1 u v 0 = Y := by
    simpa only [intervalExtension_apply, projIcc_of_mem hU hgt, projIcc_of_mem hV htv] using
      hphys.2.1 t ht hgtU
  have hfloor (q : Icc 0 U) (hqu : q ≤ u) (w : Icc 0 V) (hwv : w ≤ v) : Y ≤ x.1 q w 0 := by
    have hmax : max T (w : ℝ) ≤ t := max_le ht.1 hwv
    have hg := hga.antitoneOn (le_max_left T (w : ℝ)) ht.1 hmax
    change (q : ℝ) ≤ g t at hqu
    exact (hphys.1 q w (hqu.trans hg)).1
  rw [projIcc_of_mem hU hgt, projIcc_of_mem hV htv]
  refine ⟨hhit, ?_⟩
  intro ε hεt
  have hh := (hnorm ε U V hU hV hUR p hp f hfU x hx
    ((scalar_prefix_norm_le (hUU.trans hUδ) hf).trans hfn) u v
    ((le_max_right _ _).trans hεt) (hpoint t ht.1).2.2.2.2.1 (hpoint t ht.1).2.1 hfloor).2
  rw [hhit] at hh
  exact hh

end CauchyHorizon.Background
