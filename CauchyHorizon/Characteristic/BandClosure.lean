import CauchyHorizon.Characteristic.BandBootstrap
import CauchyHorizon.Characteristic.FiniteFeedback
import CauchyHorizon.Analysis.PrefixBootstrap

/-! The lower-kappa bootstrap is removed on every existing fixed-band prefix. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 1000000 in
theorem exists_band_bounds (B : Background) {s H dH A c : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ U₀ D n N L E : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ 0 < D ∧ 0 < n ∧ 0 < N ∧ 0 ≤ L ∧ 0 ≤ E ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (_hf : MemLp f p (volume.restrict (Icc 0 δ))),
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A → c ≤ B.outerRate * (1 - 1 / p.toReal) →
          ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
            (hx : IsWaveIntegral hU hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x),
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
            U ≤ U₀ → (∀ u v, Y ≤ x.1 u v 0) →
            U * Real.exp (B.outerRate * V) ≤ D ∧
            (∀ u v, x.1 u v 0 ≤ B.event + dH ∧ |x.2.1 u v 0| ≤ L ∧
              n * Real.exp (B.outerRate * v) ≤ -ν u v ∧ -ν u v ≤ N * Real.exp (B.outerRate * v) ∧
              (3 / 4 : ℝ) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧ |x.2.1 u v 1| ≤ E * Real.exp (-c * v)) ∧
            (∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
              |x.2.2 u v 1| ≤ (r 0 / Y) * |f u| + (N / (Y * (B.outerRate - c))) * E * Real.exp ((B.outerRate - c) * v)) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  let η := Real.log (4 / 3 : ℝ)
  have hη : 0 < η := Real.log_pos (by norm_num)
  have hexp : Real.exp (-η) = (3 / 4 : ℝ) := by
    simp only [η, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  obtain ⟨δ, R, hδ, hδr, hR, himprove⟩ :=
    B.exists_band_improvement hs hH hdH hdHR hA hc0 hca hcs hη hc hb hrc hrb hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, ?_⟩
  intro Y hY hYR
  have hY0 : 0 < Y := B.inner_pos.trans hY
  obtain ⟨U₁, T, D, n, N, L, hU₁, hU₁δ, hT, hD, hn, hN, hL, hlate⟩ := himprove Y hY hYR
  obtain ⟨U₂, hU₂, _hU₂1, _hU₂r, hearly⟩ :=
    exists_finite_small_width_kappa hT hrp hY0 hA hη hc hi hrc hr0 hφ hrd
  let E := ((H + L * (r 0 / Y) * (A * max 1 D)) / Y) * Real.exp (L * N * D / (Y ^ 2 * (B.outerRate - c)))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨min U₁ U₂, D, n, N, L, E, lt_min hU₁ hU₂, (min_le_left _ _).trans hU₁δ,
    hD, hn, hN, hL, hE, ?_⟩
  intro p hp f hf hfn hcb U V hU hV hUR hfU x hx
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
  change U ≤ min U₁ U₂ → (∀ u v, Y ≤ x.1 u v 0) → _
  intro hUU hlo
  have hUU₁ := hUU.trans (min_le_left _ _)
  have hUU₂ := hUU.trans (min_le_right _ _)
  have hfnU := (scalar_prefix_norm_le (hUU₁.trans hU₁δ) hf).trans hfn
  let K : ℝ → Icc 0 U → ℝ := fun t u => -Real.exp (intervalExtension hV (x.1 u) t 2) /
    (4 * intervalExtension hV (ν u) t)
  have hK (t : ℝ) (ht : t ∈ Icc 0 V) (u : Icc 0 U) :
      K t u = -Real.exp (x.1 u ⟨t, ht⟩ 2) / (4 * ν u ⟨t, ht⟩) := by
    simp only [K, intervalExtension_apply, projIcc_of_mem hV ht]
  have hrow (t : ℝ) (ht : t ∈ Icc 0 V)
      (hboot : T < t → ∀ q ∈ Icc (0 : ℝ) t, ∀ u, (1 / 2 : ℝ) ≤ K q u) :
      ∀ u, (3 / 4 : ℝ) ≤ K t u := by
    let y := waveTranslate (a := 0) (U := U) (b := 0) (V := t) le_rfl (by simp)
      le_rfl (by simpa only [zero_add] using ht.2) x
    have hy : IsWaveIntegral hU ht.1 B.charge B.cosmological
        (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological t hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) y :=
      hx.horizon_prefix hU hV hUR hU ht.1 le_rfl ht.2 hc hi hrc hr0 hp hfU
    let νy := radialNuField ht.1 B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) y.1 hy.choose
    have hye (u : Icc 0 U) (w : Icc 0 t) : y.1 u w = x.1 u ⟨w, w.property.1, w.property.2.trans ht.2⟩ := by
      change x.1 (intervalTranslate (a := 0) (U := U) le_rfl (by simp) u)
        (intervalTranslate (a := 0) (U := t) le_rfl (by simpa only [zero_add] using ht.2) w) = _
      rw [intervalTranslate_zero]
      congr 1
      exact Subtype.ext (zero_add _)
    have hne (u : Icc 0 U) (w : Icc 0 t) : νy u w = ν u ⟨w, w.property.1, w.property.2.trans ht.2⟩ :=
      radialNuField_prefix_eq ht.1 hV ht.2 B.charge B.cosmological
        (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 y.1 hx.choose hy.choose hye u w
    have hKy (u : Icc 0 U) (w : Icc 0 t) : -Real.exp (y.1 u w 2) / (4 * νy u w) = K w u := by
      rw [hK w ⟨w.property.1, w.property.2.trans ht.2⟩ u, hye, hne]
    have hloy (u : Icc 0 U) (w : Icc 0 t) : Y ≤ y.1 u w 0 := by rw [hye]; exact hlo _ _
    intro u
    have hbound : Real.exp (-η) ≤ -Real.exp (y.1 u ⟨t, ht.1, le_rfl⟩ 2) / (4 * νy u ⟨t, ht.1, le_rfl⟩) := by
      by_cases htT : t ≤ T
      · exact (hearly U t hU ht.1 hUR p hp f hfU y hy hfnU hUU₂ htT hloy u ⟨t, ht.1, le_rfl⟩).2
      · have htT' : T < t := lt_of_not_ge htT
        have hky (q : Icc 0 U) (w : Icc 0 t) : (1 / 2 : ℝ) ≤ -Real.exp (y.1 q w 2) / (4 * νy q w) := by
          rw [hKy]
          exact hboot htT' w w.property q
        exact ((hlate p hp f hf hfn hcb U t hU ht.1 hUR hfU y hy hUU₁ hloy hky).2.2 htT'.le u).2.1
    simpa only [hexp, hKy] using hbound
  let G : ℝ × Icc 0 U → ℝ := fun z => 1 / 2 - K z.1 z.2
  have hKc : Continuous (fun z : ℝ × Icc 0 U => K z.1 z.2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro z
    exact mul_ne_zero (by norm_num) (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU
      z.2 (projIcc 0 V hV z.1)).2.2.1.ne
  have hG : Continuous G := continuous_const.sub hKc
  have hzero (u : Icc 0 U) : G (0, u) < 0 := by
    have hb := hrow 0 ⟨le_rfl, hV⟩ (by intro hbad; linarith only [hT, hbad]) u
    dsimp only [G]
    linarith only [hb]
  have hstrict : ∀ t ∈ Icc (0 : ℝ) V, ∀ u, G (t, u) < 0 := by
    apply continuous_prefix_bootstrap hG hzero
    intro t ht hpref u
    have hb := hrow t ht (fun _ q hq u => by
      have hh := hpref q hq u
      dsimp only [G] at hh
      linarith only [hh]) u
    dsimp only [G]
    linarith only [hb]
  have hk (u : Icc 0 U) (v : Icc 0 V) : (1 / 2 : ℝ) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) := by
    have hh := hstrict v v.property u
    simp only [G, hK v v.property u] at hh
    linarith only [hh]
  have hresult := hlate p hp f hf hfn hcb U V hU hV hUR hfU x hx hUU₁ hlo hk
  have hnhi (u : Icc 0 U) (v : Icc 0 V) : |ν u v| ≤ N * Real.exp (B.outerRate * v) := by
    rw [abs_of_neg (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU u v).2.2.1]
    exact (hresult.2.1 u v).2.2.2
  have hout (v : Icc 0 V) : Real.exp (c * v) * |h v| ≤ H := by
    have hh := mul_le_mul_of_nonneg_left (hb v) (Real.exp_pos (c * v)).le
    rw [Real.norm_eq_abs] at hh
    have he : Real.exp (c * v) * Real.exp (-s * v) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith only [mul_nonneg (sub_nonneg.2 hcs) v.property.1]
    nlinarith only [hh, mul_le_mul_of_nonneg_left he hH]
  have hscalar := hx.horizon_weighted_scalar hU hV hUR hc hi hrc hr0 hφ hrd hp hfU hA hfnU
    hc0.le hca hcb hY0 hN.le hL hH hD.le hlo hnhi (fun u v => (hresult.2.1 u v).2.1) hout hresult.1
  refine ⟨hresult.1, ?_, hscalar.2⟩
  intro u v
  obtain ⟨hr, hl, hnlo, hnup⟩ := hresult.2.1 u v
  refine ⟨hr, hl, hnlo, hnup, ?_, hscalar.1 u v⟩
  have hb := hrow v v.property (fun _ q hq u => by
    have hh := hstrict q ⟨hq.1, hq.2.trans v.property.2⟩ u
    dsimp only [G] at hh
    linarith only [hh]) u
  simpa only [hK v v.property u] using hb

end CauchyHorizon.Background
