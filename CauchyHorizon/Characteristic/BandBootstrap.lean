import CauchyHorizon.Characteristic.BandWidth
import CauchyHorizon.Characteristic.BoundedWidthGeometry
import CauchyHorizon.Characteristic.WeightedScalar

/-! Late quadratic improvement with the width and nu budgets discharged. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon.Background

theorem exists_band_improvement (B : Background) {s H dH A c η : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s) (hη : 0 < η)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ U₀ T D n N L : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ 0 ≤ T ∧ 0 < D ∧ 0 < n ∧ 0 < N ∧ 0 ≤ L ∧
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
            (∀ u v, (1 / 2 : ℝ) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
            U * Real.exp (B.outerRate * V) ≤ D ∧
            (∀ u v, x.1 u v 0 ≤ B.event + dH ∧ |x.2.1 u v 0| ≤ L ∧
              n * Real.exp (B.outerRate * v) ≤ -ν u v ∧ -ν u v ≤ N * Real.exp (B.outerRate * v)) ∧
            (T ≤ V → ∀ u : Icc 0 U,
              let v : Icc 0 V := ⟨V, hV, le_rfl⟩
              (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
                (-intervalExtension hU ν t v)) ≤ η ∧
              Real.exp (-η) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧
              |massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v - horizonMass B.mass h V| ≤
                ((B.event + dH) * L / 2) * (Real.exp η - 1)) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, hδr, hR, hwidth⟩ := B.exists_band_width hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, ?_⟩
  intro Y hY hYR
  have hY0 : 0 < Y := B.inner_pos.trans hY
  have hYR' : Y ≤ B.event + dH := by linarith only [hYR, hR.2, hdH]
  have hR0 : 0 ≤ B.event + dH := hY0.le.trans hYR'
  obtain ⟨U₁, D, hU₁, hU₁δ, hD, hwide⟩ := hwidth Y hY hYR
  obtain ⟨U₂, n, N, L, hU₂, _hU₂r, hn, hN, hL, hgeom⟩ :=
    B.exists_bounded_width_geometry (D := D) hs hH hdH hdHR hA hY0 hYR' hc hb hrc hrb hrd hrdec hOut
  obtain ⟨T, hT, hlate⟩ := exists_late_weighted_feedback hc hi hrc hr0 hφ hrd hc0 hca
    hY0 hR0 hn hN.le hL hH hA hD.le hη
  refine ⟨min U₁ U₂, T, D, n, N, L, lt_min hU₁ hU₂, (min_le_left _ _).trans hU₁δ,
    hT, hD, hn, hN, hL, ?_⟩
  intro p hp f hf hfn hcb U V hU hV hUR hfU x hx
  dsimp only
  intro hUU hlo hk
  have hUU₁ := hUU.trans (min_le_left _ _)
  have hUU₂ := hUU.trans (min_le_right _ _)
  have hfnU := (scalar_prefix_norm_le (hUU₁.trans hU₁δ) hf).trans hfn
  have hw := hwide p hp f hf hfn U V hU hV hUR hfU x hx hUU₁ hlo hk
  have hg := hgeom U V hU hV hUR p hp f hfU x hx hfnU hUU₂ hlo hw
  refine ⟨hw, hg, ?_⟩
  intro hTV u
  have hnhi (u : Icc 0 U) (v : Icc 0 V) : |radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose u v| ≤ N * Real.exp (B.outerRate * v) := by
    rw [abs_of_neg (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU u v).2.2.1]
    exact (hg u v).2.2.2
  have hout (v : Icc 0 V) : Real.exp (c * v) * |h v| ≤ H := by
    have hh := mul_le_mul_of_nonneg_left (hb v) (Real.exp_pos (c * v)).le
    rw [Real.norm_eq_abs] at hh
    have he : Real.exp (c * v) * Real.exp (-s * v) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith only [mul_nonneg (sub_nonneg.2 hcs) v.property.1]
    nlinarith only [hh, mul_le_mul_of_nonneg_left he hH]
  exact hlate U V hU hV hUR p hp f hfU x hx hfnU hcb hlo (fun u v => (hg u v).1)
    (fun u v => (hg u v).2.2.1) hnhi (fun u v => (hg u v).2.1) hout hw hTV u

end CauchyHorizon.Background
