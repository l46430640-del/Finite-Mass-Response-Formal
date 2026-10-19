import CauchyHorizon.Characteristic.OuterModeMatching

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Tests

-- Unit horizon amplitude and R=r_plus give precisely the radial-mode normalization.
example (B : Background) {y : ℝ} (hy : y ∈ Ioo B.inner B.event) :
    let b := B.criticalExponent
    (B.outerRate / B.event) * B.event * b * B.z y ^ (b + 1) / (b + 1) =
      B.innerRate / (b + 1) * B.z y ^ (b + 1) ∧
      (b * B.event * B.z y ^ b) / B.criticalWeight y = B.event * b := by
  simpa only [Real.one_rpow, mul_one, div_one, div_self B.event_pos.ne', one_mul] using
    B.outer_matching_coefficients hy zero_lt_one (R := B.event)

-- At the p=4 endpoint, all choices precede the packet and both mode errors are small.
example (B : Background) {s H dH A Ecap cap ε : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hEcap : 0 ≤ Ecap) (hcap : 0 < cap) (hε : 0 < ε)
    (hbcrit : B.criticalExponent = 3 / 4) (hks : B.innerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hb1 : B.criticalExponent < 1 := by rw [hbcrit]; norm_num
    let b := B.criticalExponent
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    let Ch := r 0 / (B.event * cν ^ b)
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb1).1 (B.event - y)
    let Vmode := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb1).2 (B.event - y)
    ∃ δ Y T η : ℝ, 0 < δ ∧ δ < cap ∧ Y ∈ Ioo B.inner B.event ∧ B.event - cap < Y ∧ 0 < T ∧ 0 < η ∧
      ∀ (ℓ : ℝ) (P D : ℝ →ᵇ ℝ), Integrable (fun t => P t ^ 2) → (∫ t, P t ^ 2) ≤ Ecap →
        (∀ t, HasDerivAt P (D t) t) → Integrable (fun t => D t ^ 2) → (∫ t, D t ^ 2) ≤ η →
        MemLp (logarithmicIncoming b ℓ P) 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm (logarithmicIncoming b ℓ P) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧
          ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hf : MemLp (logarithmicIncoming b ℓ P) 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
            (_hx : IsWaveIntegral hU hV B.charge B.cosmological
              (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR le_rfl hf) x), U ≤ δ →
            (∀ t ∈ Ici T, g t ≤ U → t ≤ V →
              intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 = Y) ∧
            let φ := fun t => B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Y)
            let Eθ := fun t => Real.exp (B.innerRate * t) *
              (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1) - Ch * X Y * P (φ t)
            let Eζ := fun t => (g t * Real.exp (B.innerRate * t) *
              (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                  (Icc 0 U) (g t))) / B.criticalWeight Y - Ch * Vmode Y * P (φ t)
            ∀ l S : ℝ, T ≤ l → l ≤ S → S ≤ V → g l ≤ U →
              IntegrableOn (fun t => Eθ t ^ 2) (Icc l S) ∧
                IntegrableOn (fun t => Eζ t ^ 2) (Icc l S) ∧
                (∫ t in l..S, Eθ t ^ 2) + (∫ t in l..S, Eζ t ^ 2) ≤ ε := by
  intro hb1 b hi hr0 cν Ch X Vmode
  obtain ⟨_α, _hα, hfamily⟩ := B.exists_outer_mode_matching
    hs hH hdH hdHR hA hb1 hks hc hb hrc hrb hrinit hrd hrdec hOut
  let e := ε / (2 * (1 + Ecap))
  have he : 0 < e := by dsimp only [e]; positivity
  obtain ⟨δ, Y, T, L, hδ, hδcap, _hδ1, _hYeq, hY, hYcap, hT, hL, hsolve⟩ := hfamily cap e hcap he
  let η := ε / (2 * L)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hcrit : B.innerRate = B.outerRate * (3 / 4) := by
    have hh : B.outerRate * B.criticalExponent = B.innerRate := by
      dsimp only [Background.criticalExponent]
      field_simp [B.outerRate_pos.ne']
    rw [hbcrit] at hh
    exact hh.symm
  have hkp : B.innerRate ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    rw [hcrit]
    norm_num
  refine ⟨δ, Y, T, η, hδ, hδcap, hY, hYcap, hT, hη, ?_⟩
  intro ℓ P D hP hPE hd hD hDE hfδ hfnδ
  obtain ⟨g, hgc, _hga, _hgl, _hg0, hmatch⟩ := hsolve 4 le_rfl ℓ P D hkp hP hd hD hfδ hfnδ
  refine ⟨g, hgc, ?_⟩
  intro U V hU hV hUR hf x hx hUδ
  have hh := hmatch U V hU hV hUR hf x hx hUδ
  refine ⟨hh.1, ?_⟩
  intro φ Eθ Eζ l S hl hlS hSV hglU
  have hbound := hh.2 l S hl hlS hSV hglU
  have hsmall : e * (1 + ∫ t, P t ^ 2) + L * (∫ t, D t ^ 2) ≤ ε := by
    have hEP : 1 + (∫ t, P t ^ 2) ≤ 1 + Ecap := by linarith only [hPE]
    have hbudget := add_le_add (mul_le_mul_of_nonneg_left hEP he.le) (mul_le_mul_of_nonneg_left hDE hL.le)
    have heq : e * (1 + Ecap) + L * η = ε := by dsimp only [e, η]; field_simp; ring
    exact hbudget.trans_eq heq
  exact ⟨hbound.1, hbound.2.1, hbound.2.2.trans hsmall⟩

end CauchyHorizon.Tests
