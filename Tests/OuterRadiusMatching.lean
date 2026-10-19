import CauchyHorizon.Characteristic.OuterRadiusMatching

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Tests

-- The moving first moment retains the exponent b+1 and its signed coefficient b.
example {a b k u v : ℝ} (hb : 0 < b) (hu : 0 < u) (hcrit : k = a * b)
    (ℓ : ℝ) (P : ℝ →ᵇ ℝ) :
    Real.exp ((a + k) * v) * (∫ x in (0 : ℝ)..u, x * logarithmicIncoming b ℓ P x) =
      b * (u * Real.exp (a * v)) ^ (b + 1) *
        terminalGreen (by linarith : 0 < b + 1) P (ℓ - Real.log u) := by
  have hq : 0 < u * Real.exp (a * v) := mul_pos hu (Real.exp_pos _)
  simpa only [div_self hq.ne', Real.log_one, mul_zero, Real.exp_zero, mul_one] using
    logarithmicIncoming_phase_first_moment hb hu hq hcrit ℓ P (v := v)

-- At p=4, one near-event radius and derivative budget control both actual trace errors.
example (B : Background) {s H dH A Ecap cap ε : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hEcap : 0 ≤ Ecap) (hcap : 0 < cap) (hε : 0 < ε) (hks : B.outerRate * (3 / 4) < s)
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
    ∃ δ Y T η : ℝ, 0 < δ ∧ Y ∈ Ioo B.inner B.event ∧ B.event - cap < Y ∧ 0 < T ∧ 0 < η ∧
      ∀ (ℓ : ℝ) (P D : ℝ →ᵇ ℝ), Integrable (fun t => P t ^ 2) → (∫ t, P t ^ 2) ≤ Ecap →
        (∀ t, HasDerivAt P (D t) t) → Integrable (fun t => D t ^ 2) → (∫ t, D t ^ 2) ≤ η →
        MemLp (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧
          ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hf : MemLp (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
            (_hx : IsWaveIntegral hU hV B.charge B.cosmological
              (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR le_rfl hf) x), U ≤ δ →
            (∀ t ∈ Ici T, g t ≤ U → t ≤ V →
              intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 = Y) ∧
            let φ := fun t => B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Y)
            let Cθ := (B.outerRate / B.event) * r 0 * cν * (3 / 7) * (B.z Y / cν) ^ (7 / 4 : ℝ)
            let Cζ := (3 / 4 : ℝ) * r 0 * (B.z Y / cν) ^ (3 / 4 : ℝ)
            let Eθ := fun t => Real.exp ((B.outerRate * (3 / 4)) * t) *
              (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1) - Cθ * P (φ t)
            let Eζ := fun t => g t * Real.exp ((B.outerRate * (3 / 4)) * t) *
              (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                  (Icc 0 U) (g t)) - Cζ * P (φ t)
            ∀ l S : ℝ, T ≤ l → l ≤ S → S ≤ V → g l ≤ U →
              IntegrableOn (fun t => Eθ t ^ 2) (Icc l S) ∧
                IntegrableOn (fun t => Eζ t ^ 2) (Icc l S) ∧
                (∫ t in l..S, Eθ t ^ 2) / δ ^ (7 / 2 : ℝ) +
                  (∫ t in l..S, Eζ t ^ 2) / δ ^ (3 / 2 : ℝ) ≤ ε := by
  intro hi hr0 cν
  obtain ⟨α, hα, hfamily⟩ := B.exists_outer_radius_matching
    hs hH hdH hdHR hA (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    rfl hks hc hb hrc hrb hrinit hrd hrdec hOut
  let e := ε / (2 * (1 + Ecap))
  have he : 0 < e := by dsimp only [e]; positivity
  obtain ⟨δ, Y, T, L, hδ, hδcap, _hδ1, hYeq, hY, hT, hL, hsolve⟩ :=
    hfamily (cap / α) e (div_pos hcap hα) he
  have hYcap : B.event - cap < Y := by
    have hh := (lt_div_iff₀ hα).1 hδcap
    rw [hYeq]
    nlinarith only [hh]
  let η := ε / (2 * L)
  have hη : 0 < η := by dsimp only [η]; positivity
  refine ⟨δ, Y, T, η, hδ, hY, hYcap, hT, hη, ?_⟩
  intro ℓ P D hP hPE hd hD hDE hfδ hfnδ
  obtain ⟨g, hgc, _hga, _hgl, _hg0, hmatch⟩ := hsolve 4 le_rfl ℓ P D (by norm_num) hP hd hD hfδ hfnδ
  refine ⟨g, hgc, ?_⟩
  intro U V hU hV hUR hf x hx hUδ
  have hh := hmatch U V hU hV hUR hf x hx hUδ
  refine ⟨hh.1, ?_⟩
  intro φ Cθ Cζ Eθ Eζ l S hl hlS hSV hglU
  have hcθ : (B.outerRate / B.event) * r 0 * cν * (3 / 4 : ℝ) *
      (B.z Y / cν) ^ ((3 / 4 : ℝ) + 1) / ((3 / 4 : ℝ) + 1) = Cθ := by
    dsimp only [Cθ]
    rw [show (3 / 4 : ℝ) + 1 = 7 / 4 by norm_num]
    ring
  have hbound := hh.2 l S hl hlS hSV hglU
  dsimp only at hbound
  rw [hcθ] at hbound
  have hsmall : e * (1 + ∫ t, P t ^ 2) + L * (∫ t, D t ^ 2) ≤ ε := by
    have hEP : 1 + (∫ t, P t ^ 2) ≤ 1 + Ecap := by linarith only [hPE]
    have hbudget := add_le_add (mul_le_mul_of_nonneg_left hEP he.le) (mul_le_mul_of_nonneg_left hDE hL.le)
    have heq : e * (1 + Ecap) + L * η = ε := by dsimp only [e, η]; field_simp; ring
    exact hbudget.trans_eq heq
  refine ⟨hbound.1, hbound.2.1, ?_⟩
  simpa only [show (2 : ℝ) * ((3 / 4 : ℝ) + 1) = 7 / 2 by norm_num,
    show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] using hbound.2.2.trans hsmall

end CauchyHorizon.Tests
