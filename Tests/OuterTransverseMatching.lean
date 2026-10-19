import CauchyHorizon.Characteristic.OuterTransverseMatching

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Tests

-- Normalizing by the actual moving width removes the phase-amplitude factor exactly.
example {a b k u v : ℝ} (hu : 0 < u) (hcrit : k = a * b) (ℓ : ℝ) (P : ℝ → ℝ) :
    u * Real.exp (k * v) * logarithmicIncoming b ℓ P u =
      b * (u * Real.exp (a * v)) ^ b * P (ℓ - Real.log u) := by
  have hq : 0 < u * Real.exp (a * v) := mul_pos hu (Real.exp_pos _)
  simpa only [div_self hq.ne', Real.log_one, mul_zero, Real.exp_zero, mul_one] using
    logarithmicIncoming_phase_trace hu hq hcrit ℓ P (v := v)

-- A common p = 4 width and time make the normalized error arbitrarily small up to derivative energy.
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
    ∃ δ Y T L : ℝ, 0 < δ ∧ δ < cap ∧ Y ∈ Ioo B.inner B.event ∧ 0 < T ∧ 0 < L ∧
      ∀ (ℓ : ℝ) (P D : ℝ →ᵇ ℝ), Integrable (fun t => P t ^ 2) →
        (∫ t, P t ^ 2) ≤ Ecap → (∀ t, HasDerivAt P (D t) t) → Integrable (fun t => D t ^ 2) →
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
            let C := (3 / 4 : ℝ) * r 0 * (B.z Y / cν) ^ (3 / 4 : ℝ)
            let E := fun t => g t * Real.exp ((B.outerRate * (3 / 4)) * t) *
              (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                  (Icc 0 U) (g t)) -
              C * P (B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Y))
            ∀ l S : ℝ, T ≤ l → l ≤ S → S ≤ V → g l ≤ U →
              IntegrableOn (fun t => E t ^ 2) (Icc l S) ∧
                (∫ t in l..S, E t ^ 2) / δ ^ (3 / 2 : ℝ) ≤ ε + L * ∫ t, D t ^ 2 := by
  intro hi hr0 cν
  have ha := B.outerRate_pos
  obtain ⟨δ₀, α, K, hδ₀, _hδ₀r, _hα, hK, hfamily⟩ := B.exists_outer_transverse_matching
    hs hH hdH hdHR hA (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    rfl hks hc hb hrc hrb hrinit hrd hrdec hOut
  let M := fun d : ℝ => K * d ^ (1 / 2 : ℝ) * (1 + Ecap)
  have hMc : Continuous M := by dsimp only [M]; fun_prop (disch := norm_num)
  have hsmall : ∀ᶠ d in 𝓝 (0 : ℝ), M d < ε / 2 := hMc.continuousAt.tendsto.eventually_lt_const (by
    simpa only [M, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_zero, zero_mul] using half_pos hε)
  obtain ⟨d, hd, hMd⟩ := hsmall.exists_gt
  let δ := min δ₀ (min (cap / 2) d)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (half_pos hcap) hd)
  have hδcap : δ < cap := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hcap)
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδd : δ ≤ d := (min_le_right _ _).trans (min_le_right _ _)
  have hMδ : M δ ≤ ε / 2 := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδd (by norm_num : (0 : ℝ) ≤ 1 / 2)) hK.le)
    (by positivity : 0 ≤ 1 + Ecap)).trans hMd.le
  obtain ⟨Y, T₀, τ, _hYeq, hY, hT₀, hτ, hsolve⟩ := hfamily δ hδ hδ₀'
  let η : Ioi (0 : ℝ) := ⟨ε / (2 * (1 + Ecap)),
    show (0 : ℝ) < ε / (2 * (1 + Ecap)) from div_pos hε (by positivity)⟩
  let T := τ η
  have hT : 0 < T := hT₀.trans_le (hτ η)
  let C := (3 / 4 : ℝ) * r 0 * (B.z Y / cν) ^ (3 / 4 : ℝ)
  let L := 6 * C ^ 2 / (B.outerRate * δ ^ (3 / 2 : ℝ))
  have hC : 0 < C := by
    have hrp := B.inner_pos.trans hrinit
    have hq : 0 < B.z Y / cν := div_pos (B.z_pos hY) (Real.exp_pos _)
    dsimp only [C]
    positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨δ, Y, T, L, hδ, hδcap, hY, hT, hL, ?_⟩
  intro ℓ P D hP hPE hdP hD hfδ hfnδ
  obtain ⟨g, hgc, _hga, _hgl, _hg0, _hphase, hmatch⟩ := hsolve 4 le_rfl ℓ P D
    (by norm_num) hP hdP hD hfδ hfnδ
  refine ⟨g, hgc.mono (Ici_subset_Ici.2 (hτ η)), ?_⟩
  intro U V hU hV hUR hf x hx hUδ
  have hm := hmatch U V hU hV hUR hf x hx hUδ
  refine ⟨fun t ht => hm.1 t ((hτ η).trans ht), ?_⟩
  intro C' E l S hl hlS hSV hglU
  have hh := hm.2 η l S hl hlS hSV hglU
  have hηE : (η : ℝ) * (∫ t, P t ^ 2) ≤ ε / 2 := by
    have hηpos : 0 ≤ (η : ℝ) := η.property.le
    have he : (η : ℝ) * (1 + Ecap) = ε / 2 := by dsimp only [η]; field_simp
    exact (mul_le_mul_of_nonneg_left (hPE.trans (le_add_of_nonneg_left zero_le_one)) hηpos).trans_eq he
  have hfirst : K * δ ^ (2 * (1 - (3 / 4 : ℝ))) * (1 + ∫ t, P t ^ 2) ≤ ε / 2 := by
    rw [show 2 * (1 - (3 / 4 : ℝ)) = 1 / 2 by norm_num]
    have henergy : 1 + (∫ t, P t ^ 2) ≤ 1 + Ecap := by linarith only [hPE]
    exact (mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ K * δ ^ (1 / 2 : ℝ))).trans hMδ
  refine ⟨hh.1, ?_⟩
  have hbnd := hh.2.trans (add_le_add (add_le_add hfirst hηE) le_rfl)
  simpa only [show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num, L,
    show ε / 2 + ε / 2 = ε by ring] using hbnd

end CauchyHorizon.Tests
