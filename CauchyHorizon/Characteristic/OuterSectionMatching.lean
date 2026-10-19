import CauchyHorizon.Characteristic.OuterTransverseComparison

/-! Both actual scalar traces match their signed outer profiles on one common scaled section. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_outer_section_matching (B : Background) {s H dH A b k : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hbpos : 0 < b) (hb1 : b < 1) (hcrit : k = B.outerRate * b) (hks : k < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∀ cap ε : ℝ, 0 < cap → 0 < ε →
      ∃ δ T : ℝ, 0 < δ ∧ δ < cap ∧ δ ≤ 1 ∧ 0 ≤ T ∧
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (P : ℝ →ᵇ ℝ)
          (_hkp : k ≤ B.outerRate * (1 - 1 / p.toReal)) (_hP : Integrable (fun t => P t ^ 2))
          (hf : MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x),
          (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))).toReal ≤ A →
          let g := fun t => δ * Real.exp (-B.outerRate * t)
          let Eθ := fun t => Real.exp (k * t) *
            (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
              intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1) -
            (B.outerRate / B.event) * r 0 * cν * b * δ ^ (b + 1) *
              terminalGreen (by linarith : 0 < b + 1) P (ℓ - Real.log δ + B.outerRate * t)
          let Eζ := fun t => g t * Real.exp (k * t) *
            (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
              derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                (Icc 0 U) (g t)) - b * r 0 * δ ^ b * P (ℓ - Real.log δ + B.outerRate * t)
          ∀ l S : ℝ, T ≤ l → l ≤ S → S ≤ V → g l ≤ U →
            IntegrableOn (fun t => Eθ t ^ 2) (Icc l S) ∧
              IntegrableOn (fun t => Eζ t ^ 2) (Icc l S) ∧
              (∫ t in l..S, Eθ t ^ 2) / δ ^ (2 * (b + 1)) +
                (∫ t in l..S, Eζ t ^ 2) / δ ^ (2 * b) ≤ ε * (1 + ∫ t, P t ^ 2) := by
  intro hi hr0 cν
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  obtain ⟨δ₀, K, hδ₀, hK, htrans⟩ := B.exists_outer_transverse_comparison
    hs hH hdH hdHR hA hbpos hb1 hcrit hks hc hb hrc hrb hrd hrdec hOut
  let m := 2 * (1 - b)
  have hm : 0 < m := by dsimp only [m]; linarith only [hb1]
  let L := fun d : ℝ => 2 * K * d ^ m + 2 * b ^ 2 / a * d ^ (2 : ℕ)
  intro cap ε hcap hε
  have hLc : Continuous L :=
    ((Real.continuous_rpow_const hm.le).const_mul (2 * K)).add ((continuous_id.pow 2).const_mul (2 * b ^ 2 / a))
  have hsmall : ∀ᶠ d in 𝓝 (0 : ℝ), L d < ε / 2 := hLc.continuousAt.tendsto.eventually_lt_const
    (by simpa only [L, Real.zero_rpow hm.ne', zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using half_pos hε)
  obtain ⟨δs, hδs, hsmall⟩ := hsmall.exists_gt
  obtain ⟨δ, T, hδ, hδcap, hδ1, hT, hmoment⟩ := B.exists_outer_radiation_moment_comparison
    hs hH hdH hdHR hA hbpos hb1 hcrit hks hc hb hrc hrb hrd hrdec hOut
    (min cap (min δ₀ δs)) (ε / 2) (by positivity) (half_pos hε)
  have hδ₀' : δ ≤ δ₀ := hδcap.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδs' : δ ≤ δs := hδcap.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLδ : L δ ≤ ε / 2 := (add_le_add
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδs' hm.le) (by positivity))
    (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hδ.le hδs.le).2 hδs') (by positivity))).trans hsmall.le
  refine ⟨δ, T, hδ, hδcap.trans_le (min_le_left _ _), hδ1, hT, ?_⟩
  intro U V hU hV hUR p hp ℓ P hkp hP hf x hx hfn g Eθ Eζ l S hl hlS hSV hgl
  have hl0 : 0 ≤ l := hT.trans hl
  have hgc : Continuous g := by dsimp only [g]; fun_prop
  have hg (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Ioc 0 U ∧ g t * Real.exp (a * t) ≤ δ := by
    have hgt : g t ≤ g l := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.2 ha.le))) hδ.le
    refine ⟨⟨mul_pos hδ (Real.exp_pos _), hgt.trans hgl⟩, ?_⟩
    simp only [g, a, mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one, le_refl]
  have hgu (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Icc 0 U := ⟨(hg t ht).1.1.le, (hg t ht).1.2⟩
  have htv (t : ℝ) (ht : t ∈ Icc l S) : t ∈ Icc 0 V := ⟨hl0.trans ht.1, ht.2.trans hSV⟩
  let Q := fun t => Real.exp (k * t) *
    (x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 *
      x.2.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 1 -
      (a / B.event) * r 0 * (cν * Real.exp (a * projIcc 0 V hV t)) *
        ∫ w in (0 : ℝ)..(projIcc 0 U hU (g t) : ℝ), w * logarithmicIncoming b ℓ P w)
  have hQ := hmoment U V hU hV hUR p hp ℓ P hkp hP hf x hx hfn
    l S g hl hlS hSV hgc.continuousOn (fun t ht => ⟨hgu t ht, (hg t ht).2⟩)
  have hθeq (t : ℝ) (ht : t ∈ Icc l S) : Q t = Eθ t := by
    dsimp only [Q, Eθ, intervalExtension_apply]
    rw [mul_sub]
    congr 1
    rw [projIcc_of_mem hV (htv t ht), projIcc_of_mem hU (hgu t ht)]
    calc
      _ = ((a / B.event) * r 0 * cν) * (Real.exp ((a + k) * t) *
          ∫ w in (0 : ℝ)..(g t), w * logarithmicIncoming b ℓ P w) := by
        rw [add_mul, Real.exp_add]; ring
      _ = _ := by rw [logarithmicIncoming_scaled_first_moment hbpos hδ hcrit ℓ P t]; ring
  have hθi : IntegrableOn (fun t => Eθ t ^ 2) (Icc l S) := by
    apply hQ.1.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact congrArg (fun q : ℝ => q ^ 2) (hθeq t ht)
  have hθe : (∫ t in l..S, Eθ t ^ 2) / δ ^ (2 * (b + 1)) ≤ (ε / 2) * (1 + ∫ t, P t ^ 2) := by
    have hI : (∫ t in l..S, Q t ^ 2) = ∫ t in l..S, Eθ t ^ 2 :=
      intervalIntegral.integral_congr (fun t ht => congrArg (fun q : ℝ => q ^ 2)
        (hθeq t (by simpa only [uIcc_of_le hlS] using ht)))
    have he : (∫ t in l..S, Q t ^ 2) ≤ (ε / 2) * δ ^ (2 * (b + 1)) * (1 + ∫ t, P t ^ 2) := hQ.2
    rw [hI] at he
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hδ _)).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using he
  let E := fun t => g t * Real.exp (k * t) *
    (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
      derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
        (Icc 0 U) (g t) - (r 0 - g t) * logarithmicIncoming b ℓ P (g t))
  let R := fun t => b * g t * δ ^ b * P (ℓ - Real.log δ + a * t)
  have hE := htrans δ hδ hδ₀' U V hU hV hUR p hp ℓ P hkp hP hf x hx hfn
    l S g hl0 hlS hSV hgc.continuousOn hg
  have hR := logarithmicIncoming_radius_error_energy (b := b) ha hδ hl0 hlS ℓ P hP
  have hζeq (t : ℝ) : Eζ t = E t - R t := by
    have hh := logarithmicIncoming_scaled_trace hδ hcrit ℓ P t
    change g t * Real.exp (k * t) * logarithmicIncoming b ℓ P (g t) =
      b * δ ^ b * P (ℓ - Real.log δ + a * t) at hh
    dsimp only [Eζ, E, R]
    nlinarith only [congrArg (fun q : ℝ => (r 0 - g t) * q) hh]
  have hfc : ContinuousOn (logarithmicIncoming b ℓ P) (Ioi 0) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl ht.ne'))
    · exact P.continuous.comp_continuousOn
        (continuousOn_const.sub (continuousOn_id.log (fun t ht => ht.ne')))
  have hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 0 = -1 := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]; rfl
  have hif : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      incomingWaveVelocity hUR hp hf u 1 = logarithmicIncoming b ℓ P u := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]; rfl
  have hZc := hx.scalar_curve_continuous rfl hinu hfc hif hgc.continuousOn continuousOn_id
    (fun t ht => (hg t ht).1)
  have hζc : ContinuousOn Eζ (Icc l S) := by
    dsimp only [Eζ]
    exact ((by fun_prop : ContinuousOn (fun t => g t * Real.exp (k * t)) (Icc l S)).mul hZc).sub
      (by fun_prop)
  have hζi : IntegrableOn (fun t => Eζ t ^ 2) (Icc l S) := (hζc.pow 2).integrableOn_Icc
  have hEi : IntervalIntegrable (fun t => E t ^ 2) volume l S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hE.1
  have hRi : IntervalIntegrable (fun t => R t ^ 2) volume l S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hR.1
  have hsum := intervalIntegral.integral_mono_on (μ := volume) hlS
    ((hζc.pow 2).intervalIntegrable_of_Icc hlS) ((hEi.const_mul 2).add (hRi.const_mul 2))
    (fun t _ => show Eζ t ^ 2 ≤ 2 * E t ^ 2 + 2 * R t ^ 2 from by
      rw [hζeq]; nlinarith only [sq_nonneg (E t + R t)])
  rw [intervalIntegral.integral_add (hEi.const_mul 2) (hRi.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hsum
  have hζbound : (∫ t in l..S, Eζ t ^ 2) ≤
      2 * (K * δ ^ 2 * (1 + ∫ t, P t ^ 2)) + 2 * ((b * δ ^ (b + 1)) ^ 2 / a * ∫ t, P t ^ 2) :=
    hsum.trans (add_le_add (mul_le_mul_of_nonneg_left hE.2.1 (by norm_num))
      (mul_le_mul_of_nonneg_left hR.2 (by norm_num)))
  have hpw : δ ^ (2 : ℕ) / δ ^ (2 * b) = δ ^ m := by
    rw [← Real.rpow_natCast δ 2, ← Real.rpow_sub hδ]
    congr 1; dsimp only [m]; ring
  have hrad : (δ ^ (b + 1)) ^ (2 : ℕ) / δ ^ (2 * b) = δ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (δ ^ (b + 1)) 2, ← Real.rpow_mul hδ.le, ← Real.rpow_sub hδ]
    norm_num only [Nat.cast_ofNat]
    rw [show (b + 1) * 2 - 2 * b = 2 by ring]
    norm_num
  have hPI : 0 ≤ ∫ t, P t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  have hζe : (∫ t in l..S, Eζ t ^ 2) / δ ^ (2 * b) ≤ (ε / 2) * (1 + ∫ t, P t ^ 2) := by
    calc
      _ ≤ (2 * (K * δ ^ 2 * (1 + ∫ t, P t ^ 2)) +
          2 * ((b * δ ^ (b + 1)) ^ 2 / a * ∫ t, P t ^ 2)) / δ ^ (2 * b) :=
        div_le_div_of_nonneg_right hζbound (Real.rpow_nonneg hδ.le _)
      _ = 2 * K * δ ^ m * (1 + ∫ t, P t ^ 2) + 2 * b ^ 2 / a * δ ^ 2 * ∫ t, P t ^ 2 := by
        rw [← hpw, ← hrad]; ring
      _ ≤ L δ * (1 + ∫ t, P t ^ 2) := by
        dsimp only [L]
        nlinarith only [show 0 ≤ 2 * b ^ 2 / a * δ ^ 2 by positivity]
      _ ≤ _ := mul_le_mul_of_nonneg_right hLδ (by positivity)
  exact ⟨hθi, hζi, (add_le_add hθe hζe).trans_eq (by ring)⟩

end CauchyHorizon.Background
