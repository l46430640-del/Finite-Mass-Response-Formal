import CauchyHorizon.Characteristic.BandGrowth
import CauchyHorizon.Characteristic.OuterModeMatching
import CauchyHorizon.Analysis.LogarithmicRegularity

/-! Outer matching and actual band propagation on the same scalar field and radius chart. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 2400000 in
theorem exists_matched_band_energy (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hm : B.criticalExponent < 1) (hks : B.innerRate < s)
    {h rH : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous rH) (hrb : ∀ t, B.event - dH ≤ rH t) (hrinit : B.inner < rH 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt rH
      (horizonFunction (rH t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖rH t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h rH s) :
    let b := B.criticalExponent
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (rH t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    let Ch := rH 0 / (B.event * cν ^ b)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y cap e : ℝ, B.inner < Y → Y ≤ R → 0 < cap → 0 < e →
        ∃ Z U₀ C L : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ,
          Z ∈ Ioo Y B.event ∧ B.event - cap < Z ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < C ∧ 0 < L ∧
          ∀ (p₀ : ℝ≥0∞) (hp₀ : 4 ≤ p₀) (ℓ : ℝ) (P Q : ℝ →ᵇ ℝ),
            B.innerRate ≤ B.outerRate * (1 - 1 / p₀.toReal) → Integrable (fun t => P t ^ 2) →
            (∀ t, HasDerivAt P (Q t) t) → Integrable (fun t => Q t ^ 2) →
            MemLp (logarithmicIncoming b ℓ P) p₀ (volume.restrict (Icc 0 δ)) →
            (eLpNorm (logarithmicIncoming b ℓ P) p₀ (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < rH 0), U ≤ U₀ →
              ∀ (hfU : MemLp (logarithmicIncoming b ℓ P) p₀ (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h rH 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp₀ hfU) x),
                ∀ (ε : Ioi (0 : ℝ)) (hUp : 0 < U) (l S : ℝ), τ ε ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                  let D := Icc (0 : ℝ) (Z - Y) ×ˢ Icc l S
                  let zIn := incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h rH 0)
                  let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
                  ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ D ∧
                    (∀ z ∈ D, χ z ∈ Ioo 0 U ∧
                      x.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0 = Z - z.1) ∧
                    let u := fun z : ℝ × ℝ => projIcc 0 U hU (χ z)
                    let v := fun z : ℝ × ℝ => projIcc 0 V hV z.2
                    let ρ := fun z => x.1 (u z) (v z) 0
                    let Lm := fun z => x.2.1 (u z) (v z) 0
                    let ζ := fun z => zIn (u z) 0 * logarithmicIncoming b ℓ P (χ z) + scalarTransportCorrection hV ν x.2.1 (u z) (v z)
                    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - y)
                    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - y)
                    let φ := fun t => B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Z)
                    let P₀ := fun t => Ch * P (φ t)
                    let p := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * (ρ z * x.2.1 (u z) (v z) 1) - X (ρ z) * P₀ z.2
                    let q := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * χ z * ζ z / B.criticalWeight (ρ z) - W (ρ z) * P₀ z.2
                    let N := fun y => ∫ t in l..S, p (y, t) ^ 2 + q (y, t) ^ 2
                    Real.sqrt (N (Z - Y)) ≤
                      (Real.sqrt (e * (1 + ∫ t, P t ^ 2) + L * ∫ t, Q t ^ 2) +
                        Real.sqrt (∫ y in (0 : ℝ)..(Z - Y), (-1 / Lm (y, l)) * q (y, l) ^ 2) +
                        (Z - Y) * Real.sqrt (2 * (ε : ℝ) ^ 2 * (Ch ^ 2 / B.outerRate * ∫ t, P t ^ 2) +
                          2 * C ^ 2 * (Ch ^ 2 * B.outerRate * ∫ t, Q t ^ 2))) *
                            Real.exp (((∫ r in B.inner..B.event, B.energyGrowth r) + (ε : ℝ) * (Z - Y) + 1) / 2) := by
  intro b hi hr0 cν Ch
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have ha := B.outerRate_pos
  obtain ⟨δ, R, hδ, hR, hband⟩ := B.exists_band_reference_energy hm hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨α, _hα, houter⟩ := B.exists_outer_mode_matching hs hH hdH hdHR hA hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y cap e hY hYR hcap he
  let cap₀ := min cap (min δ (B.event - Y))
  have hcap₀ : 0 < cap₀ := lt_min hcap (lt_min hδ (sub_pos.2 (hYR.trans_lt hR.2)))
  obtain ⟨δo, Z, To, L, hδo, hδoc, _hδo1, _hZeq, hZ, hnear, _hTo, hL, hmatch⟩ := houter cap₀ e hcap₀ he
  have hδoδ : δo ≤ δ := hδoc.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hYZ : Y < Z := by
    have hh : cap₀ ≤ B.event - Y := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hnear, hh]
  obtain ⟨Ub, C, τb, hUb, hUbδ, hC, hsolve⟩ := hband Y Z hY hYZ hYR hZ.2
  have hz : Tendsto (fun t : ℝ => δo * Real.exp (-B.outerRate * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha))).const_mul δo
  have hwidth (W : Ioi (0 : ℝ)) : ∃ T : ℝ, ∀ t ≥ T, δo * Real.exp (-B.outerRate * t) < W :=
    eventually_atTop.1 (hz.eventually_lt_const W.property)
  choose TW hTW using hwidth
  let τ := fun ε W => max (τb ε W) (max To (TW W))
  refine ⟨Z, min Ub δo, C, L, τ, ⟨hYZ, hZ.2⟩, ?_, lt_min hUb hδo,
    (min_le_left _ _).trans hUbδ, hC, hL, ?_⟩
  · have hh : cap₀ ≤ cap := min_le_left _ _
    linarith only [hnear, hh]
  intro p₀ hp₀ ℓ P Q hcrit hPi hPQ hQi hf hfn
  let f := logarithmicIncoming b ℓ P
  have hP₁ : ContDiff ℝ 1 P := contDiff_one_iff_deriv.2 ⟨fun t => (hPQ t).differentiableAt, by
    have heq : deriv P = Q := funext (fun t => (hPQ t).deriv)
    rw [heq]
    exact Q.continuous⟩
  have hfc : ContDiffOn ℝ 1 f (Ioi 0) := logarithmicIncoming_contDiff hP₁ b ℓ
  have hfo := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hδoδ) le_rfl)
  have hfon := (scalar_prefix_norm_le hδoδ hf).trans hfn
  obtain ⟨g, _hgc, hga, _hglim, hgscale, hphysical⟩ := hmatch p₀ hp₀ ℓ P Q hcrit hPi hPQ hQi hfo hfon
  intro U V hU hV hUR hUU hfU x hx ε hUp l S hl hlS hSV D zIn ν
  have hbl : τb ε ⟨U, hUp⟩ ≤ l := (le_max_left _ _).trans hl
  have hTl : To ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hWl : TW ⟨U, hUp⟩ ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have hglU : g l ≤ U := by
    have hh := (hgscale l hTl).2
    calc
      g l = (g l * Real.exp (B.outerRate * l)) * Real.exp (-B.outerRate * l) := by
        rw [mul_assoc, ← Real.exp_add, show B.outerRate * l + -B.outerRate * l = 0 by ring,
          Real.exp_zero, mul_one]
      _ ≤ δo * Real.exp (-B.outerRate * l) := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
      _ ≤ U := (hTW ⟨U, hUp⟩ l hWl).le
  have hgU (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Ioc 0 U :=
    ⟨(hgscale t (hTl.trans ht.1)).1.1, (hga.antitoneOn hTl (hTl.trans ht.1) ht.1).trans hglU⟩
  have hm := hphysical U V hU hV hUR hfU x hx (hUU.trans (min_le_right _ _))
  have houterE := hm.2 l S hTl hlS hSV.le hglU
  obtain ⟨χ, hχc, hχhit, henergy⟩ := hsolve p₀ hp₀ f hf hfn hfc U V hU hV hUR
    (hUU.trans (min_le_left _ _)) hfU x hx ε hUp l S hbl hlS hSV
  refine ⟨χ, hχc, hχhit, ?_⟩
  intro u v ρ Lm ζ X W φ P₀ p q N
  have hφ₁ : ContDiff ℝ 1 φ := by dsimp only [φ]; fun_prop
  have hP₀ : ContDiff ℝ 1 P₀ := contDiff_const.mul (hP₁.comp hφ₁)
  have hprop := (henergy P₀ hP₀.contDiffOn).2.2
  have hinu := (incomingWave_constraint_data hU hUR hp₀ hfU (horizonPhi h rH 0)).1
  have hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp₀ hfU t 1 = f t := by
    filter_upwards [incomingWaveVelocity_ae hUR hp₀ hfU] with t ht
    rw [ht]; rfl
  have hχg (t : ℝ) (ht : t ∈ Icc l S) : χ (0, t) = g t := by
    have hχ := hχhit (0, t) ⟨⟨le_rfl, sub_nonneg.2 hYZ.le⟩, ht⟩
    have hg := hgU t ht
    have hr := hm.1 t (hTl.trans ht.1) hg.2 (ht.2.trans hSV.le)
    have hinj := hx.radial_strictAnti hx.choose rfl hinu (projIcc 0 V hV t)
      (fun w => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp₀ hfU w _).2.2.1)
    have hh := hinj.injective (hχ.2.trans ((by simpa only [intervalExtension_apply, sub_zero] using hr.symm)))
    simpa only [projIcc_of_mem hU ⟨hχ.1.1.le, hχ.1.2.le⟩,
      projIcc_of_mem hU ⟨hg.1.le, hg.2⟩] using congrArg Subtype.val hh
  let Eθ := fun t => Real.exp (B.innerRate * t) *
    (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
      intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1) - Ch * X Z * P (φ t)
  let Eζ := fun t => (g t * Real.exp (B.innerRate * t) *
    (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
      derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
        (Icc 0 U) (g t))) / B.criticalWeight Z - Ch * W Z * P (φ t)
  have hpq (t : ℝ) (ht : t ∈ Icc l S) : p (0, t) = Eθ t ∧ q (0, t) = Eζ t := by
    have hg := hgU t ht
    have hρ : ρ (0, t) = Z := by simpa only [sub_zero] using (hχhit (0, t) ⟨⟨le_rfl, sub_nonneg.2 hYZ.le⟩, ht⟩).2
    have hd := hx.scalar_hasDerivWithinAt_of_continuous rfl hinu hfc.continuousOn hif hg (projIcc 0 V hV t)
    have hdd := hd.derivWithin ((uniqueDiffOn_Icc hUp) _ ⟨hg.1.le, hg.2⟩)
    simp only [intervalExtension_apply] at hdd
    have hρg : x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 = Z := by
      simpa only [ρ, u, v, hχg t ht] using hρ
    constructor
    · dsimp only [p, Eθ, P₀]
      rw [hρ]
      simp only [u, v, hχg t ht, intervalExtension_apply, hρg]
      ring
    · dsimp only [q, Eζ, P₀]
      rw [hρ]
      simp only [ζ, u, v, hχg t ht, intervalExtension_apply]
      rw [hdd, projIcc_of_mem hU ⟨hg.1.le, hg.2⟩, mul_div_cancel₀ _ (hx.choose _ _)]
      ring
  have hN₀ : N 0 ≤ e * (1 + ∫ t, P t ^ 2) + L * ∫ t, Q t ^ 2 := by
    have hθi : IntervalIntegrable (fun t => Eθ t ^ 2) volume l S :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 houterE.1
    have hζi : IntervalIntegrable (fun t => Eζ t ^ 2) volume l S :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 houterE.2.1
    calc
      N 0 = ∫ t in l..S, Eθ t ^ 2 + Eζ t ^ 2 := intervalIntegral.integral_congr (fun t ht => by
        have hh := hpq t (by simpa only [uIcc_of_le hlS] using ht)
        rw [hh.1, hh.2])
      _ = (∫ t in l..S, Eθ t ^ 2) + ∫ t in l..S, Eζ t ^ 2 := intervalIntegral.integral_add hθi hζi
      _ ≤ _ := houterE.2.2
  have hφd (t : ℝ) : HasDerivAt φ B.outerRate t := by
    exact (((((hasDerivAt_id t).const_mul B.outerRate).add_const ℓ).add_const
      (Real.log cν)).sub_const (Real.log (B.z Z))).congr_deriv (by simp)
  have hP₀d (t : ℝ) : HasDerivAt P₀ (Ch * B.outerRate * Q (φ t)) t := by
    exact (((hPQ (φ t)).comp t (hφd t)).const_mul Ch).congr_deriv (by ring)
  have hPE : (∫ t in l..S, P₀ t ^ 2) ≤ Ch ^ 2 / B.outerRate * ∫ t, P t ^ 2 := by
    have hh := timeChange_l2_bound hlS ha hφ₁.continuous.continuousOn
      (fun t _ => hφd t) (fun _ _ => le_rfl) P.continuous hPi
    dsimp only [P₀]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg Ch)).trans_eq (by ring)
  have hQE : (∫ t in l..S, (deriv P₀ t) ^ 2) ≤ Ch ^ 2 * B.outerRate * ∫ t, Q t ^ 2 := by
    have hh := timeChange_l2_bound hlS ha hφ₁.continuous.continuousOn
      (fun t _ => hφd t) (fun _ _ => le_rfl) Q.continuous hQi
    have hd : deriv P₀ = fun t => Ch * B.outerRate * Q (φ t) := funext (fun t => (hP₀d t).deriv)
    rw [hd]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg Ch) (sq_nonneg B.outerRate))).trans_eq (by field_simp [ha.ne'])
  apply hprop.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hsource := add_le_add (mul_le_mul_of_nonneg_left hPE (by positivity : 0 ≤ 2 * (ε : ℝ) ^ 2))
    (mul_le_mul_of_nonneg_left hQE (by positivity : 0 ≤ 2 * C ^ 2))
  have hn := Real.sqrt_le_sqrt hN₀
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsource) (sub_nonneg.2 hYZ.le)
  linarith only [hn, hs]

end CauchyHorizon.Background
