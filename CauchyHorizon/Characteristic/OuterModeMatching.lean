import CauchyHorizon.Characteristic.OuterRadiusMatching
import CauchyHorizon.Radial.OuterMatching

/-! Both actual scalar traces match the normalized radial mode near the event horizon. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 2000000 in
theorem exists_outer_mode_matching (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hb1 : B.criticalExponent < 1) (hks : B.innerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let b := B.criticalExponent
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    let Ch := r 0 / (B.event * cν ^ b)
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb1).1 (B.event - y)
    let Vmode := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb1).2 (B.event - y)
    ∃ α : ℝ, 0 < α ∧ ∀ cap ε : ℝ, 0 < cap → 0 < ε →
      ∃ δ Y T L : ℝ, 0 < δ ∧ δ < cap ∧ δ ≤ 1 ∧ Y = B.event - α * δ ∧
        Y ∈ Ioo B.inner B.event ∧ B.event - cap < Y ∧ 0 < T ∧ 0 < L ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (P D : ℝ →ᵇ ℝ),
          B.innerRate ≤ B.outerRate * (1 - 1 / p.toReal) → Integrable (fun t => P t ^ 2) →
          (∀ t, HasDerivAt P (D t) t) → Integrable (fun t => D t ^ 2) →
          MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 δ)) →
          (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧ Tendsto g atTop (𝓝 0) ∧
            (∀ t ∈ Ici T, g t ∈ Ioo 0 δ ∧ g t * Real.exp (B.outerRate * t) ≤ δ) ∧
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hf : MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))) (x : WaveState U V)
              (_hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hf) x), U ≤ δ →
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
                  (∫ t in l..S, Eθ t ^ 2) + (∫ t in l..S, Eζ t ^ 2) ≤
                    ε * (1 + ∫ t, P t ^ 2) + L * ∫ t, D t ^ 2 := by
  intro b hi hr0 cν Ch X Vmode
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  have hbpos : 0 < b := B.criticalExponent_pos
  have hcν : 0 < cν := Real.exp_pos _
  have hcrit : B.innerRate = B.outerRate * b := by
    dsimp only [b, criticalExponent]
    field_simp [B.outerRate_pos.ne']
  obtain ⟨α, hα, hfamily⟩ := B.exists_outer_radius_matching
    hs hH hdH hdHR hA hbpos hb1 hcrit hks hc hb hrc hrb hrinit hrd hrdec hOut
  let K := max 1 (4 / α ^ (2 * b))
  have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
  have hαb : 0 < α ^ (2 * b) := Real.rpow_pos_of_pos hα _
  refine ⟨α, hα, ?_⟩
  intro cap ε hcap hε
  obtain ⟨Y₀, hY₀, hnear⟩ := B.exists_outer_mode_tolerance hb1 hcν
    (R := r 0) (ε := ε * a / 4) (by positivity)
  let e₀ := ε / (4 * K)
  have he₀ : 0 < e₀ := by dsimp only [e₀]; positivity
  obtain ⟨δ, Y, T, L, hδ, hδcap, hδ1, hYeq, hY, hT, hL, hsolve⟩ :=
    hfamily (min cap (min (cap / α) ((B.event - Y₀) / α))) e₀
      (lt_min hcap (lt_min (div_pos hcap hα) (div_pos (sub_pos.2 hY₀.2) hα))) he₀
  have hYcap : B.event - cap < Y := by
    have hh := (lt_div_iff₀ hα).1 (hδcap.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    rw [hYeq]
    nlinarith only [hh]
  have hYY₀ : Y₀ < Y := by
    have hh := (lt_div_iff₀ hα).1 (hδcap.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    rw [hYeq]
    nlinarith only [hh]
  have hcoeff := hnear Y ⟨hYY₀, hY.2⟩
  let q := B.criticalWeight Y
  have hq : 0 < q := B.criticalWeight_pos hY
  have hθscale : δ ^ (2 * (b + 1)) ≤ K :=
    (Real.rpow_le_one hδ.le hδ1 (by positivity : 0 ≤ 2 * (b + 1))).trans (le_max_left _ _)
  have hζscale : δ ^ (2 * b) / q ^ 2 ≤ K := by
    have hgap : B.event - Y = α * δ := by rw [hYeq]; ring
    have heq : δ ^ (2 * b) / q ^ 2 = ((B.event - Y) ^ (2 * b) / q ^ 2) / α ^ (2 * b) := by
      rw [hgap, Real.mul_rpow hα.le hδ.le]
      field_simp [hαb.ne']
    rw [heq]
    exact (div_le_div_of_nonneg_right hcoeff.1 hαb.le).trans (le_max_right _ _)
  let Cθ := (a / B.event) * r 0 * cν * b * (B.z Y / cν) ^ (b + 1) / (b + 1)
  let Cζ := b * r 0 * (B.z Y / cν) ^ b
  let Aθ := Cθ - Ch * X Y
  let Aζ := Cζ / q - Ch * Vmode Y
  have hA : Aθ ^ 2 + Aζ ^ 2 ≤ ε * a / 4 := hcoeff.2
  refine ⟨δ, Y, T, 2 * K * L, hδ, hδcap.trans_le (min_le_left _ _), hδ1, hYeq, hY, hYcap,
    hT, by positivity, ?_⟩
  intro p hp ℓ P D hkp hP hd hD hfδ hfnδ
  obtain ⟨g, hgc, hga, hgl, hg0, hmatch⟩ := hsolve p hp ℓ P D hkp hP hd hD hfδ hfnδ
  refine ⟨g, hgc, hga, hgl, hg0, ?_⟩
  intro U V hU hV hUR hf x hx hUδ
  have hh := hmatch U V hU hV hUR hf x hx hUδ
  refine ⟨hh.1, ?_⟩
  intro φ Eθ Eζ l S hl hlS hSV hglU
  let E₀ := fun t => Real.exp (B.innerRate * t) *
    (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
      intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1) - Cθ * P (φ t)
  let E₁ := fun t => g t * Real.exp (B.innerRate * t) *
    (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
      derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
        (Icc 0 U) (g t)) - Cζ * P (φ t)
  have hm := hh.2 l S hl hlS hSV hglU
  have hsub : Icc l S ⊆ Ici T := fun _ ht => hl.trans ht.1
  have hg (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Ioc 0 U :=
    ⟨(hg0 t (hsub ht)).1.1, (hga.antitoneOn hl (hsub ht) ht.1).trans hglU⟩
  have hφc : Continuous φ := by dsimp only [φ]; fun_prop
  have hPc : Continuous (fun t => P (φ t)) := P.continuous.comp hφc
  have hdφ (t : ℝ) (_ht : t ∈ Icc l S) : HasDerivAt φ a t :=
    (((((hasDerivAt_id t).const_mul a).add_const ℓ).add_const (Real.log cν)).sub_const
      (Real.log (B.z Y))).congr_deriv (by simp)
  have htime := timeChange_l2_bound hlS ha hφc.continuousOn hdφ (fun _ _ => le_rfl) P.continuous hP
  have harg : ContinuousOn (fun t => (projIcc 0 U hU (g t), projIcc 0 V hV t)) (Icc l S) :=
    ((continuous_projIcc (a := (0 : ℝ)) (b := U) (h := hU)).comp_continuousOn (hgc.mono hsub)).prodMk
      (continuous_projIcc (a := (0 : ℝ)) (b := V) (h := hV)).continuousOn
  have hθc : ContinuousOn (fun t => x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 *
      x.2.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 1) (Icc l S) :=
    (((continuous_apply (0 : Fin 3)).comp x.1.uncurry.continuous).comp_continuousOn harg).mul
      (((continuous_apply (1 : Fin 3)).comp x.2.1.uncurry.continuous).comp_continuousOn harg)
  have hEθc : ContinuousOn Eθ (Icc l S) :=
    ((by fun_prop : ContinuousOn (fun t => Real.exp (B.innerRate * t)) (Icc l S)).mul hθc).sub
      (hPc.continuousOn.const_mul (Ch * X Y))
  have hfc : ContinuousOn (logarithmicIncoming b ℓ P) (Ioi 0) :=
    (continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl ht.ne'))).mul
      (P.continuous.comp_continuousOn (continuousOn_const.sub (continuousOn_id.log (fun t ht => ht.ne'))))
  have hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 0 = -1 := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]; rfl
  have hif : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 1 = logarithmicIncoming b ℓ P u := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]; rfl
  have hZc := hx.scalar_curve_continuous rfl hinu hfc hif (hgc.mono hsub) continuousOn_id hg
  have hEζc : ContinuousOn Eζ (Icc l S) :=
    ((((hgc.mono hsub).mul (by fun_prop)).mul hZc).div_const q).sub
      (hPc.continuousOn.const_mul (Ch * Vmode Y))
  have heθ (t : ℝ) : Eθ t = E₀ t + Aθ * P (φ t) := by dsimp only [Eθ, E₀, Aθ]; ring
  have heζ (t : ℝ) : Eζ t = E₁ t / q + Aζ * P (φ t) := by dsimp only [Eζ, E₁, Aζ]; ring
  have hI₀ : IntervalIntegrable (fun t => E₀ t ^ 2) volume l S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hm.1
  have hI₁ : IntervalIntegrable (fun t => E₁ t ^ 2) volume l S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hm.2.1
  have hIP : IntervalIntegrable (fun t => P (φ t) ^ 2) volume l S := (hPc.pow 2).intervalIntegrable _ _
  have hIθ : IntervalIntegrable (fun t => Eθ t ^ 2) volume l S := (hEθc.pow 2).intervalIntegrable_of_Icc hlS
  have hIζ : IntervalIntegrable (fun t => Eζ t ^ 2) volume l S := (hEζc.pow 2).intervalIntegrable_of_Icc hlS
  have hsum := intervalIntegral.integral_mono_on (μ := volume) hlS (hIθ.add hIζ)
    (((hI₀.const_mul 2).add (hI₁.const_mul (2 / q ^ 2))).add (hIP.const_mul (2 * (Aθ ^ 2 + Aζ ^ 2))))
    (fun t _ => show Eθ t ^ 2 + Eζ t ^ 2 ≤
        2 * E₀ t ^ 2 + (2 / q ^ 2) * E₁ t ^ 2 + 2 * (Aθ ^ 2 + Aζ ^ 2) * P (φ t) ^ 2 from by
      rw [heθ, heζ]
      have hh₁ : (E₀ t + Aθ * P (φ t)) ^ 2 ≤ 2 * E₀ t ^ 2 + 2 * Aθ ^ 2 * P (φ t) ^ 2 := by
        nlinarith only [sq_nonneg (E₀ t - Aθ * P (φ t))]
      have hh₂ : (E₁ t / q + Aζ * P (φ t)) ^ 2 ≤ (2 / q ^ 2) * E₁ t ^ 2 + 2 * Aζ ^ 2 * P (φ t) ^ 2 := by
        calc
          _ ≤ 2 * (E₁ t / q) ^ 2 + 2 * (Aζ * P (φ t)) ^ 2 := by
            nlinarith only [sq_nonneg (E₁ t / q - Aζ * P (φ t))]
          _ = _ := by ring
      nlinarith only [hh₁, hh₂])
  rw [intervalIntegral.integral_add hIθ hIζ,
    intervalIntegral.integral_add ((hI₀.const_mul 2).add (hI₁.const_mul (2 / q ^ 2))) (hIP.const_mul (2 * (Aθ ^ 2 + Aζ ^ 2))),
    intervalIntegral.integral_add (hI₀.const_mul 2) (hI₁.const_mul (2 / q ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hsum
  have hdθ : 0 < δ ^ (2 * (b + 1)) := Real.rpow_pos_of_pos hδ _
  have hdζ : 0 < δ ^ (2 * b) := Real.rpow_pos_of_pos hδ _
  have hscaleθ : (∫ t in l..S, E₀ t ^ 2) ≤ K * ((∫ t in l..S, E₀ t ^ 2) / δ ^ (2 * (b + 1))) := by
    calc
      _ = δ ^ (2 * (b + 1)) * ((∫ t in l..S, E₀ t ^ 2) / δ ^ (2 * (b + 1))) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hθscale
        (div_nonneg (intervalIntegral.integral_nonneg hlS (fun _ _ => sq_nonneg _)) hdθ.le)
  have hscaleζ : (∫ t in l..S, E₁ t ^ 2) / q ^ 2 ≤ K * ((∫ t in l..S, E₁ t ^ 2) / δ ^ (2 * b)) := by
    calc
      _ = (δ ^ (2 * b) / q ^ 2) * ((∫ t in l..S, E₁ t ^ 2) / δ ^ (2 * b)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hζscale
        (div_nonneg (intervalIntegral.integral_nonneg hlS (fun _ _ => sq_nonneg _)) hdζ.le)
  have hscale : (∫ t in l..S, E₀ t ^ 2) + (∫ t in l..S, E₁ t ^ 2) / q ^ 2 ≤
      K * ((∫ t in l..S, E₀ t ^ 2) / δ ^ (2 * (b + 1)) + (∫ t in l..S, E₁ t ^ 2) / δ ^ (2 * b)) := by
    simpa only [mul_add] using add_le_add hscaleθ hscaleζ
  have hbudget := mul_le_mul_of_nonneg_left (hscale.trans (mul_le_mul_of_nonneg_left hm.2.2 hK.le))
    (by norm_num : (0 : ℝ) ≤ 2)
  have hPnon : 0 ≤ ∫ t, P t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  have htime' := mul_le_mul_of_nonneg_left htime (by positivity : 0 ≤ 2 * (Aθ ^ 2 + Aζ ^ 2))
  have hamp := mul_le_mul_of_nonneg_right hA (div_nonneg hPnon ha.le)
  refine ⟨(hEθc.pow 2).integrableOn_Icc, (hEζc.pow 2).integrableOn_Icc, ?_⟩
  calc
    _ ≤ 2 * K * (e₀ * (1 + ∫ t, P t ^ 2) + L * ∫ t, D t ^ 2) +
        2 * (ε * a / 4) * ((∫ t, P t ^ 2) / a) := by
      have hamps : 2 * (Aθ ^ 2 + Aζ ^ 2) * ((∫ t, P t ^ 2) / a) ≤
          2 * (ε * a / 4) * ((∫ t, P t ^ 2) / a) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hamp (by norm_num : (0 : ℝ) ≤ 2)
      exact hsum.trans (by convert add_le_add hbudget (htime'.trans hamps) using 1 <;> ring)
    _ = (ε / 2) * (1 + ∫ t, P t ^ 2) + (ε / 2) * (∫ t, P t ^ 2) + (2 * K * L) * ∫ t, D t ^ 2 := by
      dsimp only [e₀]
      field_simp
      ring
    _ ≤ _ := by nlinarith only [hε]

end CauchyHorizon.Background
