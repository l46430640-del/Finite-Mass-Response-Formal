import CauchyHorizon.Characteristic.OuterTransverseMatching

/-! Both actual scalar traces match their affine profiles on one near-event radius. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon

theorem logarithmicIncoming_phase_first_moment {a b k q u v : ℝ}
    (hb : 0 < b) (hu : 0 < u) (hq : 0 < q) (hcrit : k = a * b) (ℓ : ℝ) (P : ℝ →ᵇ ℝ) :
    Real.exp ((a + k) * v) * (∫ x in (0 : ℝ)..u, x * logarithmicIncoming b ℓ P x) =
      b * q ^ (b + 1) * Real.exp (-(b + 1) * Real.log (q / (u * Real.exp (a * v)))) *
        terminalGreen (by linarith : 0 < b + 1) P (ℓ - Real.log u) := by
  have he : u ^ (b + 1) * Real.exp ((a + k) * v) =
      q ^ (b + 1) * Real.exp (-(b + 1) * Real.log (q / (u * Real.exp (a * v)))) := by
    rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hq,
      Real.log_div hq.ne' (mul_pos hu (Real.exp_pos _)).ne',
      Real.log_mul hu.ne' (Real.exp_ne_zero _), Real.log_exp, ← Real.exp_add, ← Real.exp_add, hcrit]
    congr 1
    ring
  rw [(logarithmicIncoming_first_moment hb hu.le ℓ P).2]
  calc
    _ = b * (u ^ (b + 1) * Real.exp ((a + k) * v)) *
        terminalGreen (by linarith : 0 < b + 1) P (ℓ - Real.log u) := by ring
    _ = _ := by rw [he]; ring

namespace Background

set_option maxHeartbeats 2000000 in
theorem exists_outer_radius_matching (B : Background) {s H dH A b k : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hbpos : 0 < b) (hb1 : b < 1) (hcrit : k = B.outerRate * b) (hks : k < s)
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
    ∃ α : ℝ, 0 < α ∧ ∀ cap ε : ℝ, 0 < cap → 0 < ε →
      ∃ δ Y T L : ℝ, 0 < δ ∧ δ < cap ∧ δ ≤ 1 ∧
        Y = B.event - α * δ ∧ Y ∈ Ioo B.inner B.event ∧ 0 < T ∧ 0 < L ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (P D : ℝ →ᵇ ℝ),
          k ≤ B.outerRate * (1 - 1 / p.toReal) → Integrable (fun t => P t ^ 2) →
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
              let Cθ := (B.outerRate / B.event) * r 0 * cν * b * (B.z Y / cν) ^ (b + 1) / (b + 1)
              let Cζ := b * r 0 * (B.z Y / cν) ^ b
              let φ := fun t => B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Y)
              let Eθ := fun t => Real.exp (k * t) *
                (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                  intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1) - Cθ * P (φ t)
              let Eζ := fun t => g t * Real.exp (k * t) *
                (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                  derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                    (Icc 0 U) (g t)) - Cζ * P (φ t)
              ∀ l S : ℝ, T ≤ l → l ≤ S → S ≤ V → g l ≤ U →
                IntegrableOn (fun t => Eθ t ^ 2) (Icc l S) ∧
                  IntegrableOn (fun t => Eζ t ^ 2) (Icc l S) ∧
                  (∫ t in l..S, Eθ t ^ 2) / δ ^ (2 * (b + 1)) +
                    (∫ t in l..S, Eζ t ^ 2) / δ ^ (2 * b) ≤
                      ε * (1 + ∫ t, P t ^ 2) + L * ∫ t, D t ^ 2 := by
  intro hi hr0 cν
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  have hcν : 0 < cν := Real.exp_pos _
  have hbc : 0 < b + 1 := by linarith only [hbpos]
  obtain ⟨δ₀, α, K, hδ₀, _hδ₀r, hα, hK, hfamily⟩ := B.exists_outer_transverse_matching
    hs hH hdH hdHR hA hbpos hb1 hcrit hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨α, hα, ?_⟩
  intro cap ε hcap hε
  let m := 2 * (1 - b)
  have hm : 0 < m := by dsimp only [m]; linarith only [hb1]
  have hsmall : ∀ᶠ d : ℝ in 𝓝 0, K * d ^ m < ε / 4 :=
    ((Real.continuous_rpow_const hm.le).const_mul K).continuousAt.tendsto.eventually_lt_const
      (by simpa only [Real.zero_rpow hm.ne', mul_zero] using div_pos hε (by norm_num : (0 : ℝ) < 4))
  obtain ⟨δs, hδs, hsmall⟩ := hsmall.exists_gt
  obtain ⟨δ, Tm, hδ, hδcap, hδ1, hTm, hmoment⟩ := B.exists_outer_radiation_moment_comparison
    hs hH hdH hdHR hA hbpos hb1 hcrit hks hc hb hrc hrb hrd hrdec hOut
    (min cap (min δ₀ δs)) (ε / 12) (by positivity) (by positivity)
  have hδ₀' : δ ≤ δ₀ := hδcap.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδs' : δ ≤ δs := hδcap.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmallδ : K * δ ^ m ≤ ε / 4 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδs' hm.le) hK.le).trans hsmall.le
  obtain ⟨Y, Tg, τ, hYeq, hY, hTg, hτ, hsolve⟩ := hfamily δ hδ hδ₀'
  let q := B.z Y / cν
  let Cθ := (a / B.event) * r 0 * cν * b * q ^ (b + 1) / (b + 1)
  let Cζ := b * r 0 * q ^ b
  have hq : 0 < q := div_pos (B.z_pos hY) hcν
  let F := fun e : ℝ => Cθ * Real.exp (-(b + 1) * e)
  let ρ := min 1 (ε * a / 24)
  have hρ : 0 < ρ := lt_min zero_lt_one (by positivity)
  have hρsmall : 6 * ρ ^ 2 ≤ (ε / 4) * a := by
    have hh := mul_le_mul_of_nonneg_left (show ρ ≤ 1 from min_le_left _ _) hρ.le
    have hh' := (show ρ ≤ ε * a / 24 from min_le_right _ _)
    nlinarith only [hh, hh']
  have hFc : Continuous F := by dsimp only [F]; fun_prop
  obtain ⟨σ, hσ, hnear⟩ : ∃ σ : ℝ, 0 < σ ∧
      ∀ e ∈ Metric.ball 0 σ, |F e - Cθ| < ρ * δ ^ (b + 1) :=
    Metric.mem_nhds_iff.1 ((hFc.continuousAt.tendsto.sub_const Cθ).abs.eventually_lt_const (by
      simpa only [F, mul_zero, Real.exp_zero, mul_one, sub_self, abs_zero] using
        mul_pos hρ (Real.rpow_pos_of_pos hδ (b + 1))))
  let θ : Ioi (0 : ℝ) := ⟨min 1 (min (a / 2) σ), lt_min zero_lt_one (lt_min (half_pos ha) hσ)⟩
  let η : Ioi (0 : ℝ) := ⟨ε / 4, show (0 : ℝ) < ε / 4 from div_pos hε (by norm_num)⟩
  let T := max Tm (max (τ η) (τ θ))
  have hTη : τ η ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTθ : τ θ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hT : 0 < T := (hTg.trans_le (hτ η)).trans_le hTη
  have hTgT : Tg ≤ T := (hτ η).trans hTη
  let Lθ := 12 * Cθ ^ 2 / (a * δ ^ (2 * (b + 1))) * ((1 / (b + 1)) ^ 2 + 1)
  let Lζ := 6 * Cζ ^ 2 / (a * δ ^ (2 * b))
  have hCζ : 0 < Cζ := by
    have hrp := B.inner_pos.trans hrinit
    dsimp only [Cζ]
    positivity
  have hL : 0 < Lθ + Lζ := add_pos_of_nonneg_of_pos
    (by dsimp only [Lθ]; positivity) (by dsimp only [Lζ]; positivity)
  refine ⟨δ, Y, T, Lθ + Lζ, hδ, hδcap.trans_le (min_le_left _ _), hδ1, hYeq, hY, hT, hL, ?_⟩
  intro p hp ℓ P D hkp hP hd hD hfδ hfnδ
  obtain ⟨g, hgc, hga, hgl, hg0, hgeom, hmatch⟩ := hsolve p hp ℓ P D hkp hP hd hD hfδ hfnδ
  refine ⟨g, hgc.mono (Ici_subset_Ici.2 hTgT), hga.mono (Ici_subset_Ici.2 hTgT), hgl,
    fun t ht => ⟨hg0 t (hTgT.trans ht), (hgeom t (hTgT.trans ht)).2.1⟩, ?_⟩
  intro U V hU hV hUR hf x hx hUδ
  have hfn := (scalar_prefix_norm_le hUδ hfδ).trans hfnδ
  have hmatch' := hmatch U V hU hV hUR hf x hx hUδ
  refine ⟨fun t ht => hmatch'.1 t (hTgT.trans ht), ?_⟩
  intro Cθ' Cζ' φ Eθ Eζ l S hl hlS hSV hglU
  have hlTg : Tg ≤ l := hTgT.trans hl
  have hl0 : 0 ≤ l := hT.le.trans hl
  have hsub : Icc l S ⊆ Ici Tg := fun _ ht => hlTg.trans ht.1
  have hg (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Ioc 0 U ∧ g t * Real.exp (a * t) ≤ δ :=
    ⟨⟨(hg0 t (hsub ht)).1, (hga.antitoneOn hlTg (hsub ht) ht.1).trans hglU⟩,
      (hgeom t (hsub ht)).2.1⟩
  have hgu (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Icc 0 U := ⟨(hg t ht).1.1.le, (hg t ht).1.2⟩
  have htv (t : ℝ) (ht : t ∈ Icc l S) : t ∈ Icc 0 V := ⟨hl0.trans ht.1, ht.2.trans hSV⟩
  let ψ := fun t => ℓ - Real.log (g t)
  let e := fun t => Real.log (q / (g t * Real.exp (a * t)))
  have hψc : ContinuousOn ψ (Icc l S) :=
    continuousOn_const.sub ((hgc.mono hsub).log (fun t ht => (hg t ht).1.1.ne'))
  have hφc : Continuous φ := by dsimp only [φ]; fun_prop
  have hdψ (t : ℝ) (ht : t ∈ Icc l S) : HasDerivAt ψ (-deriv g t / g t) t := by
    simpa only [neg_div] using ((hgeom t (hsub ht)).1.hasDerivAt.log (hg t ht).1.1.ne').const_sub ℓ
  have hdφ (t : ℝ) (_ht : t ∈ Icc l S) : HasDerivAt φ a t :=
    (((((hasDerivAt_id t).const_mul a).add_const ℓ).add_const (Real.log cν)).sub_const
      (Real.log (B.z Y))).congr_deriv (by simp)
  have heq (t : ℝ) : e t = Real.log (B.z Y / (g t * (cν * Real.exp (a * t)))) := by
    dsimp only [e, q]; congr 1; ring
  have hphase (t : ℝ) (ht : t ∈ Icc l S) :
      a / 2 ≤ -deriv g t / g t ∧ |ψ t - φ t| ≤ 1 ∧ |F (e t) - Cθ| ≤ ρ * δ ^ (b + 1) := by
    have hh := (hgeom t (hsub ht)).2.2 θ (hTθ.trans (hl.trans ht.1))
    rw [← heq t] at hh
    have he' := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt hh
    have hspeed := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt hh |>.trans_le
      (show (θ : ℝ) ≤ a / 2 from (min_le_right _ _).trans (min_le_left _ _))
    have hphi : ψ t - φ t = e t := by
      rw [heq t, Real.log_div (B.z_pos hY).ne' (mul_pos (hg t ht).1.1 (mul_pos hcν (Real.exp_pos _))).ne',
        Real.log_mul (hg t ht).1.1.ne' (mul_pos hcν (Real.exp_pos _)).ne',
        Real.log_mul hcν.ne' (Real.exp_ne_zero _)]
      dsimp only [ψ, φ]
      simp only [Real.log_exp]
      ring
    refine ⟨?_, ?_, ?_⟩
    · have hh' := (abs_lt.1 hspeed).1
      linarith only [hh']
    · rw [hphi]
      exact he'.le.trans (min_le_left _ _)
    · apply le_of_lt
      apply hnear
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
        he'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let Q := fun t => (b + 1) * terminalGreen hbc P t
  have hQc : Continuous Q := by dsimp only [Q]; fun_prop
  obtain ⟨hQi, hQE⟩ := terminalGreen_l2_contraction hbc P hP
  have htime : (∫ t in l..S, Q (ψ t) ^ 2) ≤ (∫ t, P t ^ 2) / (a / 2) :=
    (timeChange_l2_bound hlS (half_pos ha) hψc hdψ (fun t ht => (hphase t ht).1) hQc hQi).trans
      (div_le_div_of_nonneg_right hQE (half_pos ha).le)
  let E₀ := fun t => Real.exp (k * t) *
    (x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 *
      x.2.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 1 -
      (a / B.event) * r 0 * (cν * Real.exp (a * projIcc 0 V hV t)) *
        ∫ w in (0 : ℝ)..(projIcc 0 U hU (g t) : ℝ), w * logarithmicIncoming b ℓ P w)
  let E₁ := fun t => (F (e t) - Cθ) * Q (ψ t)
  let E₂ := fun t => Q (ψ t) - P (φ t)
  have hE₀ := hmoment U V hU hV hUR p hp ℓ P hkp hP hf x hx hfn
    l S g ((le_max_left _ _).trans hl) hlS hSV (hgc.mono hsub) (fun t ht => ⟨hgu t ht, (hg t ht).2⟩)
  have hE₂ := terminalGreen_phase_error_energy hlS (half_pos ha) zero_le_one hbc
    hφc.continuousOn hψc hdφ hdψ (fun _ _ => half_le_self ha.le)
    (fun t ht => (hphase t ht).1) (fun t ht => (hphase t ht).2.1) P D hd hD
  have hec : ContinuousOn e (Icc l S) :=
    (continuousOn_const.div ((hgc.mono hsub).mul (by fun_prop))
      (fun t ht => (mul_pos (hg t ht).1.1 (Real.exp_pos _)).ne')).log
      (fun t ht => (div_pos hq (mul_pos (hg t ht).1.1 (Real.exp_pos _))).ne')
  have hE₁c : ContinuousOn E₁ (Icc l S) :=
    ((hFc.comp_continuousOn hec).sub continuousOn_const).mul (hQc.comp_continuousOn hψc)
  have hE₂c : ContinuousOn E₂ (Icc l S) :=
    (hQc.comp_continuousOn hψc).sub (P.continuous.comp_continuousOn hφc.continuousOn)
  have hE₁bound : (∫ t in l..S, E₁ t ^ 2) ≤ (ρ * δ ^ (b + 1)) ^ 2 * ((∫ t, P t ^ 2) / (a / 2)) := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) hlS
      ((hE₁c.pow 2).intervalIntegrable_of_Icc hlS)
      ((((hQc.comp_continuousOn hψc).pow 2).const_mul ((ρ * δ ^ (b + 1)) ^ 2)).intervalIntegrable_of_Icc hlS)
      (fun t ht => by
        change ((F (e t) - Cθ) * Q (ψ t)) ^ 2 ≤ (ρ * δ ^ (b + 1)) ^ 2 * Q (ψ t) ^ 2
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (hphase t ht).2.2)
    rw [intervalIntegral.integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left htime (sq_nonneg _))
  have harg : ContinuousOn (fun t => (projIcc 0 U hU (g t), projIcc 0 V hV t)) (Icc l S) :=
    ((continuous_projIcc (a := (0 : ℝ)) (b := U) (h := hU)).comp_continuousOn (hgc.mono hsub)).prodMk
      (continuous_projIcc (a := (0 : ℝ)) (b := V) (h := hV)).continuousOn
  have hθc : ContinuousOn (fun t => x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 *
      x.2.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 1) (Icc l S) :=
    (((continuous_apply (0 : Fin 3)).comp x.1.uncurry.continuous).comp_continuousOn harg).mul
      (((continuous_apply (1 : Fin 3)).comp x.2.1.uncurry.continuous).comp_continuousOn harg)
  have hEθc : ContinuousOn Eθ (Icc l S) :=
    ((by fun_prop : ContinuousOn (fun t => Real.exp (k * t)) (Icc l S)).mul hθc).sub
      ((P.continuous.comp hφc).continuousOn.const_mul Cθ)
  have hEeq (t : ℝ) (ht : t ∈ Icc l S) : Eθ t = E₀ t + E₁ t + Cθ * E₂ t := by
    have hmoment' := logarithmicIncoming_phase_first_moment hbpos (hg t ht).1.1 hq hcrit ℓ P (v := t)
    have hcoeff : Real.exp (k * t) * ((a / B.event) * r 0 * (cν * Real.exp (a * t)) *
        ∫ w in (0 : ℝ)..g t, w * logarithmicIncoming b ℓ P w) = F (e t) * Q (ψ t) := by
      calc
        _ = ((a / B.event) * r 0 * cν) * (Real.exp ((a + k) * t) *
            ∫ w in (0 : ℝ)..g t, w * logarithmicIncoming b ℓ P w) := by
          rw [add_mul, Real.exp_add]; ring
        _ = _ := by rw [hmoment']; dsimp only [F, Cθ, e, Q, ψ, a]; field_simp [hbc.ne']
    dsimp only [Eθ, E₀, E₁, E₂, intervalExtension_apply]
    rw [projIcc_of_mem hV (htv t ht), projIcc_of_mem hU (hgu t ht)] at ⊢
    nlinarith only [hcoeff]
  have hI₀ : IntervalIntegrable (fun t => E₀ t ^ 2) volume l S :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hE₀.1
  have hI₁ : IntervalIntegrable (fun t => E₁ t ^ 2) volume l S := (hE₁c.pow 2).intervalIntegrable_of_Icc hlS
  have hI₂ : IntervalIntegrable (fun t => E₂ t ^ 2) volume l S := (hE₂c.pow 2).intervalIntegrable_of_Icc hlS
  have hsum := intervalIntegral.integral_mono_on (μ := volume) hlS
    ((hEθc.pow 2).intervalIntegrable_of_Icc hlS)
    (((hI₀.const_mul 3).add (hI₁.const_mul 3)).add (hI₂.const_mul (3 * Cθ ^ 2)))
    (fun t ht => show Eθ t ^ 2 ≤ 3 * E₀ t ^ 2 + 3 * E₁ t ^ 2 + 3 * Cθ ^ 2 * E₂ t ^ 2 from by
      rw [hEeq t ht]
      nlinarith only [sq_nonneg (E₀ t - E₁ t), sq_nonneg (E₀ t - Cθ * E₂ t), sq_nonneg (E₁ t - Cθ * E₂ t)])
  rw [intervalIntegral.integral_add ((hI₀.const_mul 3).add (hI₁.const_mul 3)) (hI₂.const_mul (3 * Cθ ^ 2)),
    intervalIntegral.integral_add (hI₀.const_mul 3) (hI₁.const_mul 3),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hsum
  have hdpos : 0 < δ ^ (2 * (b + 1)) := Real.rpow_pos_of_pos hδ _
  have hd2 : (δ ^ (b + 1)) ^ (2 : ℕ) = δ ^ (2 * (b + 1)) := by
    rw [← Real.rpow_natCast (δ ^ (b + 1)) 2, ← Real.rpow_mul hδ.le]
    congr 1
    norm_num
    ring
  have hE₀norm : 3 * (∫ t in l..S, E₀ t ^ 2) / δ ^ (2 * (b + 1)) ≤ (ε / 4) * (1 + ∫ t, P t ^ 2) := by
    apply (div_le_iff₀ hdpos).2
    have hh := mul_le_mul_of_nonneg_left hE₀.2 (by norm_num : (0 : ℝ) ≤ 3)
    exact hh.trans_eq (by ring)
  have hE₁norm : 3 * (∫ t in l..S, E₁ t ^ 2) / δ ^ (2 * (b + 1)) ≤ (ε / 4) * ∫ t, P t ^ 2 := by
    calc
      _ ≤ 3 * ((ρ * δ ^ (b + 1)) ^ 2 * ((∫ t, P t ^ 2) / (a / 2))) / δ ^ (2 * (b + 1)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE₁bound (by norm_num)) hdpos.le
      _ = (6 * ρ ^ 2 / a) * ∫ t, P t ^ 2 := by rw [mul_pow, hd2]; field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).2 hρsmall) (integral_nonneg (fun t => sq_nonneg _))
  have hE₂norm : (3 * Cθ ^ 2) * (∫ t in l..S, E₂ t ^ 2) / δ ^ (2 * (b + 1)) ≤ Lθ * ∫ t, D t ^ 2 := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hE₂.2 (by positivity : 0 ≤ 3 * Cθ ^ 2)) hdpos.le
    exact hh.trans_eq (by dsimp only [Lθ]; norm_num; ring)
  have hθbound : (∫ t in l..S, Eθ t ^ 2) / δ ^ (2 * (b + 1)) ≤
      (ε / 4) * (1 + ∫ t, P t ^ 2) + (ε / 4) * (∫ t, P t ^ 2) + Lθ * ∫ t, D t ^ 2 := by
    have hh := div_le_div_of_nonneg_right hsum hdpos.le
    exact hh.trans (by convert add_le_add (add_le_add hE₀norm hE₁norm) hE₂norm using 1; ring)
  have hζ := hmatch'.2 η l S (hTη.trans hl) hlS hSV hglU
  have hζbound : (∫ t in l..S, Eζ t ^ 2) / δ ^ (2 * b) ≤
      (ε / 4) * (1 + ∫ t, P t ^ 2) + (ε / 4) * (∫ t, P t ^ 2) + Lζ * ∫ t, D t ^ 2 :=
    hζ.2.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hsmallδ
      (add_nonneg zero_le_one (integral_nonneg (fun t => sq_nonneg (P t))))) le_rfl) le_rfl)
  refine ⟨(hEθc.pow 2).integrableOn_Icc, hζ.1, ?_⟩
  have hh := add_le_add hθbound hζbound
  nlinarith only [hh, hε]

end Background
end CauchyHorizon
