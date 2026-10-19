import CauchyHorizon.Characteristic.OuterTransverseComparison
import CauchyHorizon.Characteristic.OuterPhase
import CauchyHorizon.Analysis.PhaseEnergy

/-! The actual transverse trace matches its fixed-radius affine profile. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon

theorem logarithmicIncoming_phase_trace {a b k q u v : ℝ}
    (hu : 0 < u) (hq : 0 < q) (hcrit : k = a * b) (ℓ : ℝ) (P : ℝ → ℝ) :
    u * Real.exp (k * v) * logarithmicIncoming b ℓ P u =
      b * q ^ b * Real.exp (-b * Real.log (q / (u * Real.exp (a * v)))) * P (ℓ - Real.log u) := by
  have hp : u * u ^ (b - 1) = u ^ b := by
    rw [Real.rpow_sub hu, Real.rpow_one]
    field_simp
  have he : u ^ b * Real.exp (k * v) =
      q ^ b * Real.exp (-b * Real.log (q / (u * Real.exp (a * v)))) := by
    rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hq,
      Real.log_div hq.ne' (mul_pos hu (Real.exp_pos _)).ne',
      Real.log_mul hu.ne' (Real.exp_ne_zero _), Real.log_exp, ← Real.exp_add, ← Real.exp_add, hcrit]
    congr 1
    ring
  calc
    _ = b * (u * u ^ (b - 1)) * Real.exp (k * v) * P (ℓ - Real.log u) := by
      dsimp only [logarithmicIncoming]; ring
    _ = _ := by rw [hp]; rw [mul_assoc b, he]; ring

namespace Background

set_option maxHeartbeats 1800000 in
theorem exists_outer_transverse_matching (B : Background) {s H dH A b k : ℝ}
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
    ∃ δ₀ α K : ℝ, 0 < δ₀ ∧ δ₀ ≤ r 0 / 4 ∧ 0 < α ∧ 0 < K ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ Y T : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
        Y = B.event - α * δ ∧ Y ∈ Ioo B.inner B.event ∧ 0 < T ∧ (∀ ε, T ≤ τ ε) ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (P D : ℝ →ᵇ ℝ),
          k ≤ B.outerRate * (1 - 1 / p.toReal) → Integrable (fun t => P t ^ 2) →
          (∀ t, HasDerivAt P (D t) t) → Integrable (fun t => D t ^ 2) →
          MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 δ)) →
          (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧ Tendsto g atTop (𝓝 0) ∧
            (∀ t ∈ Ici T, g t ∈ Ioo 0 δ) ∧
            (∀ t ∈ Ici T, DifferentiableAt ℝ g t ∧ g t * Real.exp (B.outerRate * t) ≤ δ ∧
              ∀ ε, τ ε ≤ t →
                |Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t))))| +
                  |-deriv g t / g t - B.outerRate| < (ε : ℝ)) ∧
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hf : MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U))) (x : WaveState U V)
              (_hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hf) x), U ≤ δ →
              (∀ t ∈ Ici T, g t ≤ U → t ≤ V →
                intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 = Y) ∧
              let C := b * r 0 * (B.z Y / cν) ^ b
              let φ := fun t => B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Y)
              let E := fun t => g t * Real.exp (k * t) *
                (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                  derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                    (Icc 0 U) (g t)) - C * P (φ t)
              ∀ (ε : Ioi (0 : ℝ)) (l S : ℝ), τ ε ≤ l → l ≤ S → S ≤ V → g l ≤ U →
                IntegrableOn (fun t => E t ^ 2) (Icc l S) ∧
                  (∫ t in l..S, E t ^ 2) / δ ^ (2 * b) ≤
                    K * δ ^ (2 * (1 - b)) * (1 + ∫ t, P t ^ 2) +
                      (ε : ℝ) * (∫ t, P t ^ 2) +
                      (6 * C ^ 2 / (B.outerRate * δ ^ (2 * b))) * ∫ t, D t ^ 2 := by
  intro hi hr0 cν
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  have hcν : 0 < cν := Real.exp_pos _
  obtain ⟨δg, α, β, η, hδg, hδgr, hα, _hβ, _hη, hfamily⟩ :=
    B.exists_outer_phase_family hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δt, K, hδt, hK, htrans⟩ := B.exists_outer_transverse_comparison
    hs hH hdH hdHR hA hbpos hb1 hcrit hks hc hb hrc hrb hrd hrdec hOut
  refine ⟨min δg δt, α, 3 * K, lt_min hδg hδt, (min_le_left _ _).trans hδgr, hα,
    mul_pos (by norm_num) hK, ?_⟩
  intro δ hδ hδcap
  have hδt' := hδcap.trans (min_le_right _ _)
  obtain ⟨Y, T, τ₀, hYeq, hY, hT, hτ₀, hsolve⟩ := hfamily δ hδ (hδcap.trans (min_le_left _ _))
  let q := B.z Y / cν
  let C := b * r 0 * q ^ b
  have hq : 0 < q := div_pos (B.z_pos hY) hcν
  let F := fun z : ℝ × ℝ => b * (r 0 - z.2) * q ^ b * Real.exp (-b * z.1)
  have hFc : Continuous F := by dsimp only [F]; fun_prop
  let ρ := fun ε : Ioi (0 : ℝ) => min 1 ((ε : ℝ) * a / 6)
  have hρ (ε) : 0 < ρ ε := lt_min zero_lt_one (div_pos (mul_pos ε.property ha) (by norm_num))
  have hρsmall (ε) : 6 * (ρ ε) ^ 2 ≤ (ε : ℝ) * a := by
    have hh := mul_le_mul_of_nonneg_left (show ρ ε ≤ 1 from min_le_left _ _) (hρ ε).le
    have hh' := (show ρ ε ≤ (ε : ℝ) * a / 6 from min_le_right _ _)
    nlinarith only [hh, hh']
  have htolerance (ε : Ioi (0 : ℝ)) : ∃ σ : ℝ, 0 < σ ∧
      ∀ z ∈ Metric.ball (0, 0) σ, |F z - C| < ρ ε * δ ^ b := by
    have hzero : |F (0, 0) - C| < ρ ε * δ ^ b := by
      simp only [F, C, sub_zero, mul_zero, Real.exp_zero, mul_one, sub_self, abs_zero]
      positivity [hρ ε]
    exact Metric.mem_nhds_iff.1 ((hFc.continuousAt.tendsto.sub_const C).abs.eventually_lt_const hzero)
  choose σ hσ hnear using htolerance
  let θ := fun ε : Ioi (0 : ℝ) => (⟨min 1 (min (a / 2) (σ ε)),
    lt_min zero_lt_one (lt_min (half_pos ha) (hσ ε))⟩ : Ioi (0 : ℝ))
  have he : Tendsto (fun t : ℝ => δ * Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha))).const_mul δ
  have hgtol (ε : Ioi (0 : ℝ)) := eventually_atTop.1 (he.eventually_lt_const (hσ ε))
  choose Tg hTg using hgtol
  let τ := fun ε => max (τ₀ (θ ε)) (max (τ₀ ε) (Tg ε))
  have hTτ (ε) : T ≤ τ ε := (hτ₀ (θ ε)).trans (le_max_left _ _)
  refine ⟨Y, T, τ, hYeq, hY, hT, hTτ, ?_⟩
  intro p hp ℓ P D hkp hP hd hD hfδ hfnδ
  obtain ⟨g, hgc, hga, hgl, hpoint⟩ := hsolve p hp (logarithmicIncoming b ℓ P) hfδ hfnδ
  refine ⟨g, hgc, hga, hgl, fun t ht => (hpoint t ht).1, ?_, ?_⟩
  · intro t ht
    have hpt := hpoint t ht
    refine ⟨hpt.2.1, hpt.2.2.2.1.trans (by linarith only [hδ]), ?_⟩
    intro ε hε
    exact hpt.2.2.2.2.2.2.1 ε (((le_max_left _ _).trans (le_max_right _ _)).trans hε)
  intro U V hU hV hUR hf x hx hUδ
  have hfn := (scalar_prefix_norm_le hUδ hfδ).trans hfnδ
  refine ⟨?_, ?_⟩
  · intro t ht hgtU htV
    have hgu : g t ∈ Icc 0 U := ⟨(hpoint t ht).1.1.le, hgtU⟩
    have htv : t ∈ Icc 0 V := ⟨hT.le.trans ht, htV⟩
    rw [intervalExtension_apply, intervalExtension_apply, projIcc_of_mem hU hgu, projIcc_of_mem hV htv]
    simpa only [projIcc_of_mem hU hgu, projIcc_of_mem hV htv] using
      ((hpoint t ht).2.2.2.2.2.2.2 U V hU hV hUR hf x hx hgtU htV).1
  · intro C' φ E ε l S hl hlS hSV hglU
    have hlT : T ≤ l := (hTτ ε).trans hl
    have hl0 : 0 ≤ l := hT.le.trans hlT
    have hsub : Icc l S ⊆ Ici T := fun _ ht => hlT.trans ht.1
    have hg (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Ioc 0 U ∧ g t * Real.exp (a * t) ≤ δ := by
      have hpt := hpoint t (hsub ht)
      refine ⟨⟨hpt.1.1, (hga.antitoneOn hlT (hsub ht) ht.1).trans hglU⟩, ?_⟩
      exact hpt.2.2.2.1.trans (by linarith only [hδ])
    let ψ := fun t => ℓ - Real.log (g t)
    let e := fun t => Real.log (q / (g t * Real.exp (a * t)))
    let A₁ := fun t => F (e t, g t) - C
    let E₀ := fun t => g t * Real.exp (k * t) *
      (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
        derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
          (Icc 0 U) (g t) - (r 0 - g t) * logarithmicIncoming b ℓ P (g t))
    let E₁ := fun t => A₁ t * P (ψ t)
    let E₂ := fun t => P (ψ t) - P (φ t)
    have hψc : ContinuousOn ψ (Icc l S) :=
      continuousOn_const.sub ((hgc.mono hsub).log (fun t ht => (hg t ht).1.1.ne'))
    have hφc : Continuous φ := by dsimp only [φ]; fun_prop
    have hdψ (t : ℝ) (ht : t ∈ Icc l S) : HasDerivAt ψ (-deriv g t / g t) t := by
      have hpt := hpoint t (hsub ht)
      simpa only [neg_div] using (hpt.2.1.hasDerivAt.log hpt.1.1.ne').const_sub ℓ
    have hdφ (t : ℝ) (_ht : t ∈ Icc l S) : HasDerivAt φ a t :=
      (((((hasDerivAt_id t).const_mul a).add_const ℓ).add_const (Real.log cν)).sub_const
        (Real.log (B.z Y))).congr_deriv (by simp)
    have heq (t : ℝ) (ht : t ∈ Icc l S) :
        e t = Real.log (B.z Y / (g t * (cν * Real.exp (a * t)))) := by
      dsimp only [e, q]
      congr 1
      ring
    have hphase (t : ℝ) (ht : t ∈ Icc l S) :
        |e t| < θ ε ∧ a / 2 ≤ -deriv g t / g t ∧ |ψ t - φ t| ≤ 1 ∧ |A₁ t| ≤ ρ ε * δ ^ b := by
      have hpt := hpoint t (hsub ht)
      have htτ : τ ε ≤ t := hl.trans ht.1
      have hh := hpt.2.2.2.2.2.2.1 (θ ε) ((le_max_left _ _).trans htτ)
      rw [← heq t ht] at hh
      have he' := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt hh
      have hspeed := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt hh |>.trans_le
        (show (θ ε : ℝ) ≤ a / 2 from (min_le_right _ _).trans (min_le_left _ _))
      have hphi : ψ t - φ t = e t := by
        rw [heq t ht, Real.log_div (B.z_pos hY).ne'
          (mul_pos hpt.1.1 (mul_pos hcν (Real.exp_pos _))).ne',
          Real.log_mul hpt.1.1.ne' (mul_pos hcν (Real.exp_pos _)).ne',
          Real.log_mul hcν.ne' (Real.exp_ne_zero _)]
        dsimp only [ψ, φ]
        simp only [Real.log_exp]
        ring
      have hgt : g t ≤ δ * Real.exp (-a * t) := by
        have hh' := mul_le_mul_of_nonneg_right (hg t ht).2 (Real.exp_pos (-a * t)).le
        simpa only [mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one] using hh'
      have hgs : g t < σ ε := hgt.trans_lt
        (hTg ε t (((le_max_right _ _).trans (le_max_right _ _)).trans htτ))
      have hsmall : |A₁ t| < ρ ε * δ ^ b := hnear ε (e t, g t) (by
        simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff,
          abs_of_pos hpt.1.1] using
          And.intro (he'.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hgs)
      refine ⟨he', ?_, ?_, hsmall.le⟩
      · have hh' := (abs_lt.1 hspeed).1
        linarith only [hh']
      · rw [hphi]
        exact he'.le.trans (min_le_left _ _)
    have hEi := htrans δ hδ hδt' U V hU hV hUR p hp ℓ P hkp hP hf x hx hfn
      l S g hl0 hlS hSV (hgc.mono hsub) hg
    have htime := timeChange_l2_bound hlS (half_pos ha) hψc hdψ (fun t ht => (hphase t ht).2.1) P.continuous hP
    have hE₂ := phaseChange_l2_bound hlS (half_pos ha) zero_le_one hφc.continuousOn hψc hdφ hdψ
      (fun _ _ => half_le_self ha.le) (fun t ht => (hphase t ht).2.1)
      (fun t ht => (hphase t ht).2.2.1) P.continuous D.continuous hd hD
    have hAc : ContinuousOn A₁ (Icc l S) := by
      have hep : ∀ t ∈ Icc l S, q / (g t * Real.exp (a * t)) ≠ 0 := fun t ht =>
        (div_pos hq (mul_pos (hg t ht).1.1 (Real.exp_pos _))).ne'
      have hec : ContinuousOn e (Icc l S) :=
        (continuousOn_const.div ((hgc.mono hsub).mul (by fun_prop))
          (fun t ht => (mul_pos (hg t ht).1.1 (Real.exp_pos _)).ne')).log hep
      exact (hFc.comp_continuousOn (hec.prodMk (hgc.mono hsub))).sub continuousOn_const
    have hE₁c : ContinuousOn E₁ (Icc l S) := hAc.mul (P.continuous.comp_continuousOn hψc)
    have hE₂c : ContinuousOn E₂ (Icc l S) :=
      (P.continuous.comp_continuousOn hψc).sub (P.continuous.comp_continuousOn hφc.continuousOn)
    have hE₁bound : (∫ t in l..S, E₁ t ^ 2) ≤ (ρ ε * δ ^ b) ^ 2 * ((∫ t, P t ^ 2) / (a / 2)) := by
      have hh := intervalIntegral.integral_mono_on (μ := volume) hlS
        ((hE₁c.pow 2).intervalIntegrable_of_Icc hlS)
        ((((P.continuous.comp_continuousOn hψc).pow 2).const_mul ((ρ ε * δ ^ b) ^ 2)).intervalIntegrable_of_Icc hlS)
        (fun t ht => by
          change (A₁ t * P (ψ t)) ^ 2 ≤ (ρ ε * δ ^ b) ^ 2 * P (ψ t) ^ 2
          rw [mul_pow]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity [hρ ε])).2 (hphase t ht).2.2.2)
      rw [intervalIntegral.integral_const_mul] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left htime (sq_nonneg _))
    have hfc : ContinuousOn (logarithmicIncoming b ℓ P) (Ioi 0) := by
      exact (continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl ht.ne'))).mul
        (P.continuous.comp_continuousOn (continuousOn_const.sub (continuousOn_id.log (fun t ht => ht.ne'))))
    have hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 0 = -1 := by
      filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
      rw [hu]; rfl
    have hif : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 1 = logarithmicIncoming b ℓ P u := by
      filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
      rw [hu]; rfl
    have hZc := hx.scalar_curve_continuous rfl hinu hfc hif (hgc.mono hsub) continuousOn_id (fun t ht => (hg t ht).1)
    have hEc : ContinuousOn E (Icc l S) := by
      exact (((hgc.mono hsub).mul (by fun_prop)).mul hZc).sub
        ((P.continuous.comp hφc).continuousOn.const_mul C)
    have hEeq (t : ℝ) (ht : t ∈ Icc l S) : E t = E₀ t + E₁ t + C * E₂ t := by
      have hh := logarithmicIncoming_phase_trace (hg t ht).1.1 hq hcrit ℓ P (v := t)
      have hh' := congrArg (fun z : ℝ => (r 0 - g t) * z) hh
      dsimp only [E, E₀, E₁, E₂, A₁, F, e, ψ]
      nlinarith only [hh']
    have hI₀ : IntervalIntegrable (fun t => E₀ t ^ 2) volume l S :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hlS).2 hEi.1
    have hI₁ : IntervalIntegrable (fun t => E₁ t ^ 2) volume l S := (hE₁c.pow 2).intervalIntegrable_of_Icc hlS
    have hI₂ : IntervalIntegrable (fun t => E₂ t ^ 2) volume l S := (hE₂c.pow 2).intervalIntegrable_of_Icc hlS
    have hsum := intervalIntegral.integral_mono_on (μ := volume) hlS
      ((hEc.pow 2).intervalIntegrable_of_Icc hlS)
      (((hI₀.const_mul 3).add (hI₁.const_mul 3)).add (hI₂.const_mul (3 * C ^ 2)))
      (fun t ht => show E t ^ 2 ≤ 3 * E₀ t ^ 2 + 3 * E₁ t ^ 2 + 3 * C ^ 2 * E₂ t ^ 2 from by
        rw [hEeq t ht]
        nlinarith only [sq_nonneg (E₀ t - E₁ t), sq_nonneg (E₀ t - C * E₂ t), sq_nonneg (E₁ t - C * E₂ t)])
    rw [intervalIntegral.integral_add ((hI₀.const_mul 3).add (hI₁.const_mul 3)) (hI₂.const_mul (3 * C ^ 2)),
      intervalIntegral.integral_add (hI₀.const_mul 3) (hI₁.const_mul 3),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hsum
    have hdpos : 0 < δ ^ (2 * b) := Real.rpow_pos_of_pos hδ _
    have hd2 : (δ ^ b) ^ (2 : ℕ) = δ ^ (2 * b) := by
      rw [← Real.rpow_natCast (δ ^ b) 2, ← Real.rpow_mul hδ.le]
      congr 1
      norm_num
      ring
    have hEnorm : 3 * (∫ t in l..S, E₁ t ^ 2) / δ ^ (2 * b) ≤ (ε : ℝ) * ∫ t, P t ^ 2 := by
      calc
        _ ≤ 3 * ((ρ ε * δ ^ b) ^ 2 * ((∫ t, P t ^ 2) / (a / 2))) / δ ^ (2 * b) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE₁bound (by norm_num)) hdpos.le
        _ = (6 * (ρ ε) ^ 2 / a) * ∫ t, P t ^ 2 := by rw [mul_pow, hd2]; field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).2 (hρsmall ε)) (integral_nonneg (fun t => sq_nonneg _))
    have hE₂norm : (3 * C ^ 2) * (∫ t in l..S, E₂ t ^ 2) / δ ^ (2 * b) ≤
        (6 * C ^ 2 / (a * δ ^ (2 * b))) * ∫ t, D t ^ 2 := by
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE₂.2 (by positivity : 0 ≤ 3 * C ^ 2)) hdpos.le
      exact hh.trans_eq (by norm_num; ring)
    refine ⟨(hEc.pow 2).integrableOn_Icc, ?_⟩
    have hh := div_le_div_of_nonneg_right hsum hdpos.le
    have hmain := mul_le_mul_of_nonneg_left hEi.2.2 (by norm_num : (0 : ℝ) ≤ 3)
    have hall := add_le_add (add_le_add hmain hEnorm) hE₂norm
    exact hh.trans (by convert hall using 1 <;> ring)

end Background

end CauchyHorizon
