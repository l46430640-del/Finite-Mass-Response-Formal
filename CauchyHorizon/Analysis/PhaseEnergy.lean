import CauchyHorizon.Analysis.LogarithmicMatching

/-! Profile energy under two nearby increasing phases. -/

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem phaseChange_l2_bound {l S η ε : ℝ} {φ ψ φ' ψ' P D : ℝ → ℝ}
    (hlS : l ≤ S) (hη : 0 < η) (hε : 0 ≤ ε)
    (hφ : ContinuousOn φ (Icc l S)) (hψ : ContinuousOn ψ (Icc l S))
    (hdφ : ∀ t ∈ Icc l S, HasDerivAt φ (φ' t) t)
    (hdψ : ∀ t ∈ Icc l S, HasDerivAt ψ (ψ' t) t)
    (hbφ : ∀ t ∈ Icc l S, η ≤ φ' t) (hbψ : ∀ t ∈ Icc l S, η ≤ ψ' t)
    (hclose : ∀ t ∈ Icc l S, |ψ t - φ t| ≤ ε)
    (hP : Continuous P) (hD : Continuous D) (hd : ∀ x, HasDerivAt P (D x) x)
    (hDi : Integrable (fun x => D x ^ 2)) :
    IntegrableOn (fun t => (P (ψ t) - P (φ t)) ^ 2) (Icc l S) ∧
      (∫ t in l..S, (P (ψ t) - P (φ t)) ^ 2) ≤ ε ^ 2 / η * ∫ x, D x ^ 2 := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let ν := volume.restrict (Icc l S)
  let q := fun (θ t : ℝ) => φ t + θ * (ψ t - φ t)
  let K := fun p : ℝ × ℝ => D (q p.1 p.2) ^ 2
  have hqc (θ : ℝ) : ContinuousOn (q θ) (Icc l S) := hφ.add ((hψ.sub hφ).const_mul θ)
  have hKc : ContinuousOn K ((Icc (0 : ℝ) 1) ×ˢ Icc l S) := by
    have hφt : ContinuousOn (fun p : ℝ × ℝ => φ p.2) ((Icc (0 : ℝ) 1) ×ˢ Icc l S) :=
      hφ.comp continuous_snd.continuousOn (fun _ ht => ht.2)
    have hψt : ContinuousOn (fun p : ℝ × ℝ => ψ p.2) ((Icc (0 : ℝ) 1) ×ˢ Icc l S) :=
      hψ.comp continuous_snd.continuousOn (fun _ ht => ht.2)
    exact (hD.comp_continuousOn (hφt.add (continuous_fst.continuousOn.mul (hψt.sub hφt)))).pow 2
  have hKi : Integrable K (μ.prod ν) := by
    rw [show μ.prod ν = (volume.prod volume).restrict ((Icc (0 : ℝ) 1) ×ˢ Icc l S)
      from Measure.prod_restrict _ _]
    exact hKc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hrow (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (∫ t, K (θ, t) ∂ν) ≤ (∫ x, D x ^ 2) / η := by
    have hqd (t : ℝ) (ht : t ∈ Icc l S) :
        HasDerivAt (q θ) (φ' t + θ * (ψ' t - φ' t)) t :=
      (hdφ t ht).add (((hdψ t ht).sub (hdφ t ht)).const_mul θ)
    have hqb (t : ℝ) (ht : t ∈ Icc l S) : η ≤ φ' t + θ * (ψ' t - φ' t) := by
      have h₁ := mul_nonneg (sub_nonneg.2 hθ.2) (sub_nonneg.2 (hbφ t ht))
      have h₂ := mul_nonneg hθ.1 (sub_nonneg.2 (hbψ t ht))
      nlinarith only [h₁, h₂]
    have hh := timeChange_l2_bound hlS hη (hqc θ) hqd hqb hD hDi
    simpa only [intervalIntegral.integral_of_le hlS, ν, integral_Icc_eq_integral_Ioc, K] using hh
  have hmean (t : ℝ) :
      P (ψ t) - P (φ t) = (ψ t - φ t) * ∫ θ, D (q θ t) ∂μ := by
    have hqd (θ : ℝ) : HasDerivAt (fun z => q z t) (ψ t - φ t) θ :=
      (((hasDerivAt_id θ).mul_const (ψ t - φ t)).const_add (φ t)).congr_deriv (by simp)
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun θ _ => (hd (q θ t)).comp θ (hqd θ))
      (show IntervalIntegrable (fun θ => D (q θ t) * (ψ t - φ t)) volume 0 1 from
        (by fun_prop : Continuous (fun θ => D (q θ t) * (ψ t - φ t))).intervalIntegrable _ _)
    simp only [Function.comp_def, q, zero_mul, add_zero, one_mul, add_sub_cancel] at hi
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc] at hi
    simpa only [μ, q, mul_comm] using hi.symm
  have hJensen (t : ℝ) : (∫ θ, D (q θ t) ∂μ) ^ 2 ≤ ∫ θ, K (θ, t) ∂μ := by
    let m := ∫ θ, D (q θ t) ∂μ
    have hc : Continuous (fun θ => D (q θ t)) := by fun_prop
    have hi : Integrable (fun θ => D (q θ t)) μ := hc.integrableOn_Icc
    have hi2 : Integrable (fun θ => D (q θ t) ^ 2) μ := (hc.pow 2).integrableOn_Icc
    have hn : 0 ≤ ∫ θ, (D (q θ t) - m) ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
    have he (θ : ℝ) : (D (q θ t) - m) ^ 2 = D (q θ t) ^ 2 - (2 * m) * D (q θ t) + m ^ 2 := by ring
    simp_rw [he] at hn
    have hisub : Integrable (fun θ => D (q θ t) ^ 2 - (2 * m) * D (q θ t)) μ :=
      hi2.sub (hi.const_mul (2 * m))
    rw [integral_add hisub (integrable_const (m ^ 2)),
      integral_sub hi2 (hi.const_mul (2 * m)), integral_const_mul] at hn
    have hm : (∫ _ : ℝ, m ^ 2 ∂μ) = m ^ 2 := by simp [μ]
    rw [hm] at hn
    change m ^ 2 ≤ ∫ θ, D (q θ t) ^ 2 ∂μ
    change 0 ≤ (∫ θ, D (q θ t) ^ 2 ∂μ) - 2 * m * m + m ^ 2 at hn
    nlinarith only [hn]
  have hpt (t : ℝ) (ht : t ∈ Icc l S) :
      (P (ψ t) - P (φ t)) ^ 2 ≤ ε ^ 2 * ∫ θ, K (θ, t) ∂μ := by
    rw [hmean, mul_pow]
    have hb := (sq_le_sq₀ (abs_nonneg _) hε).2 (hclose t ht)
    rw [sq_abs] at hb
    exact (mul_le_mul_of_nonneg_left (hJensen t) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hb (integral_nonneg (fun _ => sq_nonneg _)))
  have hE : IntegrableOn (fun t => (P (ψ t) - P (φ t)) ^ 2) (Icc l S) :=
    ((hP.comp_continuousOn hψ).sub (hP.comp_continuousOn hφ)).pow 2 |>.integrableOn_Icc
  have hdouble : (∫ t, ∫ θ, K (θ, t) ∂μ ∂ν) ≤ (∫ x, D x ^ 2) / η := by
    rw [← integral_integral_swap hKi]
    have hh := integral_mono_ae hKi.integral_prod_left (integrable_const ((∫ x, D x ^ 2) / η))
      ((ae_restrict_mem measurableSet_Icc).mono (fun θ hθ => hrow θ hθ))
    simpa only [μ, integral_const, measureReal_restrict_apply_univ, Real.volume_real_Icc,
      sub_zero, max_eq_left zero_le_one, one_smul] using hh
  refine ⟨hE, ?_⟩
  rw [intervalIntegral.integral_of_le hlS, ← integral_Icc_eq_integral_Ioc]
  have hh := integral_mono_ae hE (hKi.integral_prod_right.const_mul (ε ^ 2))
    ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hpt t ht))
  rw [integral_const_mul] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left hdouble (sq_nonneg ε))).trans_eq (by ring)

theorem phaseChange_l2_halfline {l η ε : ℝ} {φ ψ φ' ψ' P D : ℝ → ℝ}
    (hη : 0 < η) (hε : 0 ≤ ε)
    (hφ : ContinuousOn φ (Ici l)) (hψ : ContinuousOn ψ (Ici l))
    (hdφ : ∀ t ∈ Ici l, HasDerivAt φ (φ' t) t)
    (hdψ : ∀ t ∈ Ici l, HasDerivAt ψ (ψ' t) t)
    (hbφ : ∀ t ∈ Ici l, η ≤ φ' t) (hbψ : ∀ t ∈ Ici l, η ≤ ψ' t)
    (hclose : ∀ t ∈ Ici l, |ψ t - φ t| ≤ ε)
    (hP : Continuous P) (hD : Continuous D) (hd : ∀ x, HasDerivAt P (D x) x)
    (hDi : Integrable (fun x => D x ^ 2)) :
    MemLp (fun t => P (ψ t) - P (φ t)) 2 (volume.restrict (Ici l)) ∧
      (∫ t in Ici l, (P (ψ t) - P (φ t)) ^ 2) ≤ ε ^ 2 / η * ∫ x, D x ^ 2 := by
  let E := fun t => P (ψ t) - P (φ t)
  have hEc : ContinuousOn E (Ici l) := (hP.comp_continuousOn hψ).sub (hP.comp_continuousOn hφ)
  have hfinite (S : ℝ) (hS : l ≤ S) : (∫ t in l..S, E t ^ 2) ≤ ε ^ 2 / η * ∫ x, D x ^ 2 :=
    (phaseChange_l2_bound hS hη hε (hφ.mono Icc_subset_Ici_self) (hψ.mono Icc_subset_Ici_self)
      (fun t ht => hdφ t ht.1) (fun t ht => hdψ t ht.1)
      (fun t ht => hbφ t ht.1) (fun t ht => hbψ t ht.1)
      (fun t ht => hclose t ht.1) hP hD hd hDi).2
  have hlocal (S : ℝ) : IntegrableOn (fun t => E t ^ 2) (Ioc l S) := by
    by_cases hS : l ≤ S
    · exact (((hEc.pow 2).mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · rw [Ioc_eq_empty (not_lt.2 (le_of_not_ge hS))]
      exact integrableOn_empty
  have hi : IntegrableOn (fun t => E t ^ 2) (Ioi l) :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded (ε ^ 2 / η * ∫ x, D x ^ 2) l hlocal tendsto_id (by
      filter_upwards [eventually_ge_atTop l] with S hS
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hfinite S hS)
  refine ⟨(memLp_two_iff_integrable_sq_norm (hEc.aestronglyMeasurable measurableSet_Ici)).2 ?_, ?_⟩
  · have hh := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 hi
    change Integrable (fun t => E t ^ 2) (volume.restrict (Ici l)) at hh
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  · rw [integral_Ici_eq_integral_Ioi]
    exact le_of_tendsto (intervalIntegral_tendsto_integral_Ioi (μ := volume) l hi tendsto_id)
      ((eventually_ge_atTop l).mono (fun S hS => hfinite S hS))

theorem terminalGreen_phase_error_energy {l S η ε c : ℝ} {φ ψ φ' ψ' : ℝ → ℝ}
    (hlS : l ≤ S) (hη : 0 < η) (hε : 0 ≤ ε) (hc : 0 < c)
    (hφ : ContinuousOn φ (Icc l S)) (hψ : ContinuousOn ψ (Icc l S))
    (hdφ : ∀ t ∈ Icc l S, HasDerivAt φ (φ' t) t)
    (hdψ : ∀ t ∈ Icc l S, HasDerivAt ψ (ψ' t) t)
    (hbφ : ∀ t ∈ Icc l S, η ≤ φ' t) (hbψ : ∀ t ∈ Icc l S, η ≤ ψ' t)
    (hclose : ∀ t ∈ Icc l S, |ψ t - φ t| ≤ ε)
    (P D : ℝ →ᵇ ℝ) (hd : ∀ x, HasDerivAt P (D x) x) (hDi : Integrable (fun x => D x ^ 2)) :
    IntegrableOn (fun t => (c * terminalGreen hc P (ψ t) - P (φ t)) ^ 2) (Icc l S) ∧
      (∫ t in l..S, (c * terminalGreen hc P (ψ t) - P (φ t)) ^ 2) ≤
        (2 / η) * ((1 / c) ^ 2 + ε ^ 2) * ∫ x, D x ^ 2 := by
  let Q := fun x => c * terminalGreen hc P x - P x
  let E := fun t => P (ψ t) - P (φ t)
  have hQc : Continuous Q := by dsimp only [Q]; fun_prop
  have hEc : ContinuousOn E (Icc l S) :=
    (P.continuous.comp_continuousOn hψ).sub (P.continuous.comp_continuousOn hφ)
  have hQt : ContinuousOn (fun t => Q (ψ t)) (Icc l S) := hQc.comp_continuousOn hψ
  obtain ⟨hQi, hQE⟩ := terminalGreen_approximation_energy hc P D hd hDi
  have htime := timeChange_l2_bound hlS hη hψ hdψ hbψ hQc hQi
  have hQbound : (∫ t in l..S, Q (ψ t) ^ 2) ≤ ((1 / c) ^ 2 * ∫ x, D x ^ 2) / η :=
    htime.trans (div_le_div_of_nonneg_right hQE hη.le)
  have hEbound := (phaseChange_l2_bound hlS hη hε hφ hψ hdφ hdψ hbφ hbψ hclose
    P.continuous D.continuous hd hDi).2
  have hfull : ContinuousOn (fun t => c * terminalGreen hc P (ψ t) - P (φ t)) (Icc l S) :=
    ((terminalGreen hc P).continuous.comp_continuousOn hψ).const_mul c |>.sub
      (P.continuous.comp_continuousOn hφ)
  have hh := intervalIntegral.integral_mono_on (μ := volume) hlS
    ((hfull.pow 2).intervalIntegrable_of_Icc hlS)
    ((((hQt.pow 2).const_mul 2).add ((hEc.pow 2).const_mul 2)).intervalIntegrable_of_Icc hlS)
    (fun t _ => show (c * terminalGreen hc P (ψ t) - P (φ t)) ^ 2 ≤
        2 * Q (ψ t) ^ 2 + 2 * E t ^ 2 from by
      have he : c * terminalGreen hc P (ψ t) - P (φ t) = Q (ψ t) + E t := by dsimp only [Q, E]; ring
      rw [he]
      nlinarith only [sq_nonneg (Q (ψ t) - E t)])
  simp only [Pi.add_apply, Pi.pow_apply] at hh
  have hI₁ : IntervalIntegrable (fun t => 2 * Q (ψ t) ^ 2) volume l S :=
    ((hQt.pow 2).intervalIntegrable_of_Icc hlS).const_mul 2
  have hI₂ : IntervalIntegrable (fun t => 2 * E t ^ 2) volume l S :=
    ((hEc.pow 2).intervalIntegrable_of_Icc hlS).const_mul 2
  rw [intervalIntegral.integral_add hI₁ hI₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hh
  refine ⟨(hfull.pow 2).integrableOn_Icc, hh.trans ?_⟩
  calc
    _ ≤ 2 * (((1 / c) ^ 2 * ∫ x, D x ^ 2) / η) + 2 * (ε ^ 2 / η * ∫ x, D x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hQbound (by norm_num))
        (mul_le_mul_of_nonneg_left hEbound (by norm_num))
    _ = _ := by ring

end CauchyHorizon
