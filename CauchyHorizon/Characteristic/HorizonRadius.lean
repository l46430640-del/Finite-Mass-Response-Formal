import CauchyHorizon.Characteristic.HorizonCollar
import CauchyHorizon.Characteristic.Outgoing
import CauchyHorizon.Analysis.WeightedTerminal

/-! Existence of the nonlinear RN-dS horizon radius with its terminal limit and decay. -/

open MeasureTheory Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace CauchyHorizon.Background

variable (B : CauchyHorizon.Background)

theorem exists_horizon_radius {d : ℝ} (hd : 0 < d) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ δ < B.event ∧
      ∀ z : ℝ → ℝ, ContinuousOn z (Ici 0) →
        (∀ t ∈ Ici (0 : ℝ), ‖z t‖ ≤ ε * Real.exp (-d * t)) →
        ∃ r : ℝ → ℝ, Continuous r ∧
          (∀ t, B.event - δ ≤ r t) ∧
          (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
            (horizonFunction (r t) (B.mass - z t) B.charge B.cosmological) (Ici 0) t) ∧
          (∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ δ * Real.exp (-d * t)) ∧
          Tendsto r atTop (nhds B.event) := by
  let c := B.outerRate + d
  have hc : 0 < c := add_pos B.outerRate_pos hd
  obtain ⟨δ, hδ, hδR, J, hg, hj⟩ := B.exists_horizon_collar hc
  let ε := min (c / (4 * ((J : ℝ) + 1)))
    (c * δ / (2 * (‖B.horizonCoupling 0‖ + 1)))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hsmall : c / 4 + ε * J ≤ c / 2 := by
    have hem : ε ≤ c / (4 * ((J : ℝ) + 1)) := min_le_left _ _
    have he := (le_div_iff₀ (by positivity : 0 < 4 * ((J : ℝ) + 1))).1
      hem
    nlinarith
  have hsize : ε * ‖B.horizonCoupling 0‖ ≤ c * δ / 2 := by
    have hem : ε ≤ c * δ / (2 * (‖B.horizonCoupling 0‖ + 1)) := min_le_right _ _
    have he := (le_div_iff₀ (by positivity : 0 < 2 * (‖B.horizonCoupling 0‖ + 1))).1
      hem
    nlinarith
  refine ⟨ε, δ, hε, hδ, hδR, ?_⟩
  intro z hz hzb
  let Z := rescaledFuture hz hzb
  let e := terminalWeight d
  let S := weightedTerminalSource hc hδ hg hj B.horizonRemainder_zero
    (terminalWeight_continuous d) (terminalWeight_pos d) (terminalWeight_le_one hd)
    Z (rescaledFuture_norm_le hε.le hz hzb) hsmall hsize
  obtain ⟨Y, hY, hDY, _⟩ := S.exists_solution
  change ‖Y‖ ≤ δ at hY
  let r := fun t => B.event - e t * Y t
  have he (t : ℝ) : 0 < e t := terminalWeight_pos d t
  have hy (t : ℝ) : ‖e t * Y t‖ ≤ δ := by
    rw [norm_mul, Real.norm_of_nonneg (he t).le]
    calc
      _ ≤ 1 * ‖Y t‖ := mul_le_mul_of_nonneg_right (terminalWeight_le_one hd t) (norm_nonneg _)
      _ ≤ δ := by simpa using (Y.norm_coe_le_norm t).trans hY
  have hrb (t : ℝ) : B.event - δ ≤ r t := by
    have h := (abs_le.1 (hy t)).2
    dsimp [r]
    linarith
  have hrdec (t : ℝ) (ht : 0 ≤ t) : ‖r t - B.event‖ ≤ δ * Real.exp (-d * t) := by
    change ‖B.event - e t * Y t - B.event‖ ≤ _
    rw [sub_sub_cancel_left, norm_neg, norm_mul, Real.norm_of_nonneg (he t).le]
    have hey : e t = Real.exp (-d * t) := terminalWeight_eq ht
    rw [hey]
    exact (mul_le_mul_of_nonneg_left ((Y.norm_coe_le_norm t).trans hY) (Real.exp_pos _).le).trans_eq
      (mul_comm _ _)
  refine ⟨r, continuous_const.sub ((terminalWeight_continuous d).mul Y.continuous), hrb, ?_,
    hrdec, ?_⟩
  · intro t ht
    have hyt := hDY t
    change HasDerivAt Y (c * Y t -
      (B.horizonRemainder (e t * Y t) / e t + Z t * B.horizonCoupling (e t * Y t))) t at hyt
    have hr := ((terminalWeight_hasDerivWithinAt d ht).mul hyt.hasDerivWithinAt).const_sub B.event
    have hZt : Z t = z t / e t := by
      change futureExtension z t / e t = _
      rw [futureExtension_eq ht]
    apply hr.congr_deriv
    change -(-d * e t * Y t + e t * (c * Y t -
      (B.horizonRemainder (e t * Y t) / e t + Z t * B.horizonCoupling (e t * Y t)))) = _
    rw [hZt]
    unfold horizonRemainder horizonCoupling F horizonFunction
    dsimp [r, c]
    field_simp [(he t).ne']
    ring
  · have hexp : Tendsto (fun t : ℝ => Real.exp (-d * t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hd))
    have hzero : Tendsto (fun t => r t - B.event) atTop (nhds 0) := by
      apply squeeze_zero_norm' _ (by simpa using hexp.const_mul δ)
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simpa only [neg_mul] using hrdec t ht
    simpa only [sub_add_cancel, zero_add] using hzero.add_const B.event

theorem exists_small_tail_horizon {s : ℝ} (hs : 0 < s) :
    ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧ δ < B.event ∧
      ∀ h : ℝ → ℝ, Continuous h →
        (∀ t, ‖h t‖ ≤ η * Real.exp (-s * t)) →
        ∃ r : ℝ → ℝ, Continuous r ∧
          (∀ t, B.event - δ ≤ r t) ∧
          (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
            (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t) ∧
          (∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ δ * Real.exp (-(2 * s) * t)) ∧
          Tendsto r atTop (nhds B.event) := by
  obtain ⟨ε, δ, hε, hδ, hδR, hsolve⟩ := B.exists_horizon_radius (by positivity : 0 < 2 * s)
  let η := Real.sqrt (4 * s * ε)
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hηsq : η ^ 2 / (4 * s) = ε := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ 4 * s * ε)]
    field_simp
  refine ⟨η, δ, hη, hδ, hδR, ?_⟩
  intro h hc hb
  have hi := horizon_mass_integrable hs hη.le hc hb
  have hm : Continuous (horizonMass B.mass h) := continuous_iff_continuousAt.2
    (fun t => (horizonMass_hasDerivAt hc hi B.mass t).continuousAt)
  let z := fun t => B.mass - horizonMass B.mass h t
  have hzb (t : ℝ) (_ht : t ∈ Ici (0 : ℝ)) : ‖z t‖ ≤ ε * Real.exp (-(2 * s) * t) := by
    obtain ⟨hpos, hbound⟩ := horizonMass_bounds hs hη.le hb B.mass t
    rw [hηsq] at hbound
    simpa only [z, Real.norm_of_nonneg hpos] using hbound
  obtain ⟨r, hrc, hrb, hrd, hrdec, hrend⟩ := hsolve z (continuous_const.sub hm).continuousOn hzb
  refine ⟨r, hrc, hrb, ?_, hrdec, hrend⟩
  intro t ht
  simpa only [z, sub_sub_cancel] using hrd t ht

theorem exists_late_tail_horizon {s H : ℝ} (hs : 0 < s) (hH : 0 ≤ H)
    {h : ℝ → ℝ} (hc : ContinuousOn h (Ici 0))
    (hb : ∀ t ∈ Ici (0 : ℝ), ‖h t‖ ≤ H * Real.exp (-s * t)) :
    ∃ T δ : ℝ, 0 ≤ T ∧ 0 < δ ∧ δ < B.event ∧
      ∃ r : ℝ → ℝ, Continuous r ∧
        (∀ t, B.event - δ ≤ r t) ∧
        (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
          (horizonFunction (r t) (horizonMass B.mass (fun w => h (w + T)) t)
            B.charge B.cosmological) (Ici 0) t) ∧
        (∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ δ * Real.exp (-(2 * s) * t)) ∧
        Tendsto r atTop (nhds B.event) := by
  obtain ⟨η, δ, hη, hδ, hδR, hsolve⟩ := B.exists_small_tail_horizon hs
  have hexp : Tendsto (fun T : ℝ => Real.exp (-s * T)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hs))
  have hlim : Tendsto (fun T : ℝ => H * Real.exp (-s * T)) atTop (nhds 0) := by
    simpa using hexp.const_mul H
  obtain ⟨T, hT0, hTη⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hlim.eventually (Iio_mem_nhds hη))).exists
  let hT := fun w => futureExtension h (w + T)
  have hTc : Continuous hT := (futureExtension_continuous hc).comp
    (continuous_id.add continuous_const)
  have hTb (w : ℝ) : ‖hT w‖ ≤ η * Real.exp (-s * w) := by
    calc
      _ ≤ H * Real.exp (-s * (w + T)) := futureExtension_exponential_bound hs hH hb (w + T)
      _ = (H * Real.exp (-s * T)) * Real.exp (-s * w) := by
        rw [show -s * (w + T) = -s * T + -s * w by ring, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hTη.le (Real.exp_pos _).le
  obtain ⟨r, hrc, hrb, hrd, hrdec, hrend⟩ := hsolve hT hTc hTb
  refine ⟨T, δ, hT0, hδ, hδR, r, hrc, hrb, ?_, hrdec, hrend⟩
  intro t ht
  have heq : (fun w => hT w ^ 2) =ᵐ[volume.restrict (Ioi t)] (fun w => h (w + T) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    dsimp [hT]
    rw [futureExtension_eq (add_nonneg (le_of_lt (lt_of_le_of_lt ht hw)) hT0)]
  have hmass : horizonMass B.mass hT t = horizonMass B.mass (fun w => h (w + T)) t :=
    congrArg (fun x => B.mass - x / 2) (integral_congr_ae heq)
  simpa only [hmass] using hrd t ht

end CauchyHorizon.Background
