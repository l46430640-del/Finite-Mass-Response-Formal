import CauchyHorizon.Characteristic.HorizonRates

/-! The outgoing characteristic estimates, discharged for the nonlinear radius. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon.Background

variable (B : Background)

def OutgoingEstimates (h r : ℝ → ℝ) (s : ℝ) : Prop :=
  let K := fun t => horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological
  let L := fun t => horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological
  (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ici (0 : ℝ), ‖K t - B.outerRate / 2‖ ≤ C * Real.exp (-(2 * s) * t)) ∧
    IntegrableOn (fun t => 2 * K t - B.outerRate) (Ioi 0) ∧
    Tendsto (fun t => Real.exp (-B.outerRate * t) * (-horizonNu K t)) atTop
      (𝓝 (Real.exp (∫ t in Ioi 0, 2 * K t - B.outerRate))) ∧
    (∀ t ∈ Ici (0 : ℝ), L t = ∫ w in Ioi t, Real.exp (-(∫ x in t..w, 2 * K x)) * (h w ^ 2 / r w)) ∧
    (∀ t ∈ Ici (0 : ℝ), 0 < L t) ∧
    (∀ t ∈ Ioi (0 : ℝ),
      deriv (deriv r) t - deriv (horizonLogOmega K) t * deriv r t =
        -r t * (deriv (horizonPhi h r) t) ^ 2)

theorem OutgoingEstimates.nu_bounds {B : Background} {h r : ℝ → ℝ} {s : ℝ}
    (hOut : B.OutgoingEstimates h r s) (hs : 0 < s) (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) :
    ∃ n N : ℝ, 0 < n ∧ n ≤ 1 ∧ 1 ≤ N ∧
      ∀ t ∈ Ici (0 : ℝ),
        n * Real.exp (B.outerRate * t) ≤
          -horizonNu (fun w => horizonK (r w) (horizonMass B.mass h w) B.charge B.cosmological) t ∧
        -horizonNu (fun w => horizonK (r w) (horizonMass B.mass h w) B.charge B.cosmological) t ≤
          N * Real.exp (B.outerRate * t) := by
  obtain ⟨C, hC, hb⟩ := hOut.1
  have hmc : Continuous (horizonMass B.mass h) := continuous_iff_continuousAt.2
    (fun t => (horizonMass_hasDerivAt hc hi B.mass t).continuousAt)
  have hK := horizonK_continuous hrc hmc hr0 B.charge B.cosmological
  refine ⟨Real.exp (-(2 * C) / (2 * s)), Real.exp ((2 * C) / (2 * s)), Real.exp_pos _,
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith only [hC]) (by positivity)),
    Real.one_le_exp_iff.2 (by positivity), ?_⟩
  intro t ht
  apply horizonNu_exponential_bounds hK (by positivity) (by positivity : 0 ≤ 2 * C) ?_ ht
  intro w hw
  rw [show 2 * horizonK (r w) (horizonMass B.mass h w) B.charge B.cosmological - B.outerRate =
    2 * (horizonK (r w) (horizonMass B.mass h w) B.charge B.cosmological - B.outerRate / 2) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact (mul_le_mul_of_nonneg_left (hb w hw) (by norm_num)).trans_eq (by ring)

theorem outgoing_estimates_of_radius {s H δ : ℝ} (hs : 0 < s) (hH : 0 ≤ H)
    (hδ : 0 ≤ δ) (hδR : δ < B.event) {h r : ℝ → ℝ} (hc : Continuous h)
    (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t)) (hp : ∀ t ∈ Ici (0 : ℝ), 0 < h t)
    (hrc : Continuous r) (hrb : ∀ t, B.event - δ ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ δ * Real.exp (-(2 * s) * t))
    (hrend : Tendsto r atTop (𝓝 B.event)) : B.OutgoingEstimates h r s := by
  let m := horizonMass B.mass h
  let K := fun t => horizonK (r t) (m t) B.charge B.cosmological
  let L := fun t => horizonFunction (r t) (m t) B.charge B.cosmological
  have hm := horizon_mass_integrable hs hH hc hb
  have hmc : Continuous m := continuous_iff_continuousAt.2
    (fun t => (horizonMass_hasDerivAt hc hm B.mass t).continuousAt)
  have hrpos (t : ℝ) : 0 < r t := (sub_pos.2 hδR).trans_le (hrb t)
  have hK : Continuous K := horizonK_continuous hrc hmc (fun t => (hrpos t).ne') _ _
  have hL : Continuous L := by
    dsimp [L, horizonFunction]
    fun_prop (disch := intro t; have := hrpos t; positivity)
  have hF : ContinuousAt (fun p : ℝ × ℝ => horizonFunction p.1 p.2 B.charge B.cosmological)
      (B.event, B.mass) := by
    have hR := B.event_pos
    unfold horizonFunction
    fun_prop (disch := positivity)
  have hLend : Tendsto L atTop (𝓝 0) := by
    have hh := hF.tendsto.comp (hrend.prodMk_nhds (horizonMass_tendsto hs hH hb B.mass))
    simpa only [Function.comp_def, B.root_event] using hh
  have hdr (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : HasDerivAt r (L t) t :=
    (hrd t (show (0 : ℝ) ≤ t from le_of_lt ht)).hasDerivAt (Ici_mem_nhds ht)
  have hdL (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt L (2 * K t * L t - h t ^ 2 / r t) t := by
    exact (horizonFunction_hasDerivAt (hdr t ht) (horizonMass_hasDerivAt hc hm B.mass t)
      (hrpos t).ne' B.charge B.cosmological).congr_deriv (by dsimp [K]; ring)
  obtain ⟨hbound, hint⟩ := B.horizonK_remainder hs hH hδ hδR hc hb hrc hrb hrdec
  refine ⟨hbound, hint, horizonNu_exact_amplitude hK hint, ?_, ?_, ?_⟩
  · intro t ht
    exact (terminal_linear_representation B.outerRate_pos hK hint hL hLend hdL
      (fun w _ => div_nonneg (sq_nonneg _) (hrpos w).le) ht).2
  · intro t ht
    exact terminal_linear_pos B.outerRate_pos hK hint hL hLend hdL
      (fun w hw => div_pos (sq_pos_of_pos (hp w hw)) (hrpos w)) ht
  · intro t ht
    exact outgoing_constraint hc hm hrc hdr (fun w => (hrpos w).ne')
      (horizonPhi_integrable hs hH (sub_pos.2 hδR) hc hrc hb hrb) ht

theorem exists_small_tail_outgoing_data {s : ℝ} (hs : 0 < s) :
    ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧ δ < B.event ∧
      ∀ h : ℝ → ℝ, Continuous h →
        (∀ t, ‖h t‖ ≤ η * Real.exp (-s * t)) → (∀ t ∈ Ici (0 : ℝ), 0 < h t) →
        ∃ r : ℝ → ℝ, Continuous r ∧
          (∀ t, B.event - δ ≤ r t) ∧
          (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
            (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t) ∧
          (∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ δ * Real.exp (-(2 * s) * t)) ∧
          Tendsto r atTop (𝓝 B.event) ∧ B.OutgoingEstimates h r s := by
  obtain ⟨η, δ, hη, hδ, hδR, hsolve⟩ := B.exists_small_tail_horizon hs
  refine ⟨η, δ, hη, hδ, hδR, ?_⟩
  intro h hc hb hp
  obtain ⟨r, hrc, hrb, hrd, hrdec, hrend⟩ := hsolve h hc hb
  exact ⟨r, hrc, hrb, hrd, hrdec, hrend,
    B.outgoing_estimates_of_radius hs hη.le hδ.le hδR hc hb hp hrc hrb hrd hrdec hrend⟩

theorem exists_late_outgoing_data {s H : ℝ} (hs : 0 < s) (hH : 0 ≤ H)
    {h : ℝ → ℝ} (hc : ContinuousOn h (Ici 0))
    (hb : ∀ t ∈ Ici (0 : ℝ), ‖h t‖ ≤ H * Real.exp (-s * t))
    (hp : ∀ t ∈ Ici (0 : ℝ), 0 < h t) :
    ∃ T δ : ℝ, 0 ≤ T ∧ 0 < δ ∧ δ < B.event ∧
      ∃ g r : ℝ → ℝ, Continuous g ∧ (∀ t ∈ Ici (0 : ℝ), g t = h (t + T)) ∧
        Continuous r ∧ (∀ t, B.event - δ ≤ r t) ∧
        (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
          (horizonFunction (r t) (horizonMass B.mass g t) B.charge B.cosmological) (Ici 0) t) ∧
        (∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ δ * Real.exp (-(2 * s) * t)) ∧
        Tendsto r atTop (𝓝 B.event) ∧ B.OutgoingEstimates g r s := by
  have hec := futureExtension_continuous hc
  have heb := futureExtension_exponential_bound hs hH hb
  obtain ⟨T, δ, hT, hδ, hδR, r, hrc, hrb, hrd, hrdec, hrend⟩ :=
    B.exists_late_tail_horizon hs hH hec.continuousOn (fun t _ => heb t)
  let g := fun t => futureExtension h (t + T)
  have hgc : Continuous g := hec.comp (continuous_id.add continuous_const)
  have hgeq (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : g t = h (t + T) :=
    futureExtension_eq (add_nonneg ht hT)
  have hgb (t : ℝ) : ‖g t‖ ≤ (H * Real.exp (-s * T)) * Real.exp (-s * t) := by
    apply (heb (t + T)).trans_eq
    rw [show -s * (t + T) = -s * T + -s * t by ring, Real.exp_add]
    ring
  have hgp (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : 0 < g t := by
    rw [hgeq t ht]
    exact hp (t + T) (add_nonneg ht hT)
  exact ⟨T, δ, hT, hδ, hδR, g, r, hgc, hgeq, hrc, hrb, hrd, hrdec, hrend,
    B.outgoing_estimates_of_radius hs (by positivity) hδ.le hδR hgc hgb hgp
      hrc hrb hrd hrdec hrend⟩

end CauchyHorizon.Background
