import CauchyHorizon.Characteristic.PrefixFeedback
import CauchyHorizon.Characteristic.EarlyConstraint
import CauchyHorizon.Characteristic.ConformalBound

/-! Join pre-entry and early-region energies in the actual lapse and conformal error. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_constraint_join {M e Λ U V A B : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (z u : Icc 0 U) (hzu : z ≤ u) (v : Icc 0 V) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let S := fun t => intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU ν t v)
    let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
    (∫ t in (0 : ℝ)..z, S t) ≤ A → (∫ t in (z : ℝ)..u, S t) ≤ B →
      (∫ t in (0 : ℝ)..u, S t) ≤ A + B ∧ Real.exp (-(A + B)) ≤ κ ∧ |κ - 1| ≤ A + B := by
  dsimp only
  intro hleft hright
  obtain ⟨hSi, hk⟩ := hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
  have h0z : uIcc (0 : ℝ) z ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le z.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl z.property.2
  have hzu' : uIcc (z : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le (show (z : ℝ) ≤ u from hzu), uIcc_of_le hU]
    exact Icc_subset_Icc z.property.1 u.property.2
  have hQ := add_le_add hleft hright
  rw [intervalIntegral.integral_add_adjacent_intervals (hSi.mono_set h0z) (hSi.mono_set hzu')] at hQ
  have hκ := (Real.exp_le_exp.2 (neg_le_neg hQ)).trans_eq (hk u).symm
  refine ⟨hQ, hκ, ?_⟩
  have hκ1 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.2.2
  rw [abs_of_nonpos (sub_nonpos.2 hκ1)]
  have he := Real.add_one_le_exp (-(A + B))
  linarith only [hκ, he]

end CauchyHorizon

namespace CauchyHorizon.Background

set_option maxHeartbeats 1200000 in
theorem exists_early_geometric_feedback (B : Background)
    {s H dH A Apt ρ D₀ D c k ε κ₀ β n N He Kmax : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hApt : 0 ≤ Apt) (hρ : 0 < ρ) (hρR : ρ ≤ B.event + dH) (hD₀ : 0 ≤ D₀) (hD : 0 ≤ D)
    (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k) (hβ : 0 ≤ β)
    (hn : 0 < n) (hN : 0 ≤ N) (hHe : 0 ≤ He) (hKmax : 0 ≤ Kmax)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hcb : c ≤ B.outerRate * (1 - 1 / p.toReal))
    (hmargin : 0 < 2 * (B.outerRate / (1 + β)) * (c / B.outerRate) -
      2 * (k + ε) * β / (1 + β))
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let ω := B.outerRate / (1 + β)
    let γ := 2 * (k + ε) * β / (1 + β)
    let η := min (min B.outerRate (2 * c))
      (min (2 * ω * (1 - 1 / p.toReal) - γ) (2 * ω * (c / B.outerRate) - γ))
    ∃ U₀ C T₀ : ℝ, 0 < U₀ ∧ U₀ ≤ r 0 / 4 ∧ 0 ≤ C ∧ 0 ≤ T₀ ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        (∀ᵐ y ∂volume.restrict (Icc 0 U), |f y| ≤ Apt * y ^ (-1 / p.toReal)) → U ≤ U₀ →
        ∀ z : Icc 0 U, (∀ w ≤ z, ∀ v, ρ ≤ x.1 w v 0) →
          (z : ℝ) * Real.exp (B.outerRate * V) ≤ D₀ →
          let u : Icc 0 U := ⟨U, hU, le_rfl⟩
          let v : Icc 0 V := ⟨V, hV, le_rfl⟩
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
          let K := fun w t => horizonK (x.1 w t 0) (m w t) B.charge B.cosmological
          let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
          (∀ w, ρ ≤ x.1 w v 0 ∧ x.1 w v 0 ≤ B.event + dH) →
          U * Real.exp (ω * V) ≤ D → |K u v| ≤ Kmax →
          (∀ y ∈ Ioc (z : ℝ) U,
            let w := projIcc 0 U hU y
            ∃ T : Icc 0 V, T ≤ v ∧ V ≤ (1 + β) * T ∧ x.2.1 w T 0 < 0 ∧
              n ≤ y * (-ν w T) ∧ y * Real.exp (B.outerRate * T) ≤ D ∧
              (∀ t ≤ T, |ν w t| ≤ N * Real.exp (B.outerRate * t)) ∧
              (∀ t ≤ v, |x.2.1 w t 1| ≤ He * Real.exp (-c * t)) ∧
              (∀ t ∈ Icc T v, κ₀ ≤ -Real.exp (x.1 w t 2) / (4 * ν w t)) ∧
              (∀ t ∈ Icc T v, |K w t + k| ≤ ε)) →
            (∫ y in (0 : ℝ)..U, intervalExtension hU x.1 y v 0 * (x.2.2 y v 1) ^ 2 /
              (-intervalExtension hU ν y v)) ≤ C * Real.exp (-η * V) ∧
            |κ - 1| + |x.2.1 u v 2 - 2 * K u v| ≤ C * Real.exp (-η * V) ∧
            (T₀ ≤ V → 3 / 4 ≤ κ) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let R := B.event + dH
  have hR : 0 ≤ R := hρ.le.trans hρR
  let ω := B.outerRate / (1 + β)
  let γ := 2 * (k + ε) * β / (1 + β)
  let ξ := 1 - 1 / p.toReal
  let χ := c / B.outerRate
  let η := min (min B.outerRate (2 * c)) (min (2 * ω * ξ - γ) (2 * ω * χ - γ))
  have hξ : 0 < ξ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (incoming_exponent_bounds hp).1
  have hχ : 0 < χ := div_pos hc0 B.outerRate_pos
  have hω : 0 < ω := div_pos B.outerRate_pos (by linarith only [hβ])
  have hχξ : χ ≤ ξ := (div_le_iff₀ B.outerRate_pos).2 (by simpa only [mul_comm] using hcb)
  have hηf : 0 < 2 * ω * ξ - γ := hmargin.trans_le
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hχξ (by positivity : 0 ≤ 2 * ω)) γ)
  have hη : 0 < η := lt_min (lt_min B.outerRate_pos (by positivity)) (lt_min hηf hmargin)
  obtain ⟨U₀, C₀, E, hU₀, hU₀r, hC₀, hE, hprefix⟩ :=
    B.exists_prefix_feedback_decay hs hH hdH hdHR hA hρ hρR hD₀ hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  obtain ⟨P, hP, hpot⟩ := radialPotential_bounded B.charge B.cosmological (R := R) hρ
  let F := r 0 * Apt / ρ
  let G := (N * He / ρ) * (1 / (B.outerRate - c) + 1 / (2 * κ₀ * (k - ε) + c)) * D ^ (1 - c / B.outerRate)
  let Cf := F ^ 2 * D ^ (2 * ξ) / ξ
  let Ch := G ^ 2 * D ^ (2 * χ) / χ
  let Ci := (R / n) * (Cf + Ch)
  let Cq := C₀ + Ci
  let Hrow := E + He
  let Ck := 2 * Kmax + (4 * R * P) / ρ + 1
  let Ce := Ck * Cq + (Hrow ^ 2 / ρ) * R
  have hCf : 0 ≤ Cf := by dsimp only [Cf]; positivity
  have hCh : 0 ≤ Ch := by dsimp only [Ch]; positivity
  have hCi : 0 ≤ Ci := mul_nonneg (div_nonneg hR hn.le) (add_nonneg hCf hCh)
  have hCq : 0 ≤ Cq := add_nonneg hC₀ hCi
  have hCk : 0 ≤ Ck := by dsimp only [Ck]; positivity
  have hCe : 0 ≤ Ce := by dsimp only [Ce]; positivity
  have hlim : Tendsto (fun V : ℝ => Cq * Real.exp (-η * V)) atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hη))).const_mul Cq
    simpa only [Function.comp_def, id_eq, mul_zero] using hh
  obtain ⟨T₀, hlate⟩ := eventually_atTop.1 (hlim.eventually_lt_const (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)))
  refine ⟨U₀, Cq + Ce, max 0 T₀, hU₀, hU₀r, add_nonneg hCq hCe, le_max_left _ _, ?_⟩
  intro U V hU hV hUR f hf x hx hfn hpoint hUU z hprefloor hprewidth
  dsimp only
  intro hrow hwidth hK hmatch
  let u : Icc 0 U := ⟨U, hU, le_rfl⟩
  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let K := horizonK (x.1 u v 0) (massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v)
    B.charge B.cosmological
  let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
  let Q := ∫ y in (0 : ℝ)..U, intervalExtension hU x.1 y v 0 * (x.2.2 y v 1) ^ 2 /
    (-intervalExtension hU ν y v)
  have he (q : ℝ) (hq : η ≤ q) : Real.exp (-q * V) ≤ Real.exp (-η * V) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hq) hV)
  have hη0 : η ≤ min B.outerRate (2 * c) := min_le_left _ _
  have hη1 : η ≤ 2 * ω * ξ - γ := (min_le_right _ _).trans (min_le_left _ _)
  have hη2 : η ≤ 2 * ω * χ - γ := (min_le_right _ _).trans (min_le_right _ _)
  have hηc : η ≤ 2 * c := hη0.trans (min_le_right _ _)
  obtain ⟨hpre, hprescalar⟩ := hprefix U V hU hV hUR p hp f hf x hx hfn hcb z
    (z.property.2.trans hUU) hprefloor hprewidth
  have hpre' := hpre.trans (mul_le_mul_of_nonneg_left (he _ hη0) hC₀)
  have hinner := hx.early_constraint_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf hc0 hca
    hκ₀ hε hεk hβ hρ hR hn hN hHe hD hApt hpoint z u z.property.2 v
    (fun w _ => hrow w) hwidth hmatch
  have hinner' : (∫ y in (z : ℝ)..U, intervalExtension hU x.1 y v 0 * (x.2.2 y v 1) ^ 2 /
      (-intervalExtension hU ν y v)) ≤ Ci * Real.exp (-η * V) := by
    apply hinner.trans
    have hh := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (he _ hη1) hCf) (mul_le_mul_of_nonneg_left (he _ hη2) hCh)) (div_nonneg hR hn.le)
    simpa only [Ci, Cf, Ch, F, G, ξ, χ, ω, γ, add_mul, mul_assoc] using hh
  have hj := hx.horizon_constraint_join hU hV hUR hc hi hrc hr0 hφ hrd hp hf z u z.property.2 v hpre' hinner'
  have hQ : Q ≤ Cq * Real.exp (-η * V) := by simpa only [Cq, add_mul] using hj.1
  have hκ : Real.exp (-(Cq * Real.exp (-η * V))) ≤ κ := by simpa only [Cq, add_mul] using hj.2.1
  have hκerr : |κ - 1| ≤ Cq * Real.exp (-η * V) := by simpa only [Cq, add_mul] using hj.2.2
  have hscalar (w : Icc 0 U) : |x.2.1 w v 1| ≤ Hrow * Real.exp (-c * V) := by
    by_cases hw : w ≤ z
    · exact (hprescalar w hw).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hHe) (Real.exp_pos _).le)
    · have hym : (w : ℝ) ∈ Ioc (z : ℝ) U := ⟨lt_of_not_ge hw, w.property.2⟩
      obtain ⟨T, _hTb, _hwin, _htrap, _hn, _hD, _hpre, hscalar, _hk, _hK⟩ := hmatch w hym
      have hh := hscalar v le_rfl
      simp only [projIcc_of_mem hU w.property] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hE) (Real.exp_pos _).le)
  have hpotrow (w : Icc 0 U) :
      |1 - B.charge ^ 2 / (x.1 w v 0) ^ 2 - B.cosmological * (x.1 w v 0) ^ 2| ≤ 4 * R * P := by
    have hrw : 0 < x.1 w v 0 := hρ.trans_le (hrow w).1
    have hid : 1 - B.charge ^ 2 / (x.1 w v 0) ^ 2 - B.cosmological * (x.1 w v 0) ^ 2 =
        (-4 * x.1 w v 0) * radialPotential (x.1 w v 0) B.charge B.cosmological := by
      unfold radialPotential
      field_simp [hrw.ne']
      ring
    rw [hid, abs_mul, abs_mul, abs_of_neg (by norm_num : (-4 : ℝ) < 0), neg_neg, abs_of_pos hrw]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hrow w).2 (by norm_num))
      (hpot _ (hrow w)) (abs_nonneg _) (by positivity)
  have hconf := hx.horizon_conformal_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf hρ v
    (fun w => (hrow w).1) hpotrow hscalar u
  have hRH : r V ≤ R := by
    have hh := (hrow ⟨0, le_rfl, hU⟩).2
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v] at hh
    exact hh
  have hrad : r V - x.1 u v 0 ≤ R := by linarith only [hRH, (hrow u).1, hρ]
  have hmain : (2 * |K| + (4 * R * P) / ρ + 1) * Q ≤ Ck * Cq * Real.exp (-η * V) := by
    calc
      _ ≤ (2 * |K| + (4 * R * P) / ρ + 1) * (Cq * Real.exp (-η * V)) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
      _ ≤ Ck * (Cq * Real.exp (-η * V)) :=
        mul_le_mul_of_nonneg_right (by dsimp only [Ck]; linarith only [hK]) (by positivity)
      _ = _ := by ring
  have htail : ((Hrow * Real.exp (-c * V)) ^ 2 / ρ) * (r V - x.1 u v 0) ≤
      (Hrow ^ 2 / ρ) * R * Real.exp (-η * V) := by
    have hid : (Hrow * Real.exp (-c * V)) ^ 2 / ρ = (Hrow ^ 2 / ρ) * Real.exp (-(2 * c) * V) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      rw [show -c * V + -c * V = -(2 * c) * V by ring]
      ring
    calc
      _ ≤ ((Hrow * Real.exp (-c * V)) ^ 2 / ρ) * R := mul_le_mul_of_nonneg_left hrad (by positivity)
      _ = (Hrow ^ 2 / ρ) * R * Real.exp (-(2 * c) * V) := by rw [hid]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (he _ hηc) (by positivity)
  have herr : |x.2.1 u v 2 - 2 * K| ≤ Ce * Real.exp (-η * V) := by
    change |x.2.1 u v 2 - 2 * K| ≤ (2 * |K| + (4 * R * P) / ρ + 1) * Q +
      ((Hrow * Real.exp (-c * V)) ^ 2 / ρ) * (r V - x.1 u v 0) at hconf
    exact (hconf.trans (add_le_add hmain htail)).trans_eq (by dsimp only [Ce]; ring)
  refine ⟨hQ.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCe) (Real.exp_pos _).le),
    (add_le_add hκerr herr).trans_eq (by ring), ?_⟩
  intro hTV
  have hsmall := (hlate V ((le_max_right _ _).trans hTV)).le
  have hh := (Real.exp_le_exp.2 (neg_le_neg hsmall)).trans hκ
  norm_num [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at hh
  exact hh

end CauchyHorizon.Background
