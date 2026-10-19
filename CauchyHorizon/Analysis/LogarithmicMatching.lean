import CauchyHorizon.Analysis.LogarithmicEnergy
import CauchyHorizon.Analysis.ArrivalEnergy

/-! The signed outer moment and the exact derivative remainder of its exponential average. -/

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace CauchyHorizon

theorem logarithmicIncoming_scaled_trace {a b k δ : ℝ} (hδ : 0 < δ)
    (hcrit : k = a * b) (ℓ : ℝ) (P : ℝ → ℝ) (v : ℝ) :
    (δ * Real.exp (-a * v)) * Real.exp (k * v) *
        logarithmicIncoming b ℓ P (δ * Real.exp (-a * v)) =
      b * δ ^ b * P (ℓ - Real.log δ + a * v) := by
  have hu : 0 < δ * Real.exp (-a * v) := mul_pos hδ (Real.exp_pos _)
  have hp : (δ * Real.exp (-a * v)) * (δ * Real.exp (-a * v)) ^ (b - 1) =
      (δ * Real.exp (-a * v)) ^ b := by
    rw [Real.rpow_sub hu, Real.rpow_one]
    field_simp
  have he : Real.exp (-a * v * b) * Real.exp (k * v) = 1 := by
    rw [← Real.exp_add, hcrit, show -a * v * b + a * b * v = 0 by ring, Real.exp_zero]
  dsimp only [logarithmicIncoming]
  rw [Real.log_mul hδ.ne' (Real.exp_ne_zero _), Real.log_exp,
    show ℓ - (Real.log δ + -a * v) = ℓ - Real.log δ + a * v by ring]
  calc
    _ = b * ((δ * Real.exp (-a * v)) * (δ * Real.exp (-a * v)) ^ (b - 1)) *
        Real.exp (k * v) * P (ℓ - Real.log δ + a * v) := by ring
    _ = _ := by
      rw [hp, Real.mul_rpow hδ.le (Real.exp_pos _).le, ← Real.exp_mul]
      calc
        _ = (b * δ ^ b * P (ℓ - Real.log δ + a * v)) *
            (Real.exp (-a * v * b) * Real.exp (k * v)) := by ring
        _ = _ := by rw [he, mul_one]

theorem logarithmicIncoming_radius_error_energy {a b δ l S : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hl : 0 ≤ l) (hlS : l ≤ S) (ℓ : ℝ) (P : ℝ →ᵇ ℝ) (hP : Integrable (fun t => P t ^ 2)) :
    let R := fun t => b * (δ * Real.exp (-a * t)) * δ ^ b * P (ℓ - Real.log δ + a * t)
    IntegrableOn (fun t => R t ^ 2) (Icc l S) ∧
      (∫ t in l..S, R t ^ 2) ≤ (b * δ ^ (b + 1)) ^ 2 / a * ∫ t, P t ^ 2 := by
  intro R
  have hRc : Continuous R := by dsimp only [R]; fun_prop
  have hPc : Continuous (fun t => P (ℓ - Real.log δ + a * t)) := by fun_prop
  have htime := timeChange_l2_bound hlS ha (by fun_prop)
    (fun t _ => (((hasDerivAt_id t).const_mul a).const_add (ℓ - Real.log δ)))
    (fun _ _ => by simp) P.continuous hP
  have hpow : δ * δ ^ b = δ ^ (b + 1) := by rw [Real.rpow_add hδ, Real.rpow_one]; ring
  have hh := intervalIntegral.integral_mono_on (μ := volume) hlS ((hRc.pow 2).intervalIntegrable _ _)
    (((hPc.pow 2).const_mul ((b * δ ^ (b + 1)) ^ 2)).intervalIntegrable _ _) (fun t ht => by
      have hg0 : 0 ≤ δ * Real.exp (-a * t) := mul_nonneg hδ.le (Real.exp_pos _).le
      have hgδ : δ * Real.exp (-a * t) ≤ δ := mul_le_of_le_one_right hδ.le
        (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ha.le) (hl.trans ht.1)))
      have hsq := (sq_le_sq₀ hg0 hδ.le).2 hgδ
      have hbnd := mul_le_mul_of_nonneg_right hsq ((sq_nonneg (b * δ ^ b * P (ℓ - Real.log δ + a * t))))
      calc
        R t ^ 2 = (δ * Real.exp (-a * t)) ^ 2 * (b * δ ^ b * P (ℓ - Real.log δ + a * t)) ^ 2 := by
          dsimp only [R]; ring
        _ ≤ δ ^ 2 * (b * δ ^ b * P (ℓ - Real.log δ + a * t)) ^ 2 := hbnd
        _ = (b * δ ^ (b + 1)) ^ 2 * P (ℓ - Real.log δ + a * t) ^ 2 := by rw [← hpow]; ring)
  rw [intervalIntegral.integral_const_mul] at hh
  exact ⟨(hRc.pow 2).continuousOn.integrableOn_Icc,
    (hh.trans (mul_le_mul_of_nonneg_left htime (sq_nonneg _))).trans_eq (by ring)⟩

theorem logarithmicIncoming_first_moment {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u)
    (ℓ : ℝ) (B : ℝ →ᵇ ℝ) :
    IntervalIntegrable (fun x => x * logarithmicIncoming b ℓ B x) volume 0 u ∧
      (∫ x in (0 : ℝ)..u, x * logarithmicIncoming b ℓ B x) =
        b * u ^ (b + 1) * terminalGreen (by linarith : 0 < b + 1) B (ℓ - Real.log u) := by
  have hc : 0 < b + 1 := by linarith
  have he : (fun x => x * logarithmicIncoming b ℓ B x) =ᵐ[volume.restrict (Ioc 0 u)]
      fun x => (b / (b + 1)) * logarithmicIncoming (b + 1) ℓ B x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hp : x * x ^ (b - 1) = x ^ b := by
      calc
        _ = x ^ (1 : ℝ) * x ^ (b - 1) := by rw [Real.rpow_one]
        _ = x ^ (1 + (b - 1)) := (Real.rpow_add hx.1 _ _).symm
        _ = _ := by congr 1; ring
    dsimp only [logarithmicIncoming]
    rw [show b + 1 - 1 = b by ring]
    calc
      _ = b * (x * x ^ (b - 1)) * B (ℓ - Real.log x) := by ring
      _ = _ := by rw [hp]; field_simp
  have hm := logarithmicIncoming_primitive hc hu ℓ B
  have hi : IntervalIntegrable (fun x => x * logarithmicIncoming b ℓ B x) volume 0 u := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).2
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hu).1
      (hm.1.const_mul (b / (b + 1)))).congr he.symm
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ x in (0 : ℝ)..u, (b / (b + 1)) * logarithmicIncoming (b + 1) ℓ B x := by
      simp only [intervalIntegral.integral_of_le hu]
      exact integral_congr_ae he
    _ = _ := by rw [intervalIntegral.integral_const_mul, hm.2]; field_simp

theorem logarithmicIncoming_scaled_first_moment {a b k δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (hcrit : k = a * b) (ℓ : ℝ) (B : ℝ →ᵇ ℝ) (v : ℝ) :
    Real.exp ((a + k) * v) *
        (∫ x in (0 : ℝ)..(δ * Real.exp (-a * v)), x * logarithmicIncoming b ℓ B x) =
      b * δ ^ (b + 1) * terminalGreen (by linarith : 0 < b + 1) B (ℓ - Real.log δ + a * v) := by
  rw [(logarithmicIncoming_first_moment hb (mul_pos hδ (Real.exp_pos _)).le ℓ B).2,
    Real.log_mul hδ.ne' (Real.exp_ne_zero _), Real.log_exp,
    show ℓ - (Real.log δ + -a * v) = ℓ - Real.log δ + a * v by ring,
    Real.mul_rpow hδ.le (Real.exp_pos _).le, ← Real.exp_mul]
  have he : Real.exp ((a + k) * v) * Real.exp (-a * v * (b + 1)) = 1 := by
    rw [← Real.exp_add, hcrit]
    convert Real.exp_zero using 1
    congr 1
    ring
  calc
    _ = (b * δ ^ (b + 1) * terminalGreen (by linarith : 0 < b + 1) B
      (ℓ - Real.log δ + a * v)) * (Real.exp ((a + k) * v) * Real.exp (-a * v * (b + 1))) := by ring
    _ = _ := by rw [he, mul_one]

theorem terminalGreen_derivative_remainder {c : ℝ} (hc : 0 < c) (B D : ℝ →ᵇ ℝ)
    (hd : ∀ t, HasDerivAt B (D t) t) (t : ℝ) :
    c * terminalGreen hc B t - B t = terminalGreen hc D t := by
  let F := fun s => Real.exp (-c * s) * B s
  let G := fun s => Real.exp (-c * s) * D s - c * (Real.exp (-c * s) * B s)
  have hder (s : ℝ) : HasDerivAt F (G s) s := by
    have hh := (((hasDerivAt_id s).const_mul (-c)).exp).mul (hd s)
    exact hh.congr_deriv (by dsimp only [G, id_eq]; ring)
  have hi : IntegrableOn G (Ioi t) :=
    (discounted_integrable hc D t).sub ((discounted_integrable hc B t).const_mul c)
  have he : Tendsto (fun s : ℝ => Real.exp (-c * s)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hlim : Tendsto F atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun s => ?_) (by simpa using he.mul_const ‖B‖)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simpa only [Real.norm_eq_abs, neg_mul] using
      mul_le_mul_of_nonneg_left (B.norm_coe_le_norm s) (Real.exp_pos (-c * s)).le
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' (fun s (_hs : s ∈ Ici t) => hder s) hi hlim
  dsimp only [G, F] at hI
  rw [integral_sub (discounted_integrable hc D t) ((discounted_integrable hc B t).const_mul c),
    integral_const_mul, zero_sub] at hI
  have hh := congrArg (fun z => Real.exp (c * t) * z) hI
  have hcancel : Real.exp (c * t) * Real.exp (-c * t) = 1 := by
    rw [← Real.exp_add, show c * t + -c * t = 0 by ring, Real.exp_zero]
  change c * (Real.exp (c * t) * ∫ s in Ioi t, Real.exp (-c * s) * B s) - B t =
    Real.exp (c * t) * ∫ s in Ioi t, Real.exp (-c * s) * D s
  nlinarith only [hh, congrArg (fun z => z * B t) hcancel]

theorem terminalGreen_approximation_energy {c : ℝ} (hc : 0 < c) (B D : ℝ →ᵇ ℝ)
    (hd : ∀ t, HasDerivAt B (D t) t) (hD : Integrable (fun t => D t ^ 2)) :
    Integrable (fun t => (c * terminalGreen hc B t - B t) ^ 2) ∧
      (∫ t, (c * terminalGreen hc B t - B t) ^ 2) ≤ (1 / c) ^ 2 * ∫ t, D t ^ 2 := by
  obtain ⟨hi, hE⟩ := terminalGreen_l2_contraction hc D hD
  have he (t : ℝ) : (c * terminalGreen hc B t - B t) ^ 2 =
      (1 / c) ^ 2 * (c * terminalGreen hc D t) ^ 2 := by
    rw [terminalGreen_derivative_remainder hc B D hd t]
    field_simp
  simp_rw [he]
  exact ⟨hi.const_mul _, by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hE (sq_nonneg _)⟩

theorem logarithmicIncoming_first_moment_energy {a b k δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 < δ) (hcrit : k = a * b) (ℓ : ℝ) (B D : ℝ →ᵇ ℝ)
    (hd : ∀ t, HasDerivAt B (D t) t) (hD : Integrable (fun t => D t ^ 2)) :
    let E := fun v => Real.exp ((a + k) * v) *
      (∫ x in (0 : ℝ)..(δ * Real.exp (-a * v)), x * logarithmicIncoming b ℓ B x) -
      (b * δ ^ (b + 1) / (b + 1)) * B (ℓ - Real.log δ + a * v)
    Integrable (fun v => E v ^ 2) ∧
      (∫ v, E v ^ 2) ≤ (b * δ ^ (b + 1) / (b + 1) ^ 2) ^ 2 / a * ∫ t, D t ^ 2 := by
  intro E
  have hc : 0 < b + 1 := by linarith
  let Q := fun t => (b + 1) * terminalGreen hc B t - B t
  let C := b * δ ^ (b + 1) / (b + 1)
  let s := ℓ - Real.log δ
  have he (v : ℝ) : E v ^ 2 = C ^ 2 * Q (s + a * v) ^ 2 := by
    dsimp only [E]
    rw [logarithmicIncoming_scaled_first_moment hb hδ hcrit ℓ B v]
    dsimp only [C, Q, s]
    field_simp
  obtain ⟨hQi, hQE⟩ := terminalGreen_approximation_energy hc B D hd hD
  have htime : Integrable (fun v => Q (s + a * v) ^ 2) :=
    (hQi.comp_add_left s).comp_mul_left' ha.ne'
  have hchange : (∫ v, Q (s + a * v) ^ 2) = (1 / a) * ∫ t, Q t ^ 2 := by
    rw [Measure.integral_comp_mul_left (fun t => Q (s + t) ^ 2) a,
      integral_add_left_eq_self (fun t => Q t ^ 2) s]
    simp only [abs_of_pos (inv_pos.2 ha), smul_eq_mul, one_div]
  simp_rw [he]
  refine ⟨htime.const_mul _, ?_⟩
  rw [integral_const_mul, hchange]
  have hh := mul_le_mul_of_nonneg_left hQE (mul_nonneg (sq_nonneg C) (one_div_nonneg.2 ha.le))
  calc
    _ ≤ (C ^ 2 * (1 / a)) * ((1 / (b + 1)) ^ 2 * ∫ t, D t ^ 2) := by
      simpa only [mul_assoc] using hh
    _ = _ := by dsimp only [C]; field_simp

end CauchyHorizon
