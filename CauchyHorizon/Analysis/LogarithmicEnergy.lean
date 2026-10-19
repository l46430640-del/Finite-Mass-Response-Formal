import CauchyHorizon.Analysis.LogarithmicProfile
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-! The normalized logarithmic average contracts the whole-line L2 energy. -/

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace CauchyHorizon

theorem terminalGreen_l2_contraction {b : ℝ} (hb : 0 < b) (B : ℝ →ᵇ ℝ)
    (hB : Integrable (fun t => B t ^ 2)) :
    Integrable (fun t => (b * terminalGreen hb B t) ^ 2) ∧
      (∫ t, (b * terminalGreen hb B t) ^ 2) ≤ ∫ t, B t ^ 2 := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let w := fun z => b * Real.exp (-b * z)
  let H := fun t => b * terminalGreen hb B t
  have hw0 (z : ℝ) : 0 ≤ w z := mul_nonneg hb.le (Real.exp_pos _).le
  have hwi : Integrable w μ := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0).const_mul b
  have hwI : (∫ z, w z ∂μ) = 1 := by
    rw [show (∫ z, w z ∂μ) = b * ∫ z in Ioi (0 : ℝ), Real.exp (-b * z) from integral_const_mul _ _,
      integral_exp_mul_Ioi (neg_neg_of_pos hb), mul_zero, Real.exp_zero]
    field_simp
  have hi (F : ℝ →ᵇ ℝ) : Integrable (fun z => w z * F z) μ := by
    simpa only [w, mul_assoc] using (discounted_integrable hb F 0).const_mul b
  have hmean (t : ℝ) : (∫ z, w z * B (t + z) ∂μ) = H t := by
    simp only [w, μ, mul_assoc, integral_const_mul, H, terminalGreen_eq_shifted_integral]
  have hJensen (t : ℝ) : H t ^ 2 ≤ ∫ z, w z * B (t + z) ^ 2 ∂μ := by
    let T := B.compContinuous ⟨fun z => t + z, by fun_prop⟩
    have hi1 : Integrable (fun z => w z * B (t + z)) μ := hi T
    have hi2 : Integrable (fun z => w z * B (t + z) ^ 2) μ := hi (T ^ 2)
    have hn : 0 ≤ ∫ z, w z * (B (t + z) - H t) ^ 2 ∂μ :=
      integral_nonneg (fun z => mul_nonneg (hw0 z) (sq_nonneg _))
    have he (z : ℝ) : w z * (B (t + z) - H t) ^ 2 =
        w z * B (t + z) ^ 2 - (2 * H t) * (w z * B (t + z)) + H t ^ 2 * w z := by ring
    simp_rw [he] at hn
    have hisub : Integrable (fun z => w z * B (t + z) ^ 2 -
        (2 * H t) * (w z * B (t + z))) μ := hi2.sub (hi1.const_mul (2 * H t))
    rw [integral_add hisub (hwi.const_mul (H t ^ 2)),
      integral_sub hi2 (hi1.const_mul (2 * H t)), integral_const_mul, integral_const_mul,
      hmean t, hwI, mul_one] at hn
    nlinarith only [hn]
  let K := fun p : ℝ × ℝ => w p.1 * B (p.2 + p.1) ^ 2
  have hKc : Continuous K := by fun_prop
  have hKrow (z : ℝ) : (∫ t, K (z, t)) = w z * ∫ t, B t ^ 2 := by
    dsimp only [K]
    rw [integral_const_mul, integral_add_right_eq_self (fun t => B t ^ 2) z]
  have hKnorm (z : ℝ) : (∫ t, ‖K (z, t)‖) = w z * ∫ t, B t ^ 2 := by
    simp only [K, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 z), abs_pow, sq_abs]
    rw [integral_const_mul, integral_add_right_eq_self (fun t => B t ^ 2) z]
  have hKi : Integrable K (μ.prod volume) := by
    apply (integrable_prod_iff hKc.aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall (fun z => (hB.comp_add_right z).const_mul (w z)), ?_⟩
    simpa only [hKnorm] using hwi.mul_const (∫ t, B t ^ 2)
  have hJi := hKi.integral_prod_right
  have hHc : Continuous H := by unfold H; fun_prop
  have hHi : Integrable (fun t => H t ^ 2) := hJi.mono' (hHc.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hJensen t))
  have hJ : (∫ t, ∫ z, K (z, t) ∂μ) = ∫ t, B t ^ 2 := by
    rw [← integral_integral_swap hKi]
    simp_rw [hKrow]
    rw [integral_mul_const, hwI, one_mul]
  refine ⟨hHi, ?_⟩
  have hh := integral_mono hHi hJi hJensen
  rw [hJ] at hh
  exact hh

theorem logarithmicIncoming_outer_energy_bound {U V δ a b k : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b)
    (hcrit : k = a * b) (ℓ : ℝ) (B : ℝ →ᵇ ℝ)
    (hB : Integrable (fun t => B t ^ 2)) :
    (∫ v in (0 : ℝ)..V, (Real.exp (k * v) *
      (∫ u in (0 : ℝ)..min U (δ * Real.exp (-a * v)), |logarithmicIncoming b ℓ B u|)) ^ 2) ≤
      δ ^ (2 * b) / a * ∫ t, B t ^ 2 := by
  have hBa : Integrable (fun t => |B| t ^ 2) := by
    change Integrable (fun t => |B t| ^ 2)
    simpa only [sq_abs] using hB
  obtain ⟨hi, hbnd⟩ := terminalGreen_l2_contraction hb |B| hBa
  have hsq : (∫ t, |B| t ^ 2) = ∫ t, B t ^ 2 := by
    change (∫ t, |B t| ^ 2) = ∫ t, B t ^ 2
    simp only [sq_abs]
  rw [hsq] at hbnd
  have horder : ℓ - Real.log δ ≤ ℓ - Real.log δ + a * V :=
    le_add_of_nonneg_right (mul_nonneg ha.le hV)
  have hseg : (∫ t in (ℓ - Real.log δ)..(ℓ - Real.log δ + a * V),
      (b * terminalGreen hb |B| t) ^ 2) ≤ ∫ t, B t ^ 2 := by
    rw [intervalIntegral.integral_of_le horder]
    exact (setIntegral_le_integral hi (Filter.Eventually.of_forall (fun t => sq_nonneg _))).trans hbnd
  exact (logarithmicIncoming_outer_energy hU hV hδ ha hb hcrit ℓ B).trans
    (mul_le_mul_of_nonneg_left hseg (div_nonneg (Real.rpow_nonneg hδ.le _) ha.le))

theorem weighted_exponential_energy {V k s H : ℝ} {h : ℝ → ℝ}
    (hV : 0 ≤ V) (hks : k < s) (hH : 0 ≤ H) (hc : Continuous h)
    (hb : ∀ t ∈ Ici (0 : ℝ), |h t| ≤ H * Real.exp (-s * t)) :
    (∫ t in (0 : ℝ)..V, (Real.exp (k * t) * |h t|) ^ 2) ≤ H ^ 2 / (2 * (s - k)) := by
  let d := 2 * (s - k)
  have hd : 0 < d := mul_pos (by norm_num) (sub_pos.2 hks)
  have hw (t : ℝ) : (Real.exp (k * t) * (H * Real.exp (-s * t))) ^ 2 =
      H ^ 2 * Real.exp (-d * t) := by
    calc
      _ = H ^ 2 * (Real.exp (k * t) * Real.exp (-s * t)) ^ 2 := by ring
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 2; dsimp only [d]; ring
  have hm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) V) :
      (Real.exp (k * t) * |h t|) ^ 2 ≤ H ^ 2 * Real.exp (-d * t) := by
    rw [← hw]
    exact (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
      (by positivity)).2 (mul_le_mul_of_nonneg_left (hb t ht.1) (Real.exp_pos _).le)
  have hleft : Continuous (fun t => (Real.exp (k * t) * |h t|) ^ 2) := by fun_prop
  have hright : Continuous (fun t => H ^ 2 * Real.exp (-d * t)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hV (hleft.intervalIntegrable _ _)
    (hright.intervalIntegrable _ _) hm
  have htail := setIntegral_mono_set
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hd) 0).const_mul (H ^ 2))
    (Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg H) (Real.exp_pos _).le))
    (Filter.Eventually.of_forall (fun t (ht : t ∈ Ioc (0 : ℝ) V) => ht.1))
  simp only [intervalIntegral.integral_of_le hV] at hi
  have hh := hi.trans htail
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hd), mul_zero,
    Real.exp_zero, neg_div_neg_eq] at hh
  rw [intervalIntegral.integral_of_le hV]
  exact hh.trans_eq (by dsimp only [d]; ring)

end CauchyHorizon
