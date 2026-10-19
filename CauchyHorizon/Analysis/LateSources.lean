import CauchyHorizon.Analysis.ArrivalPower

/-! The corner power and the actual inverse Jacobian give both late source weights. -/

namespace CauchyHorizon

theorem late_weighted_sources {u j a k t v β C J L N lam ζ A : ℝ}
    (hu : 0 < u) (hj : 0 < j) (ha : 0 < a) (hk : 0 ≤ k)
    (hβ : 0 ≤ β) (hβ2 : β ≤ 2) (hC : 0 < C) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (hscale : j ≤ u * Real.exp (a * t)) (hJac : (1 + β) / (C * u) ≤ J)
    (hlam : |lam| ≤ L * u ^ (-(2 * k / a)) * Real.exp (-(2 * k) * v))
    (hA : A = u * Real.exp (k * t) * |ζ|) :
    |lam| * (N * u ^ (k / a * β - 1)) ≤
      (L * N * C / (1 + β) * j ^ (-(2 * k / a - k / a * β))) * J *
        Real.exp (-(2 * k) * v +
          (2 * k - 3 * (k * β / (1 + β))) * ((1 + β) * t)) ∧
    |lam| * |ζ| ≤ (L * C / (1 + β) * j ^ (-(2 * k / a))) * J *
      Real.exp (-(2 * k) * v + (k - k * β / (1 + β)) * ((1 + β) * t)) * A := by
  have hα : 0 < 1 + β := by linarith only [hβ]
  have hq : 0 ≤ 2 * k / a - k / a * β := by
    rw [show 2 * k / a - k / a * β = k / a * (2 - β) by ring]
    exact mul_nonneg (div_nonneg hk ha.le) (sub_nonneg.2 hβ2)
  have hpow := arrival_jacobian_power_bound hu hj hq hα hC hscale hJac
  have hpow' := arrival_jacobian_power_bound (q := 2 * k / a) hu hj
    (div_nonneg (mul_nonneg (by norm_num) hk) ha.le) hα hC hscale hJac
  have he : a * (2 * k / a - k / a * β) * t =
      (2 * k - 3 * (k * β / (1 + β))) * ((1 + β) * t) := by
    field_simp
    ring
  have he' : a * (2 * k / a) * t - k * t =
      (k - k * β / (1 + β)) * ((1 + β) * t) := by
    field_simp
    ring
  have hζ : |ζ| = u⁻¹ * Real.exp (-k * t) * A := by
    rw [hA]
    calc
      _ = (u⁻¹ * u) * (Real.exp (-k * t) * Real.exp (k * t)) * |ζ| := by
        rw [inv_mul_cancel₀ hu.ne', ← Real.exp_add,
          show -k * t + k * t = 0 by ring, Real.exp_zero]
        ring
      _ = _ := by ring
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  constructor
  · calc
      _ ≤ (L * u ^ (-(2 * k / a)) * Real.exp (-(2 * k) * v)) *
          (N * u ^ (k / a * β - 1)) :=
        mul_le_mul_of_nonneg_right hlam (by positivity)
      _ = (L * N) * u ^ (-1 - (2 * k / a - k / a * β)) *
          Real.exp (-(2 * k) * v) := by
        rw [show -1 - (2 * k / a - k / a * β) = -(2 * k / a) + (k / a * β - 1) by ring,
          Real.rpow_add hu]
        ring
      _ ≤ (L * N) * ((C / (1 + β)) * J * j ^ (-(2 * k / a - k / a * β)) *
          Real.exp (a * (2 * k / a - k / a * β) * t)) * Real.exp (-(2 * k) * v) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (mul_nonneg hL hN))
          (Real.exp_pos _).le
      _ = _ := by rw [Real.exp_add, he]; ring
  · calc
      _ ≤ (L * u ^ (-(2 * k / a)) * Real.exp (-(2 * k) * v)) * |ζ| :=
        mul_le_mul_of_nonneg_right hlam (abs_nonneg _)
      _ = L * u ^ (-1 - 2 * k / a) *
          (Real.exp (-(2 * k) * v) * Real.exp (-k * t) * A) := by
        rw [hζ, sub_eq_add_neg, Real.rpow_add hu, Real.rpow_neg_one]
        ring
      _ ≤ L * ((C / (1 + β)) * J * j ^ (-(2 * k / a)) * Real.exp (a * (2 * k / a) * t)) *
          (Real.exp (-(2 * k) * v) * Real.exp (-k * t) * A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow' hL) (by positivity)
      _ = _ := by
        have hexp : Real.exp (a * (2 * k / a) * t) * Real.exp (-k * t) =
            Real.exp ((k - k * β / (1 + β)) * ((1 + β) * t)) := by
          rw [← Real.exp_add, ← he']
          congr 1
          ring
        rw [Real.exp_add]
        calc
          _ = (L * C / (1 + β) * j ^ (-(2 * k / a))) * J *
              Real.exp (-(2 * k) * v) *
              (Real.exp (a * (2 * k / a) * t) * Real.exp (-k * t)) * A := by ring
          _ = _ := by rw [hexp]; ring

end CauchyHorizon
