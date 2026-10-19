import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exponential decay over a fixed fraction of the arrival time gives an incoming power. -/

namespace CauchyHorizon

theorem arrival_exp_power {a u T j q : ℝ}
    (ha : 0 < a) (hu : 0 < u) (hj : 0 < j) (hq : 0 ≤ q)
    (hlo : j ≤ u * Real.exp (a * T)) :
    Real.exp (-q * T) ≤ j ^ (-(q / a)) * u ^ (q / a) := by
  have hneg : Real.exp (-a * T) ≤ u / j := by
    apply (le_div_iff₀ hj).2
    have hh := mul_le_mul_of_nonneg_right hlo (Real.exp_pos (-a * T)).le
    rw [mul_assoc, ← Real.exp_add, show a * T + -a * T = 0 by ring,
      Real.exp_zero, mul_one] at hh
    simpa only [mul_comm] using hh
  have hh := Real.rpow_le_rpow (Real.exp_pos (-a * T)).le hneg (div_nonneg hq ha.le)
  rw [← Real.exp_mul, Real.div_rpow hu.le hj.le] at hh
  have he : -a * T * (q / a) = -q * T := by field_simp
  rw [he] at hh
  simpa only [Real.rpow_neg hj.le, div_eq_mul_inv, mul_comm] using hh

theorem arrival_scalar_power {a u T j c cL α dν dL C K f : ℝ}
    (ha : 0 < a) (hu : 0 < u) (hu1 : u ≤ 1) (hj : 0 < j)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hcL : 0 ≤ cL) (hα : 0 ≤ α)
    (hd : dL ≤ dν) (hgap : dL + cL * α / a ≤ c / a)
    (hlo : j ≤ u * Real.exp (a * T)) :
    2 * C * |f| + 2 * C * u ^ (-1 + c / a) +
        K * u ^ (-1 + dν) * Real.exp (-cL * (α * T)) ≤
      2 * C * |f| + (2 * C + K * j ^ (-(cL * α / a))) *
        u ^ (-1 + dL + cL * α / a) := by
  have he : Real.exp (-cL * (α * T)) ≤ j ^ (-(cL * α / a)) * u ^ (cL * α / a) := by
    simpa only [neg_mul, mul_assoc] using arrival_exp_power ha hu hj (mul_nonneg hcL hα) hlo
  have hp := Real.rpow_le_rpow_of_exponent_ge hu hu1 (show -1 + dL ≤ -1 + dν by linarith)
  have hpre := Real.rpow_le_rpow_of_exponent_ge hu hu1
    (show -1 + dL + cL * α / a ≤ -1 + c / a by linarith only [hgap])
  calc
    _ ≤ 2 * C * |f| + 2 * C * u ^ (-1 + dL + cL * α / a) +
        (K * u ^ (-1 + dL)) * (j ^ (-(cL * α / a)) * u ^ (cL * α / a)) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpre (show 0 ≤ 2 * C by positivity)))
        (mul_le_mul (mul_le_mul_of_nonneg_left hp hK) he (Real.exp_pos _).le (by positivity))
    _ = _ := by rw [Real.rpow_add hu]; ring

theorem arrival_decay_power {a u T j D N q β : ℝ}
    (ha : 0 < a) (hu : 0 < u) (hj : 0 < j) (hD : 0 ≤ D) (hN : 0 ≤ N)
    (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hlo : j ≤ u * Real.exp (a * T)) (hhi : u * Real.exp (a * T) ≤ D) :
    N * Real.exp (a * T) * Real.exp (-q * (β * T)) ≤
      (N * D * j ^ (-(q / a * β))) * u ^ (-1 + q / a * β) := by
  let δ := q / a * β
  have hdecay : Real.exp (-q * (β * T)) ≤ u ^ δ / j ^ δ := by
    have hh := arrival_exp_power ha hu hj (mul_nonneg hq hβ) hlo
    rw [show q * β / a = δ by dsimp only [δ]; ring, Real.rpow_neg hj.le,
      show -(q * β) * T = -q * (β * T) by ring] at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hplus : N * Real.exp (a * T) ≤ N * D / u := by
    have hh := (le_div_iff₀ hu).2 (by simpa only [mul_comm] using hhi)
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hh hN
  calc
    _ ≤ (N * D / u) * (u ^ δ / j ^ δ) :=
      mul_le_mul hplus hdecay (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [Real.rpow_add hu, Real.rpow_neg_one, Real.rpow_neg hj.le]
      dsimp only [δ]
      ring

theorem arrival_damping_kernel {a α q z u Tz Tu j D : ℝ}
    (ha : 0 < a) (hα : 0 ≤ α) (hq : 0 ≤ q) (hz : 0 < z) (hu : 0 < u) (hj : 0 < j)
    (hlo : j ≤ z * Real.exp (a * Tz)) (hhi : u * Real.exp (a * Tu) ≤ D) :
    Real.exp (-q * (α * Tz - α * Tu)) ≤
      (D / j) ^ (q * α / a) * (z ^ (q * α / a) * u ^ (-(q * α / a))) := by
  let σ := q * α / a
  have hσ : 0 ≤ σ := div_nonneg (mul_nonneg hq hα) ha.le
  have hD : 0 < D := (mul_pos hu (Real.exp_pos _)).trans_le hhi
  have hneg := arrival_exp_power ha hz hj (mul_nonneg hq hα) hlo
  have hplus : Real.exp ((q * α) * Tu) ≤ D ^ σ * u ^ (-σ) := by
    have hh : Real.exp (a * Tu) ≤ D / u :=
      (le_div_iff₀ hu).2 (by simpa only [mul_comm] using hhi)
    have hp := Real.rpow_le_rpow (Real.exp_pos _).le hh hσ
    rw [← Real.exp_mul, Real.div_rpow hD.le hu.le] at hp
    have he : a * Tu * σ = (q * α) * Tu := by dsimp only [σ]; field_simp
    rw [he] at hp
    simpa only [Real.rpow_neg hu.le, div_eq_mul_inv] using hp
  calc
    _ = Real.exp (-(q * α) * Tz) * Real.exp ((q * α) * Tu) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ (j ^ (-σ) * z ^ σ) * (D ^ σ * u ^ (-σ)) :=
      mul_le_mul hneg hplus (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [Real.div_rpow hD.le hj.le, Real.rpow_neg hj.le]; dsimp only [σ]; ring

theorem arrival_power_upper {z U T a D s b : ℝ}
    (hz : 0 < z) (hzU : z ≤ U) (hs : 0 ≤ s) (hsb : s ≤ b)
    (hscale : z * Real.exp (a * T) ≤ D) :
    z ^ b ≤ D ^ s * U ^ (b - s) * Real.exp (-(a * s) * T) := by
  have hh := Real.rpow_le_rpow (mul_pos hz (Real.exp_pos _)).le hscale hs
  rw [Real.mul_rpow hz.le (Real.exp_pos _).le, ← Real.exp_mul] at hh
  have hzs : z ^ s ≤ D ^ s * Real.exp (-(a * s) * T) := by
    have hb := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(a * s) * T)).le
    rw [mul_assoc, ← Real.exp_add, show a * T * s + -(a * s) * T = 0 by ring,
      Real.exp_zero, mul_one] at hb
    exact hb
  calc
    _ = z ^ (b - s) * z ^ s := by rw [← Real.rpow_add hz, sub_add_cancel]
    _ ≤ U ^ (b - s) * (D ^ s * Real.exp (-(a * s) * T)) :=
      mul_le_mul (Real.rpow_le_rpow hz.le hzU (sub_nonneg.2 hsb)) hzs
        (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg (hz.le.trans hzU) _)
    _ = _ := by ring

theorem arrival_jacobian_power_bound {u j a T q α C J : ℝ}
    (hu : 0 < u) (hj : 0 < j) (hq : 0 ≤ q) (hα : 0 < α) (hC : 0 < C)
    (hscale : j ≤ u * Real.exp (a * T)) (hJac : α / (C * u) ≤ J) :
    u ^ (-1 - q) ≤ (C / α) * J * j ^ (-q) * Real.exp (a * q * T) := by
  have hpow := Real.rpow_le_rpow_of_nonpos hj hscale (neg_nonpos.2 hq)
  rw [Real.mul_rpow hu.le (Real.exp_pos _).le, ← Real.exp_mul] at hpow
  have hp : u ^ (-q) ≤ j ^ (-q) * Real.exp (a * q * T) := by
    have hh := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (a * q * T)).le
    rw [mul_assoc, ← Real.exp_add, show a * T * -q + a * q * T = 0 by ring,
      Real.exp_zero, mul_one] at hh
    exact hh
  have hJ : u⁻¹ ≤ (C / α) * J := by
    have hh := mul_le_mul_of_nonneg_left hJac (div_pos hC hα).le
    have he : (C / α) * (α / (C * u)) = u⁻¹ := by
      field_simp
    rwa [he] at hh
  calc
    _ = u⁻¹ * u ^ (-q) := by
      rw [sub_eq_add_neg, Real.rpow_add hu, Real.rpow_neg_one]
    _ ≤ ((C / α) * J) * (j ^ (-q) * Real.exp (a * q * T)) :=
      mul_le_mul hJ hp (Real.rpow_nonneg hu.le _) ((inv_pos.2 hu).le.trans hJ)
    _ = _ := by ring

end CauchyHorizon
