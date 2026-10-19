import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Matching normalization and the exact logarithmic remainder give the corner weight. -/

namespace CauchyHorizon

theorem corner_lapse_bounds {u a k s v ellY ellV R j D Olo Ohi : ℝ}
    (hu : 0 < u) (ha : 0 < a) (hk : 0 ≤ k) (hj : 0 < j)
    (hOhi : 0 ≤ Ohi)
    (hscale : j ≤ u * Real.exp (a * s) ∧ u * Real.exp (a * s) ≤ D)
    (hmatch : Olo ≤ u * Real.exp ellY ∧ u * Real.exp ellY ≤ Ohi)
    (hrem : |ellV - ellY + 2 * k * (v - s)| ≤ R) :
    (Real.exp (-R) * Olo * j ^ (2 * k / a)) *
        (u ^ (-1 - 2 * k / a) * Real.exp (-2 * k * v)) ≤ Real.exp ellV ∧
      Real.exp ellV ≤ (Real.exp R * Ohi * D ^ (2 * k / a)) *
        (u ^ (-1 - 2 * k / a) * Real.exp (-2 * k * v)) := by
  let ρ := 2 * k / a
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  have hcancel : u * u ^ ρ * u ^ (-1 - ρ) = 1 := by
    calc
      _ = u ^ ((1 + ρ) + (-1 - ρ)) := by rw [Real.rpow_add hu, Real.rpow_add hu, Real.rpow_one]
      _ = 1 := by ring_nf; exact Real.rpow_zero u
  have hid : Real.exp ellY * Real.exp (-2 * k * (v - s)) =
      ((u * Real.exp ellY) * (u * Real.exp (a * s)) ^ ρ) *
        (u ^ (-1 - ρ) * Real.exp (-2 * k * v)) := by
    rw [Real.mul_rpow hu.le (Real.exp_pos _).le, ← Real.exp_mul]
    rw [show a * s * ρ = 2 * k * s by dsimp only [ρ]; field_simp]
    symm
    calc
      _ = (u * u ^ ρ * u ^ (-1 - ρ)) *
          (Real.exp ellY * (Real.exp (2 * k * s) * Real.exp (-2 * k * v))) := by ring
      _ = _ := by rw [hcancel, one_mul, ← Real.exp_add]; congr 2; ring
  have hlo := mul_le_mul hmatch.1 (Real.rpow_le_rpow hj.le hscale.1 hρ)
    (Real.rpow_nonneg hj.le ρ) (mul_pos hu (Real.exp_pos _)).le
  have hhi := mul_le_mul hmatch.2
    (Real.rpow_le_rpow (mul_pos hu (Real.exp_pos _)).le hscale.2 hρ)
    (Real.rpow_nonneg (mul_pos hu (Real.exp_pos _)).le ρ) hOhi
  have hweight : 0 ≤ u ^ (-1 - ρ) * Real.exp (-2 * k * v) := by positivity
  have hbaseLo := mul_le_mul_of_nonneg_right hlo hweight
  have hbaseHi := mul_le_mul_of_nonneg_right hhi hweight
  rw [← hid] at hbaseLo hbaseHi
  constructor
  · calc
      _ = Real.exp (-R) * ((Olo * j ^ ρ) * (u ^ (-1 - ρ) * Real.exp (-2 * k * v))) := by ring
      _ ≤ Real.exp (-R) * (Real.exp ellY * Real.exp (-2 * k * (v - s))) :=
        mul_le_mul_of_nonneg_left hbaseLo (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2; linarith only [(abs_le.1 hrem).1]
  · calc
      _ ≤ Real.exp R * (Real.exp ellY * Real.exp (-2 * k * (v - s))) := by
        rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2; linarith only [(abs_le.1 hrem).2]
      _ ≤ Real.exp R * ((Ohi * D ^ ρ) * (u ^ (-1 - ρ) * Real.exp (-2 * k * v))) :=
        mul_le_mul_of_nonneg_left hbaseHi (Real.exp_pos _).le
      _ = _ := by ring

end CauchyHorizon
