import CauchyHorizon.Geometry.NullMetric
import Mathlib.Tactic.Linarith

/-! A constant first null coordinate has a nonzero null normal and a one-dimensional radical. -/

namespace CauchyHorizon

theorem nullMetric_tangent {H R S : ℝ} (hH : 0 < H) (hR : 0 < R) (hS : 0 < S)
    (a : Fin 4 → ℝ) (ha : a 0 = 0) :
    nullMetricInverse H R S 0 0 = 0 ∧ nullMetricInverse H R S 1 0 ≠ 0 ∧
      (∑ i, ∑ j, nullMetricMatrix H R S i j * (Pi.single 1 1 : Fin 4 → ℝ) i * a j) = 0 ∧
      0 ≤ (∑ i, ∑ j, nullMetricMatrix H R S i j * a i * a j) ∧
      ((∑ i, ∑ j, nullMetricMatrix H R S i j * a i * a j) = 0 ↔ a 2 = 0 ∧ a 3 = 0) := by
  have he : (∑ i, ∑ j, nullMetricMatrix H R S i j * a i * a j) =
      R * (a 2 ^ 2 + S * a 3 ^ 2) := by
    norm_num [nullMetricMatrix, Fin.sum_univ_four, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, ha]
    ring
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · change -2 / H ≠ 0
    exact div_ne_zero (by norm_num) hH.ne'
  · norm_num [nullMetricMatrix, Fin.sum_univ_succ, Pi.single_apply, ha]
  · rw [he]
    exact mul_nonneg hR.le (add_nonneg (sq_nonneg _) (mul_nonneg hS.le (sq_nonneg _)))
  · rw [he]
    constructor
    · intro h
      have hz := (mul_eq_zero.1 h).resolve_left hR.ne'
      have h₂ : a 2 ^ 2 = 0 := le_antisymm
        (by nlinarith [mul_nonneg hS.le (sq_nonneg (a 3))]) (sq_nonneg _)
      have h₃ : a 3 ^ 2 = 0 := (mul_eq_zero.1 (by nlinarith [h₂] : S * a 3 ^ 2 = 0)).resolve_left hS.ne'
      exact ⟨sq_eq_zero_iff.1 h₂, sq_eq_zero_iff.1 h₃⟩
    · rintro ⟨h₂, h₃⟩
      simp [h₂, h₃]

end CauchyHorizon
