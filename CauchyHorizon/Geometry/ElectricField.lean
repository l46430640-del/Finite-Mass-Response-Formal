import CauchyHorizon.Geometry.NullMetric
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Electric two-forms in the coordinate order (V,u,theta,phi). -/

namespace CauchyHorizon

def electricTwoForm {R : Type*} [Zero R] [Neg R] (a : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, -a, 0, 0; a, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

noncomputable def raiseTwoForm (gInv F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  gInv * F * gInv.transpose

noncomputable def maxwellStress (g gInv F : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (∑ k, ∑ l, F i k * gInv k l * F j l) -
    (1 / 4 : ℝ) * g i j * (∑ k, ∑ l, F k l * raiseTwoForm gInv F k l)

theorem null_metric_volume {H r s : ℝ} (hH : 0 < H) (hr : r ≠ 0) (hs : 0 < s) :
    0 < H * r ^ 2 * s / 2 ∧
      Real.sqrt |(nullMetricMatrix H (r ^ 2) (s ^ 2)).det| = H * r ^ 2 * s / 2 := by
  have hp : 0 < H * r ^ 2 * s / 2 := by positivity
  have hd : (nullMetricMatrix H (r ^ 2) (s ^ 2)).det = -(H * r ^ 2 * s / 2) ^ 2 := by
    rw [Matrix.det_succ_row_zero]
    norm_num [Fin.sum_univ_succ, nullMetricMatrix, Matrix.det_fin_three,
      Matrix.submatrix_apply, Fin.succAbove, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail]
    simp only [Fin.ext_iff]
    norm_num [Fin.val_ofNat, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
    ring
  refine ⟨hp, ?_⟩
  rw [hd, abs_neg, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq hp.le]

theorem electric_raised {H r s e : ℝ} (hH : H ≠ 0) (hr : r ≠ 0) :
    raiseTwoForm (nullMetricInverse H (r ^ 2) (s ^ 2)) (electricTwoForm (e * H / (2 * r ^ 2))) =
      electricTwoForm (-2 * e / (H * r ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raiseTwoForm, electricTwoForm, nullMetricInverse, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.transpose_apply, hH, hr] <;> field_simp

theorem electric_density {H r s e : ℝ} (hH : H ≠ 0) (hr : r ≠ 0) :
    (H * r ^ 2 * s / 2) •
      raiseTwoForm (nullMetricInverse H (r ^ 2) (s ^ 2)) (electricTwoForm (e * H / (2 * r ^ 2))) =
        electricTwoForm (-e * s) := by
  rw [electric_raised hH hr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [electricTwoForm, Matrix.smul_apply, smul_eq_mul, hH, hr] <;> field_simp

set_option maxHeartbeats 1500000 in
theorem electric_stress {H r s e : ℝ} (hH : H ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    let g := nullMetricMatrix H (r ^ 2) (s ^ 2)
    let gInv := nullMetricInverse H (r ^ 2) (s ^ 2)
    let F := electricTwoForm (e * H / (2 * r ^ 2))
    (∀ i j, 2 * maxwellStress g gInv F i j =
      !![0, H * e ^ 2 / (2 * r ^ 4), 0, 0; H * e ^ 2 / (2 * r ^ 4), 0, 0, 0;
        0, 0, e ^ 2 / r ^ 2, 0; 0, 0, 0, e ^ 2 * s ^ 2 / r ^ 2] i j) ∧
      (∑ i, ∑ j, gInv i j * maxwellStress g gInv F i j) = 0 := by
  dsimp only
  have he := electric_raised (s := s) (e := e) hH hr
  simp only [maxwellStress, he]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [electricTwoForm, nullMetricMatrix, nullMetricInverse,
        Fin.sum_univ_succ, hH, hr] <;> field_simp <;> ring
  · norm_num [electricTwoForm, nullMetricMatrix, nullMetricInverse,
      Fin.sum_univ_succ, hH, hr, hs]
    field_simp
    ring

end CauchyHorizon
