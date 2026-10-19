import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! The spherical double-null metric, inverse and an explicit Lorentz diagonalization. -/

namespace CauchyHorizon

noncomputable def nullMetricMatrix (H R S : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, H * (-1 / 2), 0, 0; H * (-1 / 2), 0, 0, 0;
    0, 0, R, 0; 0, 0, 0, R * S]

noncomputable def nullMetricInverse (H R S : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -2 / H, 0, 0; -2 / H, 0, 0, 0;
    0, 0, R⁻¹, 0; 0, 0, 0, (R * S)⁻¹]

def nullMetricFrame : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 0, 0; 1, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

noncomputable def nullMetricFrameInverse : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, 1 / 2, 0, 0; 1 / 2, -1 / 2, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def HasNullMetricGeometry (H R S : ℝ) : Prop :=
  0 < H ∧ 0 < R ∧ 0 < S ∧
    (nullMetricMatrix H R S).transpose = nullMetricMatrix H R S ∧
    nullMetricMatrix H R S * nullMetricInverse H R S = 1 ∧
    nullMetricInverse H R S * nullMetricMatrix H R S = 1 ∧
    nullMetricFrame.transpose * nullMetricMatrix H R S * nullMetricFrame =
      Matrix.diagonal ![-H, H, R, R * S] ∧
    nullMetricFrameInverse * nullMetricFrame = 1

theorem nullMetric_geometry {H R S : ℝ} (hH : 0 < H) (hR : 0 < R) (hS : 0 < S) :
    HasNullMetricGeometry H R S := by
  refine ⟨hH, hR, hS, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [nullMetricMatrix, nullMetricInverse, nullMetricFrame, nullMetricFrameInverse,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal, Matrix.one_apply, Fin.ext_iff,
      ne_of_gt hH, ne_of_gt hR, ne_of_gt hS] <;>
    first | decide | (intro h; exfalso; revert h; decide) | (field_simp <;> ring)

end CauchyHorizon
