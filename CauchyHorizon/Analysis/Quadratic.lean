import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Quadratic stability in a Banach space, then in L2 -> L1 via Holder.
The bilinear version also applies to C(I)-valued radiation.
-/

open Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem quadratic_difference (B : E →L[ℝ] E →L[ℝ] G) (f g : E) :
    B f f - B g g = B (f - g) f + B g (f - g) := by
  simp only [map_sub, sub_apply]
  abel

theorem norm_quadratic_difference_le (B : E →L[ℝ] E →L[ℝ] G) (f g : E) :
    ‖B f f - B g g‖ ≤ ‖B‖ * ‖f - g‖ * (‖f‖ + ‖g‖) := by
  rw [quadratic_difference]
  calc
    ‖B (f - g) f + B g (f - g)‖ ≤ ‖B (f - g) f‖ + ‖B g (f - g)‖ :=
      norm_add_le _ _
    _ ≤ ‖B‖ * ‖f - g‖ * ‖f‖ + ‖B‖ * ‖g‖ * ‖f - g‖ :=
      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ = _ := by ring

theorem quadratic_difference_tendsto_zero (B : E →L[ℝ] E →L[ℝ] G)
    {f g : ℕ → E} {M : ℝ}
    (hbound : ∀ n, ‖f n‖ + ‖g n‖ ≤ M)
    (hclose : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖B (f n) (f n) - B (g n) (g n)‖) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ‖B‖ * ‖f n - g n‖ * M) atTop (𝓝 0) := by
    simpa using (hclose.const_mul ‖B‖).mul_const M
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro n
  exact (norm_quadratic_difference_le B _ _).trans
    (mul_le_mul_of_nonneg_left (hbound n)
      (mul_nonneg (norm_nonneg B) (norm_nonneg (f n - g n))))

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem l2_quadratic_difference_tendsto_l1 (B : E →L[ℝ] E →L[ℝ] G)
    {f g : ℕ → Lp E 2 μ} {M : ℝ}
    (hbound : ∀ n, ‖f n‖ + ‖g n‖ ≤ M)
    (hclose : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖B.holder 1 (f n) (f n) - B.holder 1 (g n) (g n)‖)
      atTop (𝓝 0) := by
  exact quadratic_difference_tendsto_zero (B.holderL μ 2 2 1) hbound hclose

end CauchyHorizon
