import CauchyHorizon.Analysis.Quadratic
import CauchyHorizon.Analysis.Cumulative

/-! Squared radiation and its cumulative integrals in a normed algebra.
Taking A = C(I, R) retains uniformity in the transverse coordinate.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace CauchyHorizon

variable {α A : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedRing A] [NormedAlgebra ℝ A]

noncomputable def l2Square (f : Lp A 2 μ) : Lp A 1 μ :=
  (ContinuousLinearMap.mul ℝ A).holder 1 f f

theorem l2Square_coe (f : Lp A 2 μ) :
    (fun x => l2Square f x) =ᵐ[μ] fun x => f x ^ 2 := by
  simpa [l2Square, pow_two] using (ContinuousLinearMap.mul ℝ A).coeFn_holder (r := 1) f f

theorem l2Square_close {f g : ℕ → Lp A 2 μ} {M : ℝ}
    (hbound : ∀ n, ‖f n‖ + ‖g n‖ ≤ M)
    (hclose : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖l2Square (f n) - l2Square (g n)‖) atTop (𝓝 0) :=
  l2_quadratic_difference_tendsto_l1 (ContinuousLinearMap.mul ℝ A) hbound hclose

theorem l2_square_error_integral_tendsto {f g : ℕ → Lp A 2 μ} {M : ℝ}
    (hbound : ∀ n, ‖f n‖ + ‖g n‖ ≤ M)
    (hclose : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖f n x ^ 2 - g n x ^ 2‖ ∂μ) atTop (𝓝 0) := by
  apply (l2Square_close hbound hclose).congr
  intro n
  rw [← dist_eq_norm, L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [l2Square_coe (f n), l2Square_coe (g n)] with x hf hg
  rw [hf, hg, dist_eq_norm]

theorem square_cumulative_convergence_uniform {f g : ℕ → Lp A 2 μ} {M : ℝ}
    (hbound : ∀ n, ‖f n‖ + ‖g n‖ ≤ M)
    (hclose : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ s : Set α,
      ‖(∫ x in s, f n x ^ 2 ∂μ) - ∫ x in s, g n x ^ 2 ∂μ‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := cumulative_convergence_uniform (l2Square_close hbound hclose) ε hε
  refine ⟨N, fun n hn s => ?_⟩
  have hf := integral_congr_ae (ae_mono (Measure.restrict_le_self (s := s))
    (l2Square_coe (f n)))
  have hg := integral_congr_ae (ae_mono (Measure.restrict_le_self (s := s))
    (l2Square_coe (g n)))
  simpa only [hf, hg] using hN n hn s

end CauchyHorizon
