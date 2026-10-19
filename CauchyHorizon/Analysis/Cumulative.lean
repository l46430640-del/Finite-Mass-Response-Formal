import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! An L1 error controls all cumulative integrals, including the terminal integral. -/

open Filter MeasureTheory Set
open scoped Topology

namespace CauchyHorizon

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_setIntegral_le_l1 (f : Lp E 1 μ) (s : Set α) :
    ‖∫ x in s, f x ∂μ‖ ≤ ‖f‖ := by
  have hf : Integrable (fun x => f x) μ := memLp_one_iff_integrable.1 (Lp.memLp f)
  calc
    ‖∫ x in s, f x ∂μ‖ ≤ ∫ x in s, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ ∂μ := integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (fun _ => norm_nonneg _)) hf.norm
    _ = ‖f‖ := (L1.norm_eq_integral_norm f).symm

theorem norm_setIntegral_sub_le_l1 (f g : Lp E 1 μ) (s : Set α) :
    ‖(∫ x in s, f x ∂μ) - ∫ x in s, g x ∂μ‖ ≤ ‖f - g‖ := by
  have hf : Integrable (fun x => f x) μ := memLp_one_iff_integrable.1 (Lp.memLp f)
  have hg : Integrable (fun x => g x) μ := memLp_one_iff_integrable.1 (Lp.memLp g)
  rw [← integral_sub hf.integrableOn hg.integrableOn]
  have heq : (∫ x in s, f x - g x ∂μ) = ∫ x in s, (f - g) x ∂μ :=
    integral_congr_ae (ae_mono Measure.restrict_le_self (Lp.coeFn_sub f g).symm)
  rw [heq]
  exact norm_setIntegral_le_l1 _ _

theorem cumulative_convergence_uniform {f g : ℕ → Lp E 1 μ}
    (hclose : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ s : Set α,
      ‖(∫ x in s, f n x ∂μ) - ∫ x in s, g n x ∂μ‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hclose.eventually (Iio_mem_nhds hε))
  exact ⟨N, fun n hn s => (norm_setIntegral_sub_le_l1 _ _ s).trans_lt (hN n hn)⟩

end CauchyHorizon
