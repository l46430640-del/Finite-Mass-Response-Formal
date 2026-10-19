import CauchyHorizon.Analysis.IntegratingFactor

/-! An integral inequality for a continuous norm is controlled through its C1 primitive. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem continuous_volterra_bound {g : ℝ → ℝ} {D K U : ℝ} (hg : Continuous g)
    (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Icc 0 U, g t ≤ D + K * ∫ s in 0..t, g s)
    {u : ℝ} (hu : u ∈ Icc 0 U) : g u ≤ D * Real.exp (K * U) := by
  let F : ℝ → ℝ := fun t => D + K * ∫ s in 0..t, g s
  have hd (t : ℝ) : HasDerivAt F (K * g t) t :=
    ((intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_mul K).const_add D
  have hc : Continuous F := continuous_iff_continuousAt.2 (fun t => (hd t).continuousAt)
  have hh := integrable_coefficient_gronwall (f := F) (f' := fun t => K * g t)
    (g := fun _ => K) hu.1 intervalIntegrable_const continuousOn_const hc.continuousOn
    (fun t _ => hd t) (fun t ht => mul_le_mul_of_nonneg_left
      (hb t ⟨ht.1.le, ht.2.le.trans hu.2⟩) hK)
  simp only [F, intervalIntegral.integral_same, mul_zero, add_zero,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hh
  rw [mul_comm u K] at hh
  exact (hb u hu).trans (hh.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hu.2 hK)) hD))

end CauchyHorizon
