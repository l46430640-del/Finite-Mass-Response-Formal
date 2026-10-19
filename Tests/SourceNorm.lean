import CauchyHorizon.Analysis.SourceNorm

open Set MeasureTheory

namespace CauchyHorizon.Tests

-- The weight normalization also handles a point interval and identically zero forcing.
example {a M N : ℝ} (hM : 0 ≤ M) (hNM : N ≤ M) :
    Real.sqrt N ≤ Real.sqrt M * Real.exp ((1 : ℝ) / 2) := by
  have hh := source_norm_bound_of_young (a := a) (b := a) le_rfl hM
    (F := fun _ => 0) (J := fun _ => 0) (G := fun _ => 0)
    continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ _ => by simpa using hNM)
  simpa using hh

-- Constant forcing scales with its spatial L1 norm, without a time-window factor.
example {a b M N K : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hbound : ∀ η : ℝ → ℝ, ContinuousOn η (Icc a b) → (∀ x ∈ Icc a b, 0 < η x) →
      N ≤ (M + ∫ x in a..b, K ^ 2 / η x) * Real.exp (∫ x in a..b, η x)) :
    Real.sqrt N ≤ (Real.sqrt M + (b - a) * |K|) * Real.exp ((1 : ℝ) / 2) := by
  have hh := source_norm_bound_of_young hab hM
    (F := fun _ => K ^ 2) (J := fun _ => 0) (G := fun _ => 0)
    continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ => sq_nonneg K) (fun _ _ => le_rfl) (fun η hη hη0 => by simpa using hbound η hη hη0)
  simpa only [intervalIntegral.integral_zero, Real.sqrt_zero, add_zero, zero_add,
    Real.sqrt_sq_eq_abs, intervalIntegral.integral_const, smul_eq_mul] using hh

end CauchyHorizon.Tests
