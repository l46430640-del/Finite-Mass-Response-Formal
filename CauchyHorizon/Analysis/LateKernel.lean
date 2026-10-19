import CauchyHorizon.Analysis.EarlyKernel

/-! The late double kernel retains its decaying time weight. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem late_double_kernel_bound {k χ l v : ℝ} (hgap : 0 < 2 * k - χ) (hlv : l ≤ v)
    {M : ℝ → ℝ} (hc : Continuous M) (hM : ∀ t ∈ Icc l v, 0 ≤ M t) :
    Real.exp (-k * v) * (∫ t in l..v, Real.exp ((2 * k - χ) * t) *
      ∫ w in t..v, Real.exp (-k * w) * M w) ≤
        (1 / (2 * k - χ)) * ∫ t in l..v,
          Real.exp (-k * (v - t)) * Real.exp (-χ * t) * M t := by
  let m := fun t => Real.exp (-χ * t) * M t
  have hmc : Continuous m := by fun_prop
  have hsum : k + (k - χ) = 2 * k - χ := by ring
  have hK := (exponential_double_kernel_bound (k := k) (q := k - χ)
    (by rw [hsum]; exact hgap) hlv hmc
    (fun t ht => mul_nonneg (Real.exp_pos _).le (hM t ht))).2.2
  have he (t : ℝ) : Real.exp (-k * v) * (Real.exp ((2 * k - χ) * t) *
      ∫ w in t..v, Real.exp (-k * w) * M w) =
      Real.exp (-k * (v - t)) *
        ∫ w in t..v, Real.exp (-(k - χ) * (w - t)) * m w := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro w _
    dsimp only [m]
    have hex : Real.exp (-k * v) * Real.exp ((2 * k - χ) * t) * Real.exp (-k * w) =
        Real.exp (-k * (v - t)) * Real.exp (-(k - χ) * (w - t)) * Real.exp (-χ * w) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    simpa only [mul_assoc] using congrArg (fun a => a * M w) hex
  rw [← intervalIntegral.integral_const_mul]
  have hleft := intervalIntegral.integral_congr (a := l) (b := v) (μ := volume) (fun t _ => he t)
  rw [hleft]
  simpa only [hsum, m, mul_assoc] using hK

end CauchyHorizon
