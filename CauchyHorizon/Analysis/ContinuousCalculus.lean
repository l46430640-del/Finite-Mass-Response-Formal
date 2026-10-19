import CauchyHorizon.Analysis.IntervalOperators
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.ContinuousMap.Units

/-! Pointwise formulas for calculus in the Banach algebra of continuous functions. -/

open Set

namespace CauchyHorizon

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem continuousMap_exp_apply (f : C(X, ℝ)) (x : X) :
    NormedSpace.exp f x = Real.exp (f x) := by
  simpa only [ContinuousMap.evalAlgHom_apply, Real.exp_eq_exp_ℝ] using
    NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ x)
      (ContinuousMap.evalCLM ℝ x).continuous f

omit [CompactSpace X] in
theorem continuousMap_inverse_apply (f : C(X, ℝ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    Ring.inverse f x = (f x)⁻¹ := by
  have h := congrArg (fun g : C(X, ℝ) => g x)
    (Ring.mul_inverse_cancel f ((f.isUnit_iff_forall_ne_zero).2 hf))
  change f x * Ring.inverse f x = 1 at h
  rw [← one_div]
  apply (eq_div_iff (hf x)).2
  simpa only [one_div, mul_comm] using h

theorem continuousMap_inverse_hasDerivWithinAt {f : ℝ → C(X, ℝ)}
    {f' : C(X, ℝ)} {s : Set ℝ} {t : ℝ} (hf : HasDerivWithinAt f f' s t)
    (hn : ∀ x, f t x ≠ 0) :
    HasDerivWithinAt (fun u => Ring.inverse (f u))
      (-(Ring.inverse (f t) * f' * Ring.inverse (f t))) s t := by
  have hu := ((f t).isUnit_iff_forall_ne_zero).2 hn
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [hu.unit_spec] at hi
  have hd := hi.comp_hasDerivWithinAt t hf
  simpa only [hu.unit_spec, ← Ring.inverse_unit, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, Function.comp_def] using! hd

end CauchyHorizon
