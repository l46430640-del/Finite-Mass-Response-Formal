import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Integrating a one-sided power remainder at a finite endpoint. -/

open Set Filter MeasureTheory Asymptotics
open scoped Topology

namespace CauchyHorizon

theorem integral_isBigO_rpow {f : ℝ → ℝ} {p : ℝ} (hp : -1 < p)
    (hf : f =O[𝓝[>] 0] (fun x => x ^ p)) :
    (fun x => ∫ t in (0 : ℝ)..x, f t) =O[𝓝[>] 0] (fun x => x ^ (p + 1)) := by
  obtain ⟨C, _, hbound⟩ := hf.exists_nonneg
  obtain ⟨δ, hδ, hδbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hbound.bound
  apply IsBigO.of_bound (C / (p + 1))
  filter_upwards [mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨δ, hδ, Subset.rfl⟩] with x hx
  have hxp := Real.rpow_nonneg hx.1.le (p + 1)
  rw [Real.norm_of_nonneg hxp]
  calc
    _ ≤ ∫ t in (0 : ℝ)..x, C * t ^ p := by
      apply intervalIntegral.norm_integral_le_of_norm_le hx.1.le _
        ((intervalIntegral.intervalIntegrable_rpow' hp).const_mul C)
      apply ae_of_all
      intro t ht
      simpa only [Set.mem_ofPred_eq, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le p)] using
        hδbound ⟨ht.1, ht.2.trans hx.2⟩
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hp),
        Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]
      ring

end CauchyHorizon
