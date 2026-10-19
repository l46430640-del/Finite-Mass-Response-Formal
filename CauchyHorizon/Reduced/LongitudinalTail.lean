import CauchyHorizon.Reduced.IntegralRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Uniform tails of actual fields from exponentially decaying longitudinal derivatives. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem IsWaveIntegral.longitudinal_tail_bound {U V e Λ C η : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V} {zIn : C(Icc 0 U, WaveVector)}
    {vOut : C(Icc 0 V, WaveVector)} {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))}
    {x : WaveState U V} (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (u : Icc 0 U) (i : Fin 3) (a b : Icc 0 V) (hab : a ≤ b) (hC : 0 ≤ C) (hη : 0 < η)
    (hdec : ∀ t ∈ Icc a b, |x.2.1 u t i| ≤ C * Real.exp (-η * t)) :
    |x.1 u b i - x.1 u a i| ≤ C / η * Real.exp (-η * a) := by
  let F := fun t => intervalExtension hV (x.1 u) t i
  let W := fun t => intervalExtension hV (x.2.1 u) t i
  have hFc : Continuous F := by fun_prop
  have hWc : Continuous W := by fun_prop
  have hd (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) : HasDerivAt F (W t) t := by
    have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.le.trans b.property.2⟩
    have hh := (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      t (hx.longitudinal_derivative u htV)
    change HasDerivWithinAt F (x.2.1 u ⟨t, htV⟩ i) (Icc 0 V) t at hh
    have hh' : HasDerivWithinAt F (W t) (Icc 0 V) t := by
      simpa only [W, intervalExtension_apply, projIcc_of_mem hV htV] using hh
    exact hh'.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (a : ℝ) ≤ b from hab)
    hFc.continuousOn hd (hWc.intervalIntegrable _ _)
  have hec : Continuous (fun t : ℝ => C * Real.exp (-η * t)) := by fun_prop
  have hI := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (show (a : ℝ) ≤ b from hab) (f := W) (g := fun t => C * Real.exp (-η * t))
    (Filter.Eventually.of_forall (by
      intro t ht
      have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.trans b.property.2⟩
      simpa only [W, Real.norm_eq_abs, intervalExtension_apply, projIcc_of_mem hV htV] using
        hdec ⟨t, htV⟩ ⟨ht.1.le, ht.2⟩)) (hec.intervalIntegrable _ _)
  rw [hFTC, Real.norm_eq_abs] at hI
  simp only [F, intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property] at hI
  apply hI.trans
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.2 hη.ne'), integral_exp, smul_eq_mul]
  have hh := mul_nonneg (div_nonneg hC hη.le) (Real.exp_pos (-η * (b : ℝ))).le
  simp only [inv_neg, div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

end CauchyHorizon
