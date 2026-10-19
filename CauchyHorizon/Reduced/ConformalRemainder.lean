import CauchyHorizon.Reduced.IntegralRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Integrate the partial conformal error without changing its background exponent. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem IsWaveIntegral.conformal_remainder_bound {U V e Λ C η k J : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V} {zIn : C(Icc 0 U, WaveVector)}
    {vOut : C(Icc 0 V, WaveVector)} {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))}
    {x : WaveState U V} (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (hC : 0 ≤ C) (hη : 0 < η)
    {K : ℝ → ℝ} (hK : Continuous K)
    (herr : ∀ t ∈ Icc a b, |x.2.1 u t 2 - 2 * K t| ≤ C * Real.exp (-η * t))
    (hKI : (∫ t in (a : ℝ)..b, |K t + k|) ≤ J) :
    let R := x.1 u b 2 - x.1 u a 2 + 2 * k * ((b : ℝ) - a)
    |R| ≤ C / η * Real.exp (-η * a) + 2 * J ∧
      Real.exp (x.1 u b 2) = Real.exp (x.1 u a 2) * Real.exp (-2 * k * ((b : ℝ) - a) + R) := by
  let E := fun t => intervalExtension hV (x.1 u) t 2
  let W := fun t => intervalExtension hV (x.2.1 u) t 2
  have hEc : Continuous E := by fun_prop
  have hWc : Continuous W := by fun_prop
  have hd (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) : HasDerivAt E (W t) t := by
    have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.le.trans b.property.2⟩
    have hh := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      t (hx.longitudinal_derivative u htV)
    change HasDerivWithinAt E (x.2.1 u ⟨t, htV⟩ 2) (Icc 0 V) t at hh
    have hh' : HasDerivWithinAt E (W t) (Icc 0 V) t := by
      simpa only [E, W, intervalExtension_apply, projIcc_of_mem hV htV] using hh
    exact hh'.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (a : ℝ) ≤ b from hab)
    hEc.continuousOn hd (hWc.intervalIntegrable _ _)
  have hR : (∫ t in (a : ℝ)..b, W t + 2 * k) =
      x.1 u b 2 - x.1 u a 2 + 2 * k * ((b : ℝ) - a) := by
    rw [intervalIntegral.integral_add (hWc.intervalIntegrable _ _) intervalIntegrable_const,
      hFTC, intervalIntegral.integral_const, smul_eq_mul]
    simp only [E, intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property]
    ring
  have hExp : (∫ t in (a : ℝ)..b, C * Real.exp (-η * t)) ≤ C / η * Real.exp (-η * a) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.2 hη.ne'), integral_exp, smul_eq_mul]
    have hh := mul_nonneg (div_nonneg hC hη.le) (Real.exp_pos (-η * (b : ℝ))).le
    simp only [inv_neg, div_eq_mul_inv] at hh ⊢
    nlinarith only [hh]
  have hec : Continuous (fun t : ℝ => C * Real.exp (-η * t)) := by fun_prop
  have hkc : Continuous (fun t => 2 * |K t + k|) := by fun_prop
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (show (a : ℝ) ≤ b from hab) (f := fun t => W t + 2 * k)
    (g := fun t => C * Real.exp (-η * t) + 2 * |K t + k|)
    (Filter.Eventually.of_forall (by
      intro t ht
      have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.trans b.property.2⟩
      have hh := herr ⟨t, htV⟩ ⟨ht.1.le, ht.2⟩
      simp only [Real.norm_eq_abs, W, intervalExtension_apply, projIcc_of_mem hV htV]
      calc
        _ = |(x.2.1 u ⟨t, htV⟩ 2 - 2 * K t) + 2 * (K t + k)| := by congr 1; ring
        _ ≤ |x.2.1 u ⟨t, htV⟩ 2 - 2 * K t| + |2 * (K t + k)| := abs_add_le _ _
        _ ≤ _ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; exact add_le_add hh le_rfl))
    ((hec.add hkc).intervalIntegrable _ _)
  rw [Real.norm_eq_abs, hR,
    intervalIntegral.integral_add (hec.intervalIntegrable _ _) (hkc.intervalIntegrable _ _)] at hbound
  simp only [intervalIntegral.integral_const_mul] at hbound hExp
  refine ⟨hbound.trans (add_le_add hExp
    (mul_le_mul_of_nonneg_left hKI (by norm_num : (0 : ℝ) ≤ 2))), ?_⟩
  rw [← Real.exp_add]
  congr 1
  ring

end CauchyHorizon
