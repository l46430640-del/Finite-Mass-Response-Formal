import CauchyHorizon.Analysis.TransportEnergyBound
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Normalize the free Young weight to recover a source-norm energy bound. -/

open Set MeasureTheory Filter
open scoped Topology

namespace CauchyHorizon

theorem source_norm_bound_of_young {a b M N : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    {F J G : ℝ → ℝ} (hF : ContinuousOn F (Icc a b)) (hJ : ContinuousOn J (Icc a b))
    (hG : ContinuousOn G (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x)
    (hJ0 : ∀ x ∈ Icc a b, 0 ≤ J x)
    (hbound : ∀ η : ℝ → ℝ, ContinuousOn η (Icc a b) → (∀ x ∈ Icc a b, 0 < η x) →
      N ≤ (M + ∫ x in a..b, J x + F x / η x) * Real.exp (∫ x in a..b, G x + η x)) :
    Real.sqrt N ≤ (Real.sqrt M + Real.sqrt (∫ x in a..b, J x) +
      ∫ x in a..b, Real.sqrt (F x)) * Real.exp (((∫ x in a..b, G x) + 1) / 2) := by
  let A := ∫ x in a..b, Real.sqrt (F x)
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg_of_forall hab (fun _ => Real.sqrt_nonneg _)
  have hB : 0 ≤ ∫ x in a..b, J x := intervalIntegral.integral_nonneg hab hJ0
  have hFi : IntervalIntegrable (fun x => Real.sqrt (F x)) volume a b := hF.sqrt.intervalIntegrable_of_Icc hab
  have hJi : IntervalIntegrable J volume a b := hJ.intervalIntegrable_of_Icc hab
  have hGi : IntervalIntegrable G volume a b := hG.intervalIntegrable_of_Icc hab
  -- The extra h in the denominator also covers zero-length intervals and zero sources.
  have hreg (h : ℝ) (hh : 0 < h) :
      N ≤ (M + (∫ x in a..b, J x) + (A + (b - a) * h + h) * A) *
        Real.exp ((∫ x in a..b, G x) + 1) := by
    let D := A + (b - a) * h + h
    have hD : 0 < D := add_pos_of_nonneg_of_pos
      (add_nonneg hA (mul_nonneg (sub_nonneg.2 hab) hh.le)) hh
    let η := fun x => (Real.sqrt (F x) + h) / D
    have hη : ContinuousOn η (Icc a b) := (hF.sqrt.add continuousOn_const).div_const D
    have hη0 (x : ℝ) (_hx : x ∈ Icc a b) : 0 < η x :=
      div_pos (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hh) hD
    have hηi : IntervalIntegrable η volume a b := hη.intervalIntegrable_of_Icc hab
    have hηint : (∫ x in a..b, η x) ≤ 1 := by
      dsimp only [η]
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add hFi intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      exact (div_le_one hD).2 (le_add_of_nonneg_right hh.le)
    have hquot : ContinuousOn (fun x => F x / η x) (Icc a b) :=
      hF.div hη (fun x hx => (hη0 x hx).ne')
    have hpoint (x : ℝ) (hx : x ∈ Icc a b) : F x / η x ≤ D * Real.sqrt (F x) := by
      have hs : F x / (Real.sqrt (F x) + h) ≤ Real.sqrt (F x) := by
        apply (div_le_iff₀ (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hh)).2
        nlinarith only [Real.sq_sqrt (hF0 x hx), mul_nonneg (Real.sqrt_nonneg (F x)) hh.le]
      calc
        _ = D * (F x / (Real.sqrt (F x) + h)) := by dsimp only [η]; simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hs hD.le
    have hsource := intervalIntegral.integral_mono_on hab (hquot.intervalIntegrable_of_Icc hab)
      (hFi.const_mul D) hpoint
    rw [intervalIntegral.integral_const_mul] at hsource
    have hh' := hbound η hη hη0
    rw [intervalIntegral.integral_add hJi (hquot.intervalIntegrable_of_Icc hab),
      intervalIntegral.integral_add hGi hηi] at hh'
    apply hh'.trans
    apply mul_le_mul
    · linarith only [hsource]
    · exact Real.exp_le_exp.2 (by linarith only [hηint])
    · exact (Real.exp_pos _).le
    · exact add_nonneg (add_nonneg hM hB) (mul_nonneg hD.le hA)
  have hc : Continuous (fun h : ℝ =>
      (M + (∫ x in a..b, J x) + (A + (b - a) * h + h) * A) *
        Real.exp ((∫ x in a..b, G x) + 1)) := by fun_prop
  have hN : N ≤ (M + (∫ x in a..b, J x) + A ^ 2) * Real.exp ((∫ x in a..b, G x) + 1) := by
    have ht := hc.continuousAt (x := (0 : ℝ)) |>.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have hh := ge_of_tendsto ht (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact hreg h hh)
    simpa only [mul_zero, add_zero, pow_two] using hh
  have hsum : M + (∫ x in a..b, J x) + A ^ 2 ≤
      (Real.sqrt M + Real.sqrt (∫ x in a..b, J x) + A) ^ 2 := by
    nlinarith only [Real.sq_sqrt hM, Real.sq_sqrt hB,
      mul_nonneg (Real.sqrt_nonneg M) (Real.sqrt_nonneg (∫ x in a..b, J x)),
      mul_nonneg (Real.sqrt_nonneg M) hA,
      mul_nonneg (Real.sqrt_nonneg (∫ x in a..b, J x)) hA]
  have he : Real.exp (((∫ x in a..b, G x) + 1) / 2) ^ 2 = Real.exp ((∫ x in a..b, G x) + 1) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply Real.sqrt_le_iff.2
  refine ⟨mul_nonneg (add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA)
    (Real.exp_pos _).le, ?_⟩
  rw [mul_pow, he]
  exact hN.trans (mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le)

end CauchyHorizon
