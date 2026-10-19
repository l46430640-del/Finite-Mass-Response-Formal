import CauchyHorizon.Analysis.IntegratingFactor

/-! Signed damping with a nonnegative forcing envelope. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem damped_scalar_bound {y c f F : ℝ → ℝ} {a b q : ℝ}
    (hab : a ≤ b) (hq : 0 < q) (hy : ContinuousOn y (Icc a b))
    (hc : ContinuousOn c (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt y (-c t * y t + f t) t)
    (hcoef : ∀ t ∈ Icc a b, q ≤ c t) (hforce : ∀ t ∈ Icc a b, |f t| ≤ F t) :
    (∀ t ∈ Icc a b, |y t| ≤ Real.exp (-q * (t - a)) *
      (|y a| + ∫ s in a..t, Real.exp (q * (s - a)) * F s)) ∧
    (∫ t in a..b, |y t|) ≤ (|y a| + ∫ t in a..b, F t) / q := by
  let g := fun t => Real.exp (q * (t - a)) * F t
  let Z := fun t => Real.exp (-q * (t - a)) * (|y a| + ∫ s in a..t, g s)
  have hgc : ContinuousOn g (Icc a b) := by unfold g; fun_prop
  have hgi : IntervalIntegrable g volume a b := hgc.intervalIntegrable_of_Icc hab
  have hpc : ContinuousOn (fun t => ∫ s in a..t, g s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hgi left_mem_uIcc
  have hZc : ContinuousOn Z (Icc a b) := by unfold Z; fun_prop
  have hZa : Z a = |y a| := by simp [Z]
  have hZ0 (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ Z t := by
    apply mul_nonneg (Real.exp_pos _).le
    apply add_nonneg (abs_nonneg _)
    apply intervalIntegral.integral_nonneg ht.1
    intro s hs
    exact mul_nonneg (Real.exp_pos _).le
      ((abs_nonneg _).trans (hforce s ⟨hs.1, hs.2.trans ht.2⟩))
  have hZd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt Z (-q * Z t + F t) t := by
    have he := (((hasDerivAt_id t).sub_const a).const_mul (-q)).exp
    have hp := (primitive_hasDerivAt_interior hgi (hgc.mono Ioo_subset_Icc_self) ht).const_add |y a|
    have heq : Real.exp (-q * (t - a)) * Real.exp (q * (t - a)) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      congr 1
      ring
    apply (he.mul hp).congr_deriv
    dsimp only [Z, g, id_eq]
    nlinarith only [congrArg (fun z => z * F t) heq]
  have hsign (σ : ℝ) (hσ : |σ| = 1) (t : ℝ) (ht : t ∈ Icc a b) : σ * y t ≤ Z t := by
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hsi (v : ℝ) : σ * y v ≤ |y v| := by
      calc
        _ ≤ |σ * y v| := le_abs_self _
        _ = _ := by rw [abs_mul, hσ, one_mul]
    have hh := integrable_coefficient_gronwall (f := fun v => σ * y v - Z v)
      (f' := fun v => σ * (-c v * y v + f v) - (-q * Z v + F v))
      (g := fun v => -c v) ht.1
      ((hc.mono hsub).neg.intervalIntegrable_of_Icc ht.1)
      (hc.neg.mono (Ioo_subset_Icc_self.trans hsub))
      (((hy.mono hsub).const_mul σ).sub (hZc.mono hsub))
      (fun v hv => ((hd v ⟨hv.1, hv.2.trans_le ht.2⟩).const_mul σ).sub
        (hZd v ⟨hv.1, hv.2.trans_le ht.2⟩)) (by
          intro v hv
          have hvb : v ∈ Icc a b := ⟨hv.1.le, hv.2.le.trans ht.2⟩
          have hsf : σ * f v ≤ F v := by
            calc
              _ ≤ |σ * f v| := le_abs_self _
              _ = |f v| := by rw [abs_mul, hσ, one_mul]
              _ ≤ _ := hforce v hvb
          nlinarith only [mul_nonneg (sub_nonneg.2 (hcoef v hvb)) (hZ0 v hvb), hsf])
    have hstart : σ * y a - Z a ≤ 0 := by rw [hZa]; exact sub_nonpos.2 (hsi a)
    have hend := hh.trans (mul_nonpos_of_nonpos_of_nonneg hstart (Real.exp_pos _).le)
    exact sub_nonpos.1 hend
  have hbound (t : ℝ) (ht : t ∈ Icc a b) : |y t| ≤ Z t := by
    apply abs_le.2
    have hminus := hsign (-1) (by norm_num) t ht
    have hplus := hsign 1 (by norm_num) t ht
    constructor <;> linarith only [hminus, hplus]
  refine ⟨hbound, ?_⟩
  have hZi : IntervalIntegrable Z volume a b := hZc.intervalIntegrable_of_Icc hab
  have hFi : IntervalIntegrable F volume a b := hF.intervalIntegrable_of_Icc hab
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hZc hZd
    ((hZi.const_mul (-q)).add hFi)
  rw [intervalIntegral.integral_add (hZi.const_mul (-q)) hFi,
    intervalIntegral.integral_const_mul, hZa] at hI
  apply (le_div_iff₀ hq).2
  have hmono := intervalIntegral.integral_mono_on hab
    (hy.abs.intervalIntegrable_of_Icc hab) hZi hbound
  have hz := hZ0 b (right_mem_Icc.2 hab)
  nlinarith only [mul_le_mul_of_nonneg_left hmono hq.le, hI, hz]

end CauchyHorizon
