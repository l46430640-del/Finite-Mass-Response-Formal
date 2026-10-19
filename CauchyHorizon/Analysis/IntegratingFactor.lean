import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Integrating factors with coefficients that may be singular at both endpoints. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem primitive_hasDerivAt_interior {g : ℝ → ℝ} {a b x : ℝ}
    (hg : IntervalIntegrable g volume a b) (hc : ContinuousOn g (Ioo a b))
    (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t => ∫ s in a..t, g s) (g x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · apply hg.mono_set
    rw [uIcc_of_le hx.1.le, uIcc_of_le (hx.1.le.trans hx.2.le)]
    exact Icc_subset_Icc le_rfl hx.2.le
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hc x hx
  · exact hc.continuousAt (isOpen_Ioo.mem_nhds hx)

theorem integral_mul_exp_primitive {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hc : ContinuousOn g (Ioo a b)) :
    (∫ t in a..b, g t * Real.exp (∫ s in a..t, g s)) =
      Real.exp (∫ t in a..b, g t) - 1 := by
  have hprimitive := intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  have hexp := Real.continuous_exp.comp_continuousOn hprimitive
  have hint := hg.continuousOn_mul hexp
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (by simpa only [uIcc_of_le hab, Function.comp_def] using hexp)
    (fun x hx => (primitive_hasDerivAt_interior hg hc hx).exp) hint
  simpa [mul_comm] using hftc

theorem integrable_coefficient_gronwall {f f' g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hgc : ContinuousOn g (Ioo a b)) (hfc : ContinuousOn f (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Ioo a b, f' x ≤ g x * f x) :
    f b ≤ f a * Real.exp (∫ x in a..b, g x) := by
  let H := fun t => Real.exp (-(∫ s in a..t, g s)) * f t
  have hp : ContinuousOn (fun t => ∫ s in a..t, g s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  have hHc : ContinuousOn H (Icc a b) := by
    exact (Real.continuous_exp.comp_continuousOn hp.neg).mul hfc
  have hHd (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt H (Real.exp (-(∫ s in a..x, g s)) * (f' x - g x * f x)) x := by
    have he : HasDerivAt (fun t => Real.exp (-(∫ s in a..t, g s)))
        (Real.exp (-(∫ s in a..x, g s)) * (-g x)) x :=
      (Real.hasDerivAt_exp _).comp x (primitive_hasDerivAt_interior hg hgc hx).neg
    exact (he.mul (hfd x hx)).congr_deriv (by ring)
  have hm : AntitoneOn H (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hHc
    · intro x hx
      rw [interior_Icc] at hx
      exact (hHd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hHd x hx).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.2 (hbound x hx))
  have hend := hm (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  simp only [H, intervalIntegral.integral_same, neg_zero, Real.exp_zero, one_mul] at hend
  have he := mul_le_mul_of_nonneg_left hend (Real.exp_pos (∫ x in a..b, g x)).le
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at he
  simpa only [mul_comm] using he

noncomputable def volterraWeight (a : ℝ) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ s in a..t, 2 * m s)

theorem volterraWeight_pos (a : ℝ) (m : ℝ → ℝ) (t : ℝ) :
    0 < volterraWeight a m t := Real.exp_pos _

theorem volterraWeight_continuous {a b : ℝ} {m : ℝ → ℝ}
    (hm : IntervalIntegrable m volume a b) :
    ContinuousOn (volterraWeight a m) (uIcc a b) := by
  exact Real.continuous_exp.comp_continuousOn
    (intervalIntegral.continuousOn_primitive_interval' (hm.const_mul 2) left_mem_uIcc)

theorem volterraWeight_kernel_bound {a b : ℝ} {c m : ℝ → ℝ} (hab : a ≤ b)
    (hc : IntervalIntegrable c volume a b) (hm : IntervalIntegrable m volume a b)
    (hmc : ContinuousOn m (Ioo a b))
    (hdom : ∀ t ∈ uIcc a b, |c t| ≤ m t) (x : ℝ) (hx : x ∈ Icc a b) :
    (∫ t in a..x, |c t| * volterraWeight a m t) ≤ (1 / 2 : ℝ) * volterraWeight a m x := by
  have hsub : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hx.2
  have hmi := hm.mono_set hsub
  have hci := hc.mono_set hsub
  have hwc := (volterraWeight_continuous hm).mono hsub
  have hmc' : ContinuousOn (fun t => 2 * m t) (Ioo a x) :=
    continuousOn_const.mul (hmc.mono (Ioo_subset_Ioo le_rfl hx.2))
  have hid := integral_mul_exp_primitive hx.1 (hmi.const_mul 2) hmc'
  change (∫ t in a..x, (2 * m t) * volterraWeight a m t) =
    volterraWeight a m x - 1 at hid
  have hfactor : (∫ t in a..x, (2 * m t) * volterraWeight a m t) =
      2 * ∫ t in a..x, m t * volterraWeight a m t := by
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
  rw [hfactor] at hid
  calc
    _ ≤ ∫ t in a..x, m t * volterraWeight a m t := by
      apply intervalIntegral.integral_mono_on hx.1 (hci.abs.mul_continuousOn hwc)
        (hmi.mul_continuousOn hwc)
      intro t ht
      have ht' : t ∈ uIcc a b := hsub (by simpa only [uIcc_of_le hx.1] using ht)
      exact mul_le_mul_of_nonneg_right (hdom t ht') (volterraWeight_pos a m t).le
    _ ≤ _ := by linarith

end CauchyHorizon
