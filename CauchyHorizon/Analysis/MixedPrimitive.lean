import CauchyHorizon.Analysis.MixedSource
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The square-root horizontal gain for the mixed-norm characteristic integral. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure α} [IsFiniteMeasure μ]

theorem l2_setIntegral_bound (f : Lp E 2 μ) {s : Set α} (hs : MeasurableSet s) :
    ‖∫ x in s, f x ∂μ‖ ≤ Real.sqrt (μ.real s) * ‖f‖ := by
  let χ : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
  let B : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  let g := B.holder 1 χ f
  have he : (∫ x, g x ∂μ) = ∫ x in s, f x ∂μ := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [B.coeFn_holder (r := 1) χ f, indicatorConstLp_coeFn (p := 2) (hs := hs)
      (hμs := measure_ne_top μ s) (c := (1 : ℝ))]
      with x hx hχ
    change g x = s.indicator (fun x => f x) x
    change g x = B (χ x) (f x) at hx
    rw [hx]
    change χ x = s.indicator (fun _ => (1 : ℝ)) x at hχ
    rw [hχ]
    by_cases hxs : x ∈ s <;> simp [B, hxs]
  have hχ : ‖χ‖ ≤ Real.sqrt (μ.real s) := by
    have h := norm_indicatorConstLp_le (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := (1 : ℝ))
    simpa only [norm_one, one_mul, ENNReal.toReal_ofNat, Real.sqrt_eq_rpow] using h
  calc
    _ = ‖L1.integral g‖ := by rw [L1.integral_eq_integral, he]
    _ ≤ ‖g‖ := L1.norm_integral_le g
    _ ≤ ‖B‖ * ‖χ‖ * ‖f‖ := B.norm_holder_apply_apply_le χ f
    _ ≤ 1 * Real.sqrt (μ.real s) * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      exact mul_le_mul ContinuousLinearMap.opNorm_lsmul_le hχ (norm_nonneg χ) zero_le_one
    _ = _ := by rw [one_mul]

variable {a b : ℝ}

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem l2_intervalIntegrable (hab : a ≤ b) (f : Lp E 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun x => f x) volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 ((Lp.memLp f).integrable (by norm_num))

noncomputable def horizontalPrimitive (hab : a ≤ b) (f : Lp E 2 (volume.restrict (Icc a b))) :
    C(Icc a b, E) where
  toFun t := ∫ x in a..(t : ℝ), f x
  continuous_toFun := by
    have h := intervalIntegral.continuousOn_primitive_interval' (l2_intervalIntegrable hab f) left_mem_uIcc
    rw [uIcc_of_le hab] at h
    exact h.domRestrict

theorem horizontalPrimitive_norm_le (hab : a ≤ b) (f : Lp E 2 (volume.restrict (Icc a b))) :
    ‖horizontalPrimitive hab f‖ ≤ Real.sqrt (b - a) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  have hsub : Ioc a (t : ℝ) ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans t.property.2⟩
  have he : (volume.restrict (Icc a b)).restrict (Ioc a (t : ℝ)) = volume.restrict (Ioc a (t : ℝ)) := by
    rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 hsub]
  have hm : (volume.restrict (Icc a b)).real (Ioc a (t : ℝ)) ≤ b - a := by
    calc
      _ ≤ (volume.restrict (Icc a b)).real univ := measureReal_mono (subset_univ _)
      _ = b - a := by
        rw [measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
  have h := l2_setIntegral_bound f (s := Ioc a (t : ℝ)) measurableSet_Ioc
  change ‖∫ x in a..(t : ℝ), f x‖ ≤ _
  rw [intervalIntegral.integral_of_le t.property.1]
  have h' : ‖∫ x in Ioc a (t : ℝ), f x‖ ≤
      Real.sqrt ((volume.restrict (Icc a b)).real (Ioc a (t : ℝ))) * ‖f‖ := by
    simpa only [he] using h
  exact h'.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hm) (norm_nonneg f))

omit [CompleteSpace E] in
theorem horizontalPrimitive_sub (hab : a ≤ b) (f g : Lp E 2 (volume.restrict (Icc a b))) :
    horizontalPrimitive hab (f - g) = horizontalPrimitive hab f - horizontalPrimitive hab g := by
  ext t
  have hsub : Ioc a (t : ℝ) ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans t.property.2⟩
  have he : (fun x => (f - g) x) =ᵐ[volume.restrict (Ioc a (t : ℝ))] fun x => f x - g x :=
    ae_mono (Measure.restrict_mono hsub le_rfl) (Lp.coeFn_sub f g)
  change (∫ x in a..(t : ℝ), (f - g) x) = (∫ x in a..(t : ℝ), f x) - ∫ x in a..(t : ℝ), g x
  simp only [intervalIntegral.integral_of_le t.property.1]
  rw [integral_congr_ae he]
  have hf : IntegrableOn (fun x => f x) (Icc a b) := (Lp.memLp f).integrable (by norm_num)
  have hg : IntegrableOn (fun x => g x) (Icc a b) := (Lp.memLp g).integrable (by norm_num)
  exact integral_sub (hf.mono_set hsub) (hg.mono_set hsub)

theorem horizontalPrimitive_lipschitz (hab : a ≤ b) :
    LipschitzWith ⟨Real.sqrt (b - a), Real.sqrt_nonneg _⟩
      (horizontalPrimitive (E := E) hab) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [dist_eq_norm, ← horizontalPrimitive_sub]
  exact horizontalPrimitive_norm_le hab (f - g)

end CauchyHorizon
