import CauchyHorizon.Radial.ModeDerivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Quantitative inner-endpoint bounds for the actual positive radial mode. -/

open Set MeasureTheory
open scoped Topology

namespace CauchyHorizon.Background

variable (B : CauchyHorizon.Background)

theorem exists_inner_weight_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc B.inner B.event,
      B.criticalWeight r ≤ C * (r - B.inner) ^ (-1 / 2 : ℝ) ∧
      |B.F r| ≤ C * (r - B.inner) := by
  let g : ℝ → ℝ := fun r => (B.event - r) ^ B.criticalExponent *
    Real.exp (B.criticalExponent * B.regularLog r)
  let f : ℝ → ℝ := fun r => -B.cosmological * (r - B.event) *
    (r - B.cosmologicalRadius) * (r - B.negativeRoot) / (3 * r ^ 2)
  have hg : ContinuousOn g (Icc B.inner B.event) :=
    ((continuousOn_const.sub continuousOn_id).rpow_const
      (fun _ _ => Or.inr B.criticalExponent_pos.le)).mul
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul B.regularLog_continuousOn))
  have hf : ContinuousOn f (Icc B.inner B.event) := by
    apply ContinuousOn.div
      (((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).mul
        (continuousOn_id.sub continuousOn_const)).mul
        (continuousOn_id.sub continuousOn_const))
      (continuousOn_const.mul (continuousOn_id.pow 2))
    intro r hr
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (B.inner_pos.trans_le hr.1).ne')
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨max 0 (max G H), le_max_left _ _, ?_⟩
  intro r hr
  constructor
  · calc
      B.criticalWeight r = g r * (r - B.inner) ^ (-1 / 2 : ℝ) := by
        dsimp [criticalWeight, g]
        ring
      _ ≤ max 0 (max G H) * (r - B.inner) ^ (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right
          ((le_abs_self _).trans ((hG r hr).trans
            ((le_max_left G H).trans (le_max_right 0 (max G H)))))
          (Real.rpow_nonneg (sub_nonneg.2 hr.1) _)
  · have heq : B.F r = f r * (r - B.inner) := by
      rw [B.factorization (B.inner_pos.trans_le hr.1).ne']
      dsimp [f]
      ring
    rw [heq, abs_mul, abs_of_nonneg (sub_nonneg.2 hr.1)]
    exact mul_le_mul_of_nonneg_right ((hH r hr).trans
      ((le_max_right G H).trans (le_max_right 0 (max G H)))) (sub_nonneg.2 hr.1)

theorem radialMode_inner_remainders (hb : B.criticalExponent < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Icc 0 B.radialLength,
      |B.transmission hb - (B.radialMode hb).1 x| ≤
        C * (B.radialLength - x) ^ (1 / 2 : ℝ) ∧
      |B.criticalWeight (B.event - x) * (B.radialMode hb).2 x| ≤
        C * (B.radialLength - x) ^ (-1 / 2 : ℝ) ∧
      |(-B.F (B.event - x)) *
        (B.criticalWeight (B.event - x) * (B.radialMode hb).2 x)| ≤
        C * (B.radialLength - x) ^ (1 / 2 : ℝ) := by
  obtain ⟨Q, hQ, hweight⟩ := B.exists_inner_weight_bound
  let A := B.outerRate * Q / B.inner
  have hA : 0 ≤ A := div_nonneg (mul_nonneg B.outerRate_pos.le hQ) B.inner_pos.le
  let N := ‖(B.radialMode hb).2‖
  have hN : 0 ≤ N := norm_nonneg _
  have hcoeff (t : ℝ) (ht : t ∈ Icc 0 B.radialLength) :
      |B.coefficientX t| ≤ A * (B.radialLength - t) ^ (-1 / 2 : ℝ) := by
    have hr := B.inward_mem ht
    have hdist : B.event - t - B.inner = B.radialLength - t := by
      dsimp [radialLength]
      ring
    rw [abs_of_nonneg (B.coefficients_nonneg ht).1]
    calc
      B.coefficientX t ≤
          B.outerRate * (Q * (B.radialLength - t) ^ (-1 / 2 : ℝ)) / B.inner := by
        apply div_le_div₀ (mul_nonneg B.outerRate_pos.le
          (mul_nonneg hQ (Real.rpow_nonneg (sub_nonneg.2 ht.2) _)))
          (mul_le_mul_of_nonneg_left (by simpa only [hdist] using (hweight _ hr).1)
            B.outerRate_pos.le) B.inner_pos hr.1
      _ = _ := by dsimp [A]; ring
  refine ⟨max (2 * A * N) (max (Q * N) (Q * Q * N)),
    le_trans (by positivity : 0 ≤ 2 * A * N) (le_max_left _ _), ?_⟩
  intro x
  have hdist : B.event - (x : ℝ) - B.inner = B.radialLength - x := by
    dsimp [radialLength]
    ring
  have hd : 0 ≤ B.radialLength - x := sub_nonneg.2 x.property.2
  have hp := Real.rpow_nonneg hd (-1 / 2 : ℝ)
  have hs := Real.rpow_nonneg hd (1 / 2 : ℝ)
  have hsplit : (B.radialLength - x) *
      (B.radialLength - x) ^ (-1 / 2 : ℝ) =
      (B.radialLength - x) ^ (1 / 2 : ℝ) := by
    rcases eq_or_lt_of_le hd with hz | hz
    · rw [← hz]
      norm_num
    · calc
        _ = (B.radialLength - x) ^ (1 + (-1 / 2 : ℝ)) := by
          rw [Real.rpow_add hz, Real.rpow_one]
        _ = _ := by norm_num
  have hV : |(B.radialMode hb).2 x| ≤ N :=
    (B.radialMode hb).2.norm_coe_le_norm x
  have hW : |B.criticalWeight (B.event - x) * (B.radialMode hb).2 x| ≤
      Q * N * (B.radialLength - x) ^ (-1 / 2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (B.criticalWeight_nonneg (B.inward_mem x.property))]
    calc
      _ ≤ (Q * (B.radialLength - x) ^ (-1 / 2 : ℝ)) * N :=
        mul_le_mul (by simpa only [hdist] using
          (hweight _ (B.inward_mem x.property)).1) hV (abs_nonneg _) (mul_nonneg hQ hp)
      _ = _ := by ring
  have hX : |B.transmission hb - (B.radialMode hb).1 x| ≤
      (2 * A * N) * (B.radialLength - x) ^ (1 / 2 : ℝ) := by
    have hi : IntervalIntegrable (fun t => (B.radialLength - t) ^ (-1 / 2 : ℝ))
        volume (x : ℝ) B.radialLength := by
      simpa only [sub_zero, sub_sub_cancel] using
        ((intervalIntegral.intervalIntegrable_rpow'
          (a := (0 : ℝ)) (b := B.radialLength - x)
          (by norm_num : (-1 : ℝ) < -1 / 2)).comp_sub_left B.radialLength).symm
    have hint : (∫ t in (x : ℝ)..B.radialLength,
        (B.radialLength - t) ^ (-1 / 2 : ℝ)) =
        2 * (B.radialLength - x) ^ (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_comp_sub_left
        (fun t : ℝ => t ^ (-1 / 2 : ℝ)) B.radialLength, sub_self,
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
      norm_num
      ring
    calc
      _ ≤ (∫ t in (x : ℝ)..B.radialLength, |B.coefficientX t|) * N :=
        volterraPair_terminal_remainder B.radialLength_pos.le
          (B.coefficients_integrable hb).1 (B.radialMode_spec hb) x
      _ ≤ (∫ t in (x : ℝ)..B.radialLength,
          A * (B.radialLength - t) ^ (-1 / 2 : ℝ)) * N := by
        apply mul_le_mul_of_nonneg_right _ hN
        apply intervalIntegral.integral_mono_on x.property.2
          (((B.coefficients_integrable hb).1.mono_set
            (by simpa only [uIcc_of_le x.property.2, uIcc_of_le B.radialLength_pos.le]
              using Icc_subset_Icc x.property.1 le_rfl)).abs) (hi.const_mul A)
        intro t ht
        exact hcoeff t ⟨x.property.1.trans ht.1, ht.2⟩
      _ = _ := by rw [intervalIntegral.integral_const_mul, hint]; ring
  refine ⟨hX.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hs),
    hW.trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hp), ?_⟩
  calc
    _ = |B.F (B.event - x)| *
        |B.criticalWeight (B.event - x) * (B.radialMode hb).2 x| := by
      rw [abs_mul, abs_neg]
    _ ≤ (Q * (B.radialLength - x)) *
        (Q * N * (B.radialLength - x) ^ (-1 / 2 : ℝ)) :=
      mul_le_mul (by simpa only [hdist] using
        (hweight _ (B.inward_mem x.property)).2) hW (abs_nonneg _) (mul_nonneg hQ hd)
    _ = (Q * Q * N) * (B.radialLength - x) ^ (1 / 2 : ℝ) := by
      calc
        _ = (Q * Q * N) * ((B.radialLength - x) *
            (B.radialLength - x) ^ (-1 / 2 : ℝ)) := by ring
        _ = _ := by rw [hsplit]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) hs

theorem radialMode_W_hasDerivAt (hb : B.criticalExponent < 1) {x : ℝ}
    (hx : x ∈ Ioo 0 B.radialLength) :
    HasDerivAt (extendCurve B.radialLength_pos.le (B.radialMode hb).1)
      (B.outerRate / (B.event - x) *
        (B.criticalWeight (B.event - x) *
          extendCurve B.radialLength_pos.le (B.radialMode hb).2 x)) x ∧
    HasDerivAt (fun t => B.criticalWeight (B.event - t) *
        extendCurve B.radialLength_pos.le (B.radialMode hb).2 t)
      (B.innerRate / (-B.F (B.event - x)) *
        (B.criticalWeight (B.event - x) *
          extendCurve B.radialLength_pos.le (B.radialMode hb).2 x) +
        1 / (B.outerRate * (B.event - x)) *
          extendCurve B.radialLength_pos.le (B.radialMode hb).1 x) x := by
  have hr := B.inward_mem_interior hx
  have hq := B.criticalWeight_hasDerivAt hr
  have hm := B.radialMode_hasDerivAt hb hx
  constructor
  · apply hm.1.congr_deriv
    dsimp [coefficientX]
    ring
  · apply ((hq.comp x ((hasDerivAt_id x).const_sub B.event)).mul hm.2).congr_deriv
    dsimp [coefficientV]
    have hq0 := (B.criticalWeight_pos hr).ne'
    field_simp

end CauchyHorizon.Background
