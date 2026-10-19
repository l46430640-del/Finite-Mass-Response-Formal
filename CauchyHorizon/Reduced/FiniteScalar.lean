import CauchyHorizon.Reduced.ScalarCorrectionBound
import CauchyHorizon.Reduced.ScalarIntegral
import CauchyHorizon.Analysis.ContinuousGronwall

/-! Quantitative scalar bounds through the continuous longitudinal norm. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.finite_scalar_bound {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {ρ R N A H J : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R) (hN : 0 ≤ N)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N)
    (hvel : ∀ u v, |x.2.1 u v 0| ≤ A)
    (hout : ∀ v, |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| ≤ H)
    (hinput : (∫ t in (0 : ℝ)..U, |uIn t 1|) ≤ J) :
    let E := ((H + A * (R / ρ) * J) / ρ) * Real.exp ((A * (V * N / ρ) / ρ) * U)
    (∀ u : Icc 0 U, ‖waveCoordinateField 1 x.2.1 u‖ ≤ E) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        |x.2.2 u v 1| ≤ (R / ρ) * |uIn u 1| + (V * N / ρ) * E := by
  let α := R / ρ
  let β := V * N / ρ
  let D := (H + A * α * J) / ρ
  let K := A * β / ρ
  let S := waveCoordinateField 1 x.2.1
  let F : ℝ → ℝ := fun t => ‖intervalExtension hU S t‖
  have hα : 0 ≤ α := div_nonneg hR hρ.le
  have hβ : 0 ≤ β := div_nonneg (mul_nonneg hV hN) hρ.le
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hA hβ) hρ.le
  have hFc : Continuous F := (intervalExtension hU S).continuous.norm
  have hfi : IntervalIntegrable (fun t => uIn t 1) volume 0 U := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    exact (ContinuousLinearMap.proj (1 : Fin 3) : WaveVector →L[ℝ] ℝ).integrable_comp
      ((Lp.memLp uIn).integrable (by norm_num))
  have hs := hx.scalar_transverse_bound hr hinu hρ hN hlo hin hν
  have hvol (u : Icc 0 U) : ‖S u‖ ≤ D + K * ∫ t in (0 : ℝ)..u, F t := by
    have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
      rw [uIcc_of_le u.property.1, uIcc_of_le hU]
      exact Icc_subset_Icc le_rfl u.property.2
    have hfu := hfi.abs.mono_set hsub
    have hFr := hFc.intervalIntegrable (μ := volume) (0 : ℝ) u
    have hJsmall : (∫ t in (0 : ℝ)..u, |uIn t 1|) ≤ J :=
      (intervalIntegral.integral_mono_interval le_rfl u.property.1 u.property.2
        (Filter.Eventually.of_forall (fun t => abs_nonneg (uIn t 1))) hfi.abs).trans hinput
    have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..u, F t :=
      intervalIntegral.integral_nonneg u.property.1 (fun t _ => norm_nonneg _)
    apply (ContinuousMap.norm_le _ (add_nonneg hD (mul_nonneg hK hnonneg))).2
    intro v
    have hb : |∫ t in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1| ≤
        A * (α * J + β * ∫ t in (0 : ℝ)..u, F t) := by
      have hd : ∀ᵐ t ∂volume, t ∈ Ioc (0 : ℝ) u →
          ‖-x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1‖ ≤ A * (α * |uIn t 1| + β * F t) := by
        apply (ae_restrict_iff' measurableSet_Ioc).1
        have hioc : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
        filter_upwards [ae_mono (Measure.restrict_mono hioc le_rfl) hs] with t ht
        rw [Real.norm_eq_abs, abs_mul, abs_neg]
        exact mul_le_mul (hvel (projIcc 0 U hU t) v) (ht v) (abs_nonneg _) hA
      have hi := intervalIntegral.norm_integral_le_of_norm_le u.property.1 hd
        (((hfu.const_mul α).add (hFr.const_mul β)).const_mul A)
      rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hfu.const_mul α) (hFr.const_mul β),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
      exact hi.trans (mul_le_mul_of_nonneg_left
        (add_le_add_left (mul_le_mul_of_nonneg_left hJsmall hα) _) hA)
    have hrp : 0 < x.1 u v 0 := hρ.trans_le (hlo u v)
    have ht : x.1 u v 0 * |x.2.1 u v 1| ≤ H + A * (α * J + β * ∫ t in (0 : ℝ)..u, F t) := by
      calc
        _ = |x.1 u v 0 * x.2.1 u v 1| := by rw [abs_mul, abs_of_pos hrp]
        _ ≤ |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
            |∫ t in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1| := by
          rw [hx.theta_integral hzin u v]
          exact abs_add_le _ _
        _ ≤ _ := add_le_add (hout v) hb
    have htρ := (mul_le_mul_of_nonneg_right (hlo u v) (abs_nonneg (x.2.1 u v 1))).trans ht
    change |x.2.1 u v 1| ≤ D + K * ∫ t in (0 : ℝ)..u, F t
    calc
      _ ≤ (H + A * (α * J + β * ∫ t in (0 : ℝ)..u, F t)) / ρ := by
        apply (le_div_iff₀ hρ).2
        simpa only [mul_comm ρ] using htρ
      _ = _ := by dsimp only [D, K]; ring
  have hlong (u : Icc 0 U) : ‖S u‖ ≤ D * Real.exp (K * U) := by
    have hb (t : ℝ) (ht : t ∈ Icc 0 U) : F t ≤ D + K * ∫ s in 0..t, F s := by
      simpa only [F, intervalExtension_apply, projIcc_of_mem hU ht] using hvol ⟨t, ht⟩
    have hh := continuous_volterra_bound hFc hD hK hb u.property
    simpa only [F, intervalExtension_apply, projIcc_of_mem hU u.property] using hh
  refine ⟨hlong, ?_⟩
  filter_upwards [hs] with u hu
  intro v
  exact (hu v).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hlong (projIcc 0 U hU u)) hβ) _)

end CauchyHorizon
