import CauchyHorizon.Reduced.LongitudinalFlux

/-! Finite-rectangle radial bounds from the horizontal flux and the incoming gauge. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.radial_horizontal_integral
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (u : Icc 0 U) (v : Icc 0 V) :
    (∫ t in (0 : ℝ)..u, -intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v) =
      x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0 := by
  have hc : Continuous (fun t => intervalExtension hU x.1 t v 0) := by fun_prop
  have hn : Continuous (fun t => intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v) := by fun_prop
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le u.property.1 hc.continuousOn
    (fun t ht => by
      have htU : t ∈ Icc 0 U := ⟨ht.1.le, ht.2.le.trans u.property.2⟩
      simpa only [intervalExtension_apply, projIcc_of_mem hU htU] using
        (hx.radial_hasDerivWithinAt hr hzin hinu v htU).hasDerivAt
          (Icc_mem_nhds ht.1 (ht.2.trans_le u.property.2)))
    (hn.intervalIntegrable (0 : ℝ) u)
  simp only [intervalExtension_apply, projIcc_of_mem hU u.property,
    projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩)] at hp
  rw [intervalIntegral.integral_neg]
  change (∫ t in (0 : ℝ)..u, intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v) =
    x.1 u v 0 - x.1 ⟨0, le_rfl, hU⟩ v 0 at hp
  linarith only [hp]

theorem IsWaveIntegral.radial_flux_gap_bound
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {ρ R B : ℝ} (hρ : 0 < ρ) (hR : ρ ≤ R) (hB : 0 ≤ B)
    (hP : ∀ r ∈ Icc ρ R, |radialPotential r e Λ| ≤ B)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0)
    (haxis : ∀ v, x.1 ⟨0, le_rfl, hU⟩ v 0 ≤ R)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v ≤ 0)
    (homega : ∀ u v, Real.exp (x.1 u v 2) ≤ -4 * radialNuField hV e Λ zIn x.1 hr u v)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.1 u v 0 ≤ R ∧
      (∫ t in (0 : ℝ)..u, Real.exp (intervalExtension hU x.1 t v 2)) ≤
        4 * (x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) ∧
      |x.2.1 u v 0| ≤ (R * |vOut v 0| + 4 * R * B *
        (x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0)) / ρ := by
  let N := radialNuField hV e Λ zIn x.1 hr
  have hRp : 0 < R := hρ.trans_le hR
  have hrp (a : Icc 0 U) (b : Icc 0 V) : 0 < x.1 a b 0 := hρ.trans_le (hlo a b)
  have hupper (a : Icc 0 U) : x.1 a v 0 ≤ R := by
    have hn := intervalIntegral.integral_nonneg (μ := volume) a.property.1
      (fun t _ => neg_nonneg.2 (hnu (projIcc 0 U hU t) v))
    change 0 ≤ ∫ t in (0 : ℝ)..a, -intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v at hn
    rw [hx.radial_horizontal_integral hr hzin hinu a v] at hn
    exact (sub_nonneg.1 hn).trans (haxis v)
  have hc : Continuous (fun t => Real.exp (intervalExtension hU x.1 t v 2)) := by fun_prop
  have hn : Continuous (fun t => -intervalExtension hU N t v) := by fun_prop
  have hOmega : (∫ t in (0 : ℝ)..u, Real.exp (intervalExtension hU x.1 t v 2)) ≤
      4 * (x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..u, 4 * (-intervalExtension hU N t v) := by
        apply intervalIntegral.integral_mono_on u.property.1 (hc.intervalIntegrable _ _)
          ((continuous_const.mul hn).intervalIntegrable _ _)
        intro t _ht
        change Real.exp (x.1 (projIcc 0 U hU t) v 2) ≤ 4 * (-N (projIcc 0 U hU t) v)
        simpa only [mul_neg, neg_mul] using homega (projIcc 0 U hU t) v
      _ = 4 * (x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) := by
        rw [intervalIntegral.integral_const_mul, hx.radial_horizontal_integral hr hzin hinu u v]
  let F := radialFluxField e Λ (flipRectangle x.1) (fun v u => hr u v) v
  have hf : |continuousPrimitive hU F u| ≤
      4 * R * B * (x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) := by
    change |∫ t in (0 : ℝ)..u, intervalExtension hU F t| ≤ _
    calc
      _ ≤ ∫ t in (0 : ℝ)..u, |intervalExtension hU F t| :=
        intervalIntegral.abs_integral_le_integral_abs u.property.1
      _ ≤ ∫ t in (0 : ℝ)..u, (R * B) * Real.exp (intervalExtension hU x.1 t v 2) := by
        apply intervalIntegral.integral_mono_on u.property.1
          ((intervalExtension hU F).continuous.abs.intervalIntegrable _ _)
          ((continuous_const.mul hc).intervalIntegrable _ _)
        intro t _ht
        let a := projIcc 0 U hU t
        change |x.1 a v 0 * (Real.exp (x.1 a v 2) * radialPotential (x.1 a v 0) e Λ)| ≤
          (R * B) * Real.exp (x.1 a v 2)
        rw [abs_mul, abs_mul, abs_of_pos (hrp a v), abs_of_pos (Real.exp_pos _)]
        have hp := mul_le_mul (hupper a) (hP _ ⟨hlo a v, hupper a⟩) (abs_nonneg _) hRp.le
        nlinarith only [mul_le_mul_of_nonneg_right hp (Real.exp_pos (x.1 a v 2)).le]
      _ = (R * B) * ∫ t in (0 : ℝ)..u, Real.exp (intervalExtension hU x.1 t v 2) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ 4 * R * B * (x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) := by
        nlinarith only [mul_le_mul_of_nonneg_left hOmega (mul_nonneg hRp.le hB)]
  have hflux := hx.horizontal_radial_flux hr hzin u v
  have hlambda : x.1 u v 0 * |x.2.1 u v 0| ≤ R * |vOut v 0| +
      4 * R * B * (x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) := by
    calc
      _ = |x.1 u v 0 * x.2.1 u v 0| := by rw [abs_mul, abs_of_pos (hrp u v)]
      _ ≤ |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 0| + |continuousPrimitive hU F u| := by
        rw [hflux]
        exact abs_add_le _ _
      _ ≤ R * |vOut v 0| + 4 * R * B * (x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) := by
        rw [abs_mul, abs_of_pos (hrp ⟨0, le_rfl, hU⟩ v)]
        exact add_le_add (mul_le_mul_of_nonneg_right (haxis v) (abs_nonneg _)) hf
  refine ⟨hupper u, hOmega, ?_⟩
  apply (le_div_iff₀ hρ).2
  calc
    _ = ρ * |x.2.1 u v 0| := mul_comm _ _
    _ ≤ x.1 u v 0 * |x.2.1 u v 0| := mul_le_mul_of_nonneg_right (hlo u v) (abs_nonneg _)
    _ ≤ _ := hlambda

theorem IsWaveIntegral.finite_radial_flux_bound
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {ρ R L B : ℝ} (hρ : 0 < ρ) (hR : ρ ≤ R) (hB : 0 ≤ B)
    (hP : ∀ r ∈ Icc ρ R, |radialPotential r e Λ| ≤ B)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0)
    (haxis : ∀ v, x.1 ⟨0, le_rfl, hU⟩ v 0 ≤ R)
    (hvel : ∀ v, |vOut v 0| ≤ L)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v ≤ 0)
    (homega : ∀ u v, Real.exp (x.1 u v 2) ≤ -4 * radialNuField hV e Λ zIn x.1 hr u v)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.1 u v 0 ≤ R ∧
      (∫ t in (0 : ℝ)..u, Real.exp (intervalExtension hU x.1 t v 2)) ≤ 4 * R ∧
      |x.2.1 u v 0| ≤ (R * L + 4 * R ^ 2 * B) / ρ := by
  have hb := hx.radial_flux_gap_bound hr hzin hinu hρ hR hB hP hlo haxis hnu homega u v
  have hgap : x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0 ≤ R := by
    linarith only [haxis v, hlo u v, hρ]
  refine ⟨hb.1, hb.2.1.trans (by linarith only [hgap]), hb.2.2.trans ?_⟩
  apply div_le_div_of_nonneg_right _ hρ.le
  have hg := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hρ.le.trans hR)) hB)
  have hv := mul_le_mul_of_nonneg_left (hvel v) (hρ.le.trans hR)
  nlinarith only [hg, hv]

theorem IsWaveIntegral.radial_gap_weighted_bound
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {N a : ℝ} (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v ≤ 0)
    (hbound : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (u : Icc 0 U) (v : Icc 0 V) :
    0 ≤ x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0 ∧
      x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0 ≤ N * u * Real.exp (a * v) := by
  rw [← hx.radial_horizontal_integral hr hzin hinu u v]
  refine ⟨intervalIntegral.integral_nonneg u.property.1 (fun t _ =>
    neg_nonneg.2 (hnu (projIcc 0 U hU t) v)), ?_⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => -intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v)
    (C := N * Real.exp (a * v)) (a := (0 : ℝ)) (b := (u : ℝ))
    (fun t _ => by simpa only [norm_neg, Real.norm_eq_abs, intervalExtension_apply] using hbound (projIcc 0 U hU t) v)
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg u.property.1] at hb
  exact (le_abs_self _).trans (hb.trans_eq (by ring))

end CauchyHorizon
