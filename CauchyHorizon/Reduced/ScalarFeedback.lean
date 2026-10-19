import CauchyHorizon.Reduced.RadiationEnergy
import CauchyHorizon.Reduced.LongitudinalFlux

/-! Signed outer scalar transport separates the direct incoming term from its feedback. -/

open MeasureTheory Set

namespace CauchyHorizon

noncomputable def scalarRadiationFeedback {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (z w : WaveRectangle U V) (ν : C(Icc 0 U, C(Icc 0 V, ℝ)))
    (hr : ∀ u v, z u v 0 ≠ 0) : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  flipRectangle (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (continuousPrimitiveL hU)
    (flipRectangle (-waveCoordinateField 0 w * scalarRegularPart hV z w ν hr)))

theorem IsWaveIntegral.theta_incoming_feedback {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.1 u v 0 * x.2.1 u v 1 = x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1 +
      (∫ t in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU t) v 0 *
        (zIn (projIcc 0 U hU t) 0 / x.1 (projIcc 0 U hU t) v 0) * uIn t 1) +
      scalarRadiationFeedback hU hV x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr u v := by
  let A : C(Icc 0 U, ℝ) :=
    ⟨fun w => -x.2.1 w v 0 * scalarIncomingCoefficient zIn x.1 hr w v, by fun_prop⟩
  let B : C(Icc 0 U, ℝ) :=
    ⟨fun w => -x.2.1 w v 0 *
      scalarRegularPart hV x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr w v, by fun_prop⟩
  have hf : MemLp (fun t => uIn t 1) 2 (volume.restrict (Icc 0 U)) :=
    (ContinuousLinearMap.proj (1 : Fin 3) : WaveVector →L[ℝ] ℝ).comp_memLp' (Lp.memLp uIn)
  have hAi : IntervalIntegrable (fun t => A (projIcc 0 U hU t) * uIn t 1) volume 0 u := by
    have hp : MemLp (fun t => A (projIcc 0 U hU t) * uIn t 1) 2
        (volume.restrict (Icc 0 U)) := hf.mul (intervalExtension hU A).memLp_top
    have hi : IntegrableOn (fun t => A (projIcc 0 U hU t) * uIn t 1) (Icc 0 U) :=
      hp.integrable (by norm_num)
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le u.property.1).2
    exact hi.mono_set (Icc_subset_Icc le_rfl u.property.2)
  have hBi : IntervalIntegrable (fun t => B (projIcc 0 U hU t)) volume 0 u :=
    (intervalExtension hU B).continuous.intervalIntegrable (0 : ℝ) u
  have he : (fun t => -x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1) =ᵐ[
      volume.restrict (Icc 0 U)] fun t => A (projIcc 0 U hU t) * uIn t 1 +
        B (projIcc 0 U hU t) := by
    filter_upwards [hx.scalar_decomposition hr hinu] with t ht
    have hh := congrArg (fun q : C(Icc 0 V, ℝ) => q v) ht
    change x.2.2 t v 1 = uIn t 1 * scalarIncomingCoefficient zIn x.1 hr (projIcc 0 U hU t) v +
      scalarRegularPart hV x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr (projIcc 0 U hU t) v at hh
    rw [hh]
    dsimp only [A, B, ContinuousMap.coe_mk]
    ring
  have hs : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
  have heq : (∫ t in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1) =
      ∫ t in (0 : ℝ)..u, A (projIcc 0 U hU t) * uIn t 1 + B (projIcc 0 U hU t) := by
    simp only [intervalIntegral.integral_of_le u.property.1]
    exact integral_congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) he)
  rw [hx.theta_integral hzin u v, heq, intervalIntegral.integral_add hAi hBi]
  change _ + (_ + _) = _ + _ + _
  rw [add_assoc]
  rfl

theorem IsWaveIntegral.outer_feedback_kernel_at {U V e Λ a k ρ R N L δ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (B : Icc 0 V → ℝ) (hB : Antitone B)
    (hlo : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v → ρ ≤ x.1 u v 0)
    (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hwidth : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v → (u : ℝ) * Real.exp (a * v) ≤ δ)
    (M : C(Icc 0 V, ℝ)) (hM0 : ∀ v, 0 ≤ M v)
    (hM : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v)
    (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ B v)
    (hlam : ∀ w : Icc 0 U, w ≤ u → |x.2.1 w v 0| ≤ L) :
      Real.exp (k * v) *
          |scalarRadiationFeedback hU hV x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr u v| ≤
        (L * N * δ / ρ ^ 2) * causalExpIntegral hV (a - k) M v := by
  have hglobal (q : Icc 0 U) (t : Icc 0 V) (_hq : (q : ℝ) ≤ B t) : |x.2.1 q t 0| ≤ ‖x.2.1‖ :=
    (norm_le_pi_norm (x.2.1 q t) 0).trans
      (((x.2.1 q).norm_coe_le_norm t).trans (x.2.1.norm_coe_le_norm q))
  have hcor := (hx.outer_radiation_majorant_on hr hzin hinu hρ hN (norm_nonneg x.2.1) B hB hlo hin hν hglobal
    (ContinuousMap.const _ (ContinuousMap.const _ 1)) (fun _ => monotone_const) M hM0
    (fun u v hu => by simpa using hM u v hu)).1
  simp only [ContinuousMap.const_apply, mul_one] at hcor
  let J := causalExpIntegral hV (a - k) M v
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg v.property.1
    (fun t _ => mul_nonneg (Real.exp_pos _).le (hM0 _))
  let K := (N / ρ) * Real.exp (a * v) * J
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (u : ℝ)) (C := L * K / ρ)
    (f := fun t => Real.exp (k * v) * (-x.2.1 (projIcc 0 U hU t) v 0 *
      scalarRegularPart hV x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr (projIcc 0 U hU t) v))
    (fun t ht => ?_)
  · rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), sub_zero, abs_of_nonneg u.property.1] at hb
    have hw := mul_le_mul_of_nonneg_right (hwidth u v hu)
      (mul_nonneg (div_nonneg (mul_nonneg hL hN) (sq_nonneg ρ)) hJ)
    change Real.exp (k * v) * |scalarRadiationFeedback hU hV x.1 x.2.1
      (radialNuField hV e Λ zIn x.1 hr) hr u v| ≤ _ at hb
    dsimp only [K] at hb
    dsimp only [J] at *
    calc
      _ ≤ _ := hb
      _ = (u : ℝ) * Real.exp (a * v) * ((L * N / ρ ^ 2) * causalExpIntegral hV (a - k) M v) := by ring
      _ ≤ _ := hw
      _ = _ := by ring
  · rw [uIoc_of_le u.property.1] at ht
    have htU : t ∈ Icc 0 U := ⟨ht.1.le, ht.2.trans u.property.2⟩
    have htB : t ≤ B v := ht.2.trans hu
    have hrpos := hρ.trans_le (hlo ⟨t, htU⟩ v htB)
    have hc := hcor ⟨t, htU⟩ v htB
    simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
      projIcc_of_mem hU htU]
    change Real.exp (k * v) * (|x.2.1 ⟨t, htU⟩ v 0| *
      |scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 ⟨t, htU⟩ v /
        x.1 ⟨t, htU⟩ v 0|) ≤ _
    rw [abs_div, abs_of_pos hrpos]
    calc
      _ = |x.2.1 ⟨t, htU⟩ v 0| * (Real.exp (k * v) *
        |scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 ⟨t, htU⟩ v|) /
          x.1 ⟨t, htU⟩ v 0 := by ring
      _ ≤ L * K / x.1 ⟨t, htU⟩ v 0 := div_le_div_of_nonneg_right
        (mul_le_mul (hlam ⟨t, htU⟩ ht.2) hc (by positivity) hL) hrpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hL hK) hρ (hlo ⟨t, htU⟩ v htB)

theorem IsWaveIntegral.outer_feedback_kernel_on {U V e Λ a k ρ R N L δ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (B : Icc 0 V → ℝ) (hB : Antitone B)
    (hlo : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v → ρ ≤ x.1 u v 0)
    (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v → |x.2.1 u v 0| ≤ L)
    (hwidth : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v → (u : ℝ) * Real.exp (a * v) ≤ δ)
    (M : C(Icc 0 V, ℝ)) (hM0 : ∀ v, 0 ≤ M v)
    (hM : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v) :
    ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      Real.exp (k * v) *
          |scalarRadiationFeedback hU hV x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr u v| ≤
        (L * N * δ / ρ ^ 2) * causalExpIntegral hV (a - k) M v := by
  intro u v hu
  exact hx.outer_feedback_kernel_at hr hzin hinu hρ hN hL B hB hlo hin hν hwidth M hM0 hM u v hu
    (fun w hw => hlam w v ((show (w : ℝ) ≤ u from hw).trans hu))

end CauchyHorizon
