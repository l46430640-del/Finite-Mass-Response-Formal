import CauchyHorizon.Reduced.OuterScalar

/-! Weighted scalar transport summed by Gronwall, with no small-kernel assumption. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 800000 in
theorem IsWaveIntegral.weighted_scalar_bound {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {a c ρ R N L H J δ : ℝ} (hc : 0 ≤ c) (hac : c < a) (hρ : 0 < ρ)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hout : ∀ v : Icc 0 V, Real.exp (c * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| ≤ H)
    (hinput : Real.exp (c * V) * (∫ t in (0 : ℝ)..U, |uIn t 1|) ≤ J)
    (hwidth : U * Real.exp (a * V) ≤ δ) :
    let E := ((H + L * (R / ρ) * J) / ρ) * Real.exp (L * N * δ / (ρ ^ 2 * (a - c)))
    (∀ u v, |x.2.1 u v 1| ≤ E * Real.exp (-c * v)) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        |x.2.2 u v 1| ≤ (R / ρ) * |uIn u 1| + (N / (ρ * (a - c))) * E * Real.exp ((a - c) * v) := by
  let α := R / ρ
  let β := N / (ρ * (a - c))
  let D := (H + L * α * J) / ρ
  let K := L * β / ρ * Real.exp (a * V)
  let E := D * Real.exp (L * N * δ / (ρ ^ 2 * (a - c)))
  let ν := radialNuField hV e Λ zIn x.1 hr
  let weight : C(Icc 0 V, ℝ) := ⟨fun v => Real.exp (c * v), by fun_prop⟩
  let W := ContinuousMap.const (Icc 0 U) weight * waveCoordinateField 1 x.2.1
  let F : ℝ → ℝ := fun t => ‖intervalExtension hU W t‖
  have hα : 0 ≤ α := div_nonneg hR hρ.le
  have hβ : 0 ≤ β := div_nonneg hN (mul_nonneg hρ.le (sub_pos.2 hac).le)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hFc : Continuous F := (intervalExtension hU W).continuous.norm
  have hw (u : Icc 0 U) (v : Icc 0 V) : |x.2.1 u v 1| ≤ ‖W u‖ * Real.exp (-c * v) := by
    have hb := (W u).norm_coe_le_norm v
    change ‖Real.exp (c * v) * x.2.1 u v 1‖ ≤ ‖W u‖ at hb
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] at hb
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hb)
  have htrans : ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      |x.2.2 t v 1| ≤ α * |uIn t 1| + β * F t * Real.exp ((a - c) * v) := by
    filter_upwards [hx.zeta_transport hr hinu] with t ht
    intro v
    let u := projIcc 0 U hU t
    have hcor := scalarTransportCorrection_weighted_bound (hV := hV) hac hN (norm_nonneg (W u))
      (ContinuousMap.const (Icc 0 U) (ν u)) (ContinuousMap.const (Icc 0 U) (x.2.1 u))
      (fun _ v => hν u v) (fun _ v => hw u v) u v
    have hb : ρ * |x.2.2 t v 1| ≤ R * |uIn t 1| + N * F t / (a - c) * Real.exp ((a - c) * v) := by
      calc
        _ ≤ x.1 u v 0 * |x.2.2 t v 1| := mul_le_mul_of_nonneg_right (hlo u v) (abs_nonneg _)
        _ = |x.1 u v 0 * x.2.2 t v 1| := by rw [abs_mul, abs_of_pos (hρ.trans_le (hlo u v))]
        _ ≤ _ := by
          rw [ht v]
          exact (abs_add_le _ _).trans (add_le_add
            (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hin u) (abs_nonneg _)) hcor)
    apply (le_div_iff₀ hρ).2 (by simpa only [mul_comm ρ] using hb) |>.trans_eq ?_
    dsimp only [α, β]
    field_simp
  have hfi : IntervalIntegrable (fun t => uIn t 1) volume 0 U := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    exact (ContinuousLinearMap.proj (1 : Fin 3) : WaveVector →L[ℝ] ℝ).integrable_comp
      ((Lp.memLp uIn).integrable (by norm_num))
  have hvol (u : Icc 0 U) : ‖W u‖ ≤ D + K * ∫ t in (0 : ℝ)..u, F t := by
    have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
      rw [uIcc_of_le u.property.1, uIcc_of_le hU]
      exact Icc_subset_Icc le_rfl u.property.2
    have hfu := hfi.abs.mono_set hsub
    have hFr := hFc.intervalIntegrable (μ := volume) (0 : ℝ) u
    have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..u, F t :=
      intervalIntegral.integral_nonneg u.property.1 (fun t _ => norm_nonneg _)
    apply (ContinuousMap.norm_le _ (add_nonneg hD (mul_nonneg hK hnonneg))).2
    intro v
    have hb : |∫ t in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1| ≤
        L * (α * (∫ t in (0 : ℝ)..u, |uIn t 1|) + β * Real.exp ((a - c) * v) * ∫ t in (0 : ℝ)..u, F t) := by
      have hd : ∀ᵐ t ∂volume, t ∈ Ioc (0 : ℝ) u →
          ‖-x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1‖ ≤
            L * (α * |uIn t 1| + (β * Real.exp ((a - c) * v)) * F t) := by
        apply (ae_restrict_iff' measurableSet_Ioc).1
        have hioc : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
        filter_upwards [ae_mono (Measure.restrict_mono hioc le_rfl) htrans] with t ht
        rw [Real.norm_eq_abs, abs_mul, abs_neg]
        have hh := mul_le_mul (hlam (projIcc 0 U hU t) v) (ht v) (abs_nonneg _) hL
        simpa only [mul_right_comm β] using hh
      have hi := intervalIntegral.norm_integral_le_of_norm_le u.property.1 hd
        (((hfu.const_mul α).add (hFr.const_mul (β * Real.exp ((a - c) * v)))).const_mul L)
      simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hfu.const_mul α) (hFr.const_mul (β * Real.exp ((a - c) * v)))] using hi
    have hj : Real.exp (c * v) * (∫ t in (0 : ℝ)..u, |uIn t 1|) ≤ J := by
      have hi := intervalIntegral.integral_mono_interval le_rfl u.property.1 u.property.2
        (Filter.Eventually.of_forall (fun t => abs_nonneg (uIn t 1))) hfi.abs
      exact (mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 hc)) hi
        (intervalIntegral.integral_nonneg u.property.1 (fun _ _ => abs_nonneg _)) (Real.exp_pos _).le).trans hinput
    have ht : |x.1 u v 0 * x.2.1 u v 1| ≤ |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
        L * (α * (∫ t in (0 : ℝ)..u, |uIn t 1|) + β * Real.exp ((a - c) * v) * ∫ t in (0 : ℝ)..u, F t) := by
      rw [hx.theta_integral hzin u v]
      exact (abs_add_le _ _).trans (add_le_add_right hb _)
    have hh := mul_le_mul_of_nonneg_left ht (Real.exp_pos (c * v)).le
    rw [abs_mul, abs_of_pos (hρ.trans_le (hlo u v))] at hh
    have he : Real.exp (c * v) * Real.exp ((a - c) * v) = Real.exp (a * v) := by
      rw [← Real.exp_add]; congr 1; ring
    have hh' : Real.exp (c * v) * (x.1 u v 0 * |x.2.1 u v 1|) ≤
        Real.exp (c * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
        L * α * (Real.exp (c * v) * ∫ t in (0 : ℝ)..u, |uIn t 1|) +
        L * β * Real.exp (a * v) * ∫ t in (0 : ℝ)..u, F t := by
      apply hh.trans_eq
      rw [← he]
      ring
    have hj' := mul_le_mul_of_nonneg_left hj (mul_nonneg hL hα)
    have hK' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left v.property.2 (hc.trans hac.le))) (mul_nonneg hL hβ)) hnonneg
    have hr' := mul_le_mul_of_nonneg_right (hlo u v)
      (mul_nonneg (Real.exp_pos (c * v)).le (abs_nonneg (x.2.1 u v 1)))
    have hbound : ρ * (Real.exp (c * v) * |x.2.1 u v 1|) ≤
        H + L * α * J + L * β * Real.exp (a * V) * ∫ t in (0 : ℝ)..u, F t := by
      nlinarith only [hh', hj', hK', hr', hout v]
    change ‖Real.exp (c * v) * x.2.1 u v 1‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply ((le_div_iff₀ hρ).2 (by simpa only [mul_comm ρ] using hbound)).trans_eq
    dsimp only [D, K]
    ring
  have hlong (u : Icc 0 U) : ‖W u‖ ≤ E := by
    have hb (t : ℝ) (ht : t ∈ Icc 0 U) : F t ≤ D + K * ∫ s in 0..t, F s := by
      simpa only [F, intervalExtension_apply, projIcc_of_mem hU ht] using hvol ⟨t, ht⟩
    have hh := continuous_volterra_bound hFc hD hK hb u.property
    have he : K * U ≤ L * N * δ / (ρ ^ 2 * (a - c)) := by
      have hcoef : L * β / ρ = L * N / (ρ ^ 2 * (a - c)) := by dsimp only [β]; field_simp
      dsimp only [K]
      calc
        _ = (L * β / ρ) * (U * Real.exp (a * V)) := by ring
        _ ≤ (L * β / ρ) * δ := mul_le_mul_of_nonneg_left hwidth (by positivity)
        _ = _ := by rw [hcoef]; ring
    have hh' : ‖W u‖ ≤ D * Real.exp (K * U) := by
      simpa only [F, intervalExtension_apply, projIcc_of_mem hU u.property] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 he) hD)
  refine ⟨fun u v => (hw u v).trans (mul_le_mul_of_nonneg_right (hlong u) (Real.exp_pos _).le), ?_⟩
  filter_upwards [htrans] with t ht
  intro v
  exact (ht v).trans (add_le_add_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hlong (projIcc 0 U hU t)) hβ) (Real.exp_pos _).le) _)

end CauchyHorizon
