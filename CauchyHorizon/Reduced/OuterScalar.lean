import CauchyHorizon.Reduced.FiniteScalar
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Weighted scalar estimates on finite rectangles in the outer region. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}

theorem scalarTransportCorrection_weighted_bound {a c N S : ℝ} (hac : c < a)
    (hN : 0 ≤ N) (hS : 0 ≤ S)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (w : WaveRectangle U V)
    (hν : ∀ u v, |ν u v| ≤ N * Real.exp (a * v))
    (hw : ∀ u v, |w u v 1| ≤ S * Real.exp (-c * v)) (u : Icc 0 U) (v : Icc 0 V) :
    |scalarTransportCorrection hV ν w u v| ≤ N * S / (a - c) * Real.exp ((a - c) * v) := by
  have hd : 0 < a - c := sub_pos.2 hac
  have hi : IntervalIntegrable (fun t : ℝ => N * S * Real.exp ((a - c) * t)) volume 0 v :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).const_mul (N * S)).intervalIntegrable _ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le v.property.1
    (f := fun t => -ν u (projIcc 0 V hV t) * w u (projIcc 0 V hV t) 1)
    (g := fun t => N * S * Real.exp ((a - c) * t)) (Filter.Eventually.of_forall (fun t ht => ?_)) hi
  · change |∫ t in (0 : ℝ)..v, -ν u (projIcc 0 V hV t) * w u (projIcc 0 V hV t) 1| ≤ _
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left _ hd.ne', integral_exp, mul_zero, Real.exp_zero, smul_eq_mul] at hb
    calc
      _ ≤ N * S * ((a - c)⁻¹ * (Real.exp ((a - c) * v) - 1)) := hb
      _ ≤ _ := by
        have hp := mul_nonneg (mul_nonneg hN hS) (inv_nonneg.2 hd.le)
        rw [div_eq_mul_inv]
        nlinarith only [hp]
  · have htV : t ∈ Icc 0 V := ⟨ht.1.le, ht.2.trans v.property.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_neg, projIcc_of_mem hV htV]
    calc
      _ ≤ (N * Real.exp (a * t)) * (S * Real.exp (-c * t)) :=
        mul_le_mul (hν u ⟨t, htV⟩) (hw u ⟨t, htV⟩) (abs_nonneg _) (mul_nonneg hN (Real.exp_pos _).le)
      _ = _ := by rw [mul_mul_mul_comm, ← Real.exp_add]; congr 2; ring

theorem IsWaveIntegral.outer_scalar_bound {e Λ : ℝ}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {a c ρ R N L H J δ : ℝ} (hc : 0 ≤ c) (hac : c < a) (hρ : 0 < ρ)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hJ : 0 ≤ J) (hδ : 0 ≤ δ)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hout : ∀ v : Icc 0 V, Real.exp (c * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| ≤ H)
    (hinput : Real.exp (c * V) * (∫ t in (0 : ℝ)..U, |uIn t 1|) ≤ J)
    (hwidth : U * Real.exp (a * V) ≤ δ) (hsmall : L * N * δ / (ρ ^ 2 * (a - c)) ≤ 1 / 2) :
    let E := 2 * (H + L * (R / ρ) * J) / ρ
    (∀ u v, |x.2.1 u v 1| ≤ E * Real.exp (-c * v)) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        |x.2.2 u v 1| ≤ (R / ρ) * |uIn u 1| + (N / (ρ * (a - c))) * E * Real.exp ((a - c) * v) := by
  let α := R / ρ
  let β := N / (ρ * (a - c))
  let E := 2 * (H + L * α * J) / ρ
  let weight : C(Icc 0 V, ℝ) := ⟨fun v => Real.exp (c * v),
    Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)⟩
  let W := ContinuousMap.const (Icc 0 U) weight * waveCoordinateField 1 x.2.1
  let S := ‖W‖
  have hα : 0 ≤ α := div_nonneg hR hρ.le
  have hβ : 0 ≤ β := div_nonneg hN (mul_nonneg hρ.le (sub_pos.2 hac).le)
  have hS : 0 ≤ S := norm_nonneg W
  have hw (u : Icc 0 U) (v : Icc 0 V) : |x.2.1 u v 1| ≤ S * Real.exp (-c * v) := by
    have hb := ((W u).norm_coe_le_norm v).trans (W.norm_coe_le_norm u)
    change ‖Real.exp (c * v) * x.2.1 u v 1‖ ≤ S at hb
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] at hb
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hb)
  have htrans : ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      |x.2.2 t v 1| ≤ α * |uIn t 1| + β * S * Real.exp ((a - c) * v) := by
    filter_upwards [hx.zeta_transport hr hinu] with t ht
    intro v
    let u := projIcc 0 U hU t
    have hrp := hρ.trans_le (hlo u v)
    have hb : ρ * |x.2.2 t v 1| ≤ R * |uIn t 1| + N * S / (a - c) * Real.exp ((a - c) * v) := by
      calc
        _ ≤ x.1 u v 0 * |x.2.2 t v 1| := mul_le_mul_of_nonneg_right (hlo u v) (abs_nonneg _)
        _ = |x.1 u v 0 * x.2.2 t v 1| := by rw [abs_mul, abs_of_pos hrp]
        _ ≤ _ := by
          rw [ht v]
          exact (abs_add_le _ _).trans (add_le_add
            (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hin u) (abs_nonneg _))
            (scalarTransportCorrection_weighted_bound hac hN hS _ _ hν hw u v))
    apply (le_div_iff₀ hρ).2 (by simpa only [mul_comm ρ] using hb) |>.trans_eq ?_
    dsimp only [α, β]
    field_simp
  have hfi : IntervalIntegrable (fun t => uIn t 1) volume 0 U := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    exact (ContinuousLinearMap.proj (1 : Fin 3) : WaveVector →L[ℝ] ℝ).integrable_comp
      ((Lp.memLp uIn).integrable (by norm_num))
  have hB : S ≤ (H + L * α * J + L * β * δ * S) / ρ := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro u
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro v
    have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
      rw [uIcc_of_le u.property.1, uIcc_of_le hU]
      exact Icc_subset_Icc le_rfl u.property.2
    have hfu := hfi.abs.mono_set hsub
    have hioc : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
    have hb : |∫ t in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1| ≤
        L * (α * (∫ t in (0 : ℝ)..u, |uIn t 1|) + β * S * Real.exp ((a - c) * v) * u) := by
      have hd : ∀ᵐ t ∂volume, t ∈ Ioc (0 : ℝ) u →
          ‖-x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1‖ ≤ L * (α * |uIn t 1| + β * S * Real.exp ((a - c) * v)) := by
        apply (ae_restrict_iff' measurableSet_Ioc).1
        filter_upwards [ae_mono (Measure.restrict_mono hioc le_rfl) htrans] with t ht
        rw [Real.norm_eq_abs, abs_mul, abs_neg]
        exact mul_le_mul (hlam _ v) (ht v) (abs_nonneg _) hL
      have hi := intervalIntegral.norm_integral_le_of_norm_le u.property.1 hd
        (((hfu.const_mul α).add intervalIntegrable_const).const_mul L)
      simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hfu.const_mul α) intervalIntegrable_const,
        intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm (u : ℝ), mul_assoc] using hi
    have hj : Real.exp (c * v) * (∫ t in (0 : ℝ)..u, |uIn t 1|) ≤ J := by
      have hi := intervalIntegral.integral_mono_interval le_rfl u.property.1 u.property.2
        (Filter.Eventually.of_forall (fun t => abs_nonneg (uIn t 1))) hfi.abs
      exact (mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 hc)) hi
        (intervalIntegral.integral_nonneg u.property.1 (fun _ _ => abs_nonneg _)) (Real.exp_pos _).le).trans hinput
    have huδ : (u : ℝ) * Real.exp (a * v) ≤ δ :=
      (mul_le_mul u.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 (hc.trans hac.le)))
        (Real.exp_pos _).le hU).trans hwidth
    have he : Real.exp (c * v) * Real.exp ((a - c) * v) = Real.exp (a * v) := by
      rw [← Real.exp_add]; congr 1; ring
    have ht : |x.1 u v 0 * x.2.1 u v 1| ≤
        |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
          L * (α * (∫ t in (0 : ℝ)..u, |uIn t 1|) + β * S * Real.exp ((a - c) * v) * u) := by
      rw [hx.theta_integral hzin u v]
      exact (abs_add_le _ _).trans (add_le_add_right hb _)
    have hh := mul_le_mul_of_nonneg_left ht (Real.exp_pos (c * v)).le
    have hj' := mul_le_mul_of_nonneg_left hj (mul_nonneg hL hα)
    have hu' := mul_le_mul_of_nonneg_left huδ (mul_nonneg (mul_nonneg hL hβ) hS)
    have hr' := mul_le_mul_of_nonneg_right (hlo u v) (mul_nonneg (Real.exp_pos (c * v)).le (abs_nonneg (x.2.1 u v 1)))
    rw [abs_mul, abs_of_pos (hρ.trans_le (hlo u v))] at hh
    have hh' : Real.exp (c * v) * (x.1 u v 0 * |x.2.1 u v 1|) ≤
        Real.exp (c * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
        L * α * (Real.exp (c * v) * ∫ t in (0 : ℝ)..u, |uIn t 1|) +
        L * β * S * ((u : ℝ) * Real.exp (a * v)) := by
      apply hh.trans_eq
      rw [← he]
      ring
    have hb' : ρ * (Real.exp (c * v) * |x.2.1 u v 1|) ≤ H + L * α * J + L * β * δ * S := by
      nlinarith only [hh', hj', hu', hr', hout v]
    change ‖Real.exp (c * v) * x.2.1 u v 1‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (le_div_iff₀ hρ).2 (by simpa only [mul_comm ρ] using hb')
  have hSE : S ≤ E := by
    have hcoef : L * β * δ / ρ ≤ 1 / 2 := by
      have he : L * β * δ / ρ = L * N * δ / (ρ ^ 2 * (a - c)) := by dsimp only [β]; field_simp
      rwa [he]
    have hb' : S ≤ (H + L * α * J) / ρ + (L * β * δ / ρ) * S := by
      convert hB using 1
      ring
    have hs := mul_le_mul_of_nonneg_right hcoef hS
    have hle : S ≤ 2 * ((H + L * α * J) / ρ) := by linarith only [hb', hs]
    exact hle.trans_eq (by dsimp only [E]; ring)
  refine ⟨fun u v => (hw u v).trans (mul_le_mul_of_nonneg_right hSE (Real.exp_pos _).le), ?_⟩
  filter_upwards [htrans] with t ht
  intro v
  exact (ht v).trans (add_le_add_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSE hβ) (Real.exp_pos _).le) _)

end CauchyHorizon
