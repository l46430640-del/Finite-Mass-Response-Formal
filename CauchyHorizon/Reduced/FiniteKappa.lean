import CauchyHorizon.Reduced.KappaIntegral

/-! Finite-time lower bounds for the normalized lapse and conformal factor. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.finite_kappa_bound {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2)
    {R n J : ℝ} (hR : 0 ≤ R) (hn : 0 < n)
    (hrhi : ∀ u v, x.1 u v 0 ≤ R)
    (hnlo : ∀ u v, n ≤ -radialNuField hV e Λ zIn x.1 hr u v)
    (haxis : ∀ v, Real.exp (x.1 ⟨0, le_rfl, hU⟩ v 2) =
      -4 * radialNuField hV e Λ zIn x.1 hr ⟨0, le_rfl, hU⟩ v)
    (hscalar : ∀ v, (∫ t in (0 : ℝ)..U, (x.2.2 t v 1) ^ 2) ≤ J)
    (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ zIn x.1 hr
    Real.exp (-(R / n * J)) ≤ -Real.exp (x.1 u v 2) / (4 * N u v) ∧
      4 * n * Real.exp (-(R / n * J)) ≤ Real.exp (x.1 u v 2) := by
  let N := radialNuField hV e Λ zIn x.1 hr
  let S : ℝ → ℝ := fun t => intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
    (-intervalExtension hU N t v)
  have hnu (a : Icc 0 U) (b : Icc 0 V) : N a b < 0 := neg_pos.1 (hn.trans_le (hnlo a b))
  obtain ⟨hi, hk⟩ := hx.kappa_exponential hr hzin hinu hinell hnu haxis v
  let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (1 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  have hf : MemLp (fun t => x.2.2 t v 1) 2 (volume.restrict (Icc 0 U)) :=
    T.comp_memLp' (Lp.memLp x.2.2)
  have hfi : IntervalIntegrable (fun t => (x.2.2 t v 1) ^ 2) volume 0 U := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    change Integrable (fun t => (x.2.2 t v 1) ^ 2) (volume.restrict (Icc 0 U))
    simpa only [pow_two] using (hf.mul' hf (r := 1)).integrable le_rfl
  have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le u.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl u.property.2
  have hI : (∫ t in (0 : ℝ)..u, S t) ≤ R / n * J := by
    have hb : ∀ t : ℝ, S t ≤ (R / n) * (x.2.2 t v 1) ^ 2 := by
      intro t
      have hnp : 0 < -N (projIcc 0 U hU t) v := neg_pos.2 (hnu _ v)
      have hratio := (div_le_div_of_nonneg_right (hrhi (projIcc 0 U hU t) v) hnp.le).trans
        (div_le_div_of_nonneg_left hR hn (hnlo (projIcc 0 U hU t) v))
      calc
        S t = (x.1 (projIcc 0 U hU t) v 0 / (-N (projIcc 0 U hU t) v)) * (x.2.2 t v 1) ^ 2 := by
          dsimp only [S, intervalExtension_apply]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
    have hh := intervalIntegral.integral_mono_on u.property.1 (hi.mono_set hsub)
      ((hfi.const_mul (R / n)).mono_set hsub) (fun t _ => hb t)
    rw [intervalIntegral.integral_const_mul] at hh
    have hsmall := (intervalIntegral.integral_mono_interval le_rfl u.property.1 u.property.2
      (Filter.Eventually.of_forall (fun t => sq_nonneg (x.2.2 t v 1))) hfi).trans (hscalar v)
    exact hh.trans (mul_le_mul_of_nonneg_left hsmall (div_nonneg hR hn.le))
  have hκ : Real.exp (-(R / n * J)) ≤ -Real.exp (x.1 u v 2) / (4 * N u v) := by
    rw [hk u]
    exact Real.exp_le_exp.2 (neg_le_neg hI)
  refine ⟨hκ, ?_⟩
  have hmul := (le_div_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) (hnu u v))).1 hκ
  have hl := mul_le_mul_of_nonneg_right (hnlo u v) (Real.exp_pos (-(R / n * J))).le
  nlinarith only [hmul, hl]

end CauchyHorizon
