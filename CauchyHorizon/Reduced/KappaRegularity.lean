import CauchyHorizon.Reduced.ConstraintIntegral

/-! Horizontal kappa regularity from the nonvanishing weighted radial derivative. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.kappa_horizontal_regular {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v ≠ 0) (v : Icc 0 V) :
    let N := fun t => intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v
    let κ := fun t => -Real.exp (intervalExtension hU x.1 t v 2) / (4 * N t)
    AbsolutelyContinuousOnInterval κ 0 U ∧
      ∀ᵐ t ∂volume.restrict (Icc 0 U), HasDerivWithinAt κ
        (κ t * intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 / N t) (Icc 0 U) t := by
  let N := fun t => intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v
  let E := fun t => intervalExtension hU x.1 t v 2
  let Q := fun t => N t * Real.exp (-E t)
  let κ := fun t => -Real.exp (E t) / (4 * N t)
  let G : ℝ → ℝ := fun q => -1 / (4 * q)
  have hn (t : ℝ) : N t ≠ 0 := hnu (projIcc 0 U hU t) v
  have hQ (t : ℝ) : Q t ≠ 0 := mul_ne_zero (hn t) (Real.exp_ne_zero _)
  have hG : ∀ q ∈ Q '' uIcc (0 : ℝ) U, ContDiffAt ℝ 1 G q := by
    rintro q ⟨t, _ht, rfl⟩
    exact contDiffAt_const.div (contDiffAt_const.mul contDiffAt_id) (mul_ne_zero (by norm_num) (hQ t))
  have he : G ∘ Q = κ := by
    funext t
    dsimp only [G, Q, κ, Function.comp_apply]
    rw [Real.exp_neg]
    field_simp [hn t, Real.exp_ne_zero]
  have hAC : AbsolutelyContinuousOnInterval κ 0 U := by
    rw [← he]
    exact absolutelyContinuous_comp_contDiffAt (hx.weightedNu_absolutelyContinuous hr hzin v) hG
  refine ⟨hAC, ?_⟩
  filter_upwards [hx.transverse_constraint hr hzin hinu hinell, hx.horizontal_derivative hzin] with t hdN hdZ
  let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  have hdE := T.hasFDerivAt.comp_hasDerivWithinAt t hdZ
  have hd := hdE.exp.neg.div ((hdN v).const_mul 4) (mul_ne_zero (by norm_num) (hn t))
  apply hd.congr_deriv
  change ((-(Real.exp (E t) * x.2.2 t v 2)) * (4 * N t) -
      (-Real.exp (E t)) * (4 * (x.2.2 t v 2 * N t -
        intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2))) / (4 * N t) ^ 2 =
    (-Real.exp (E t) / (4 * N t)) * intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 / N t
  field_simp [hn t]
  ring

end CauchyHorizon
