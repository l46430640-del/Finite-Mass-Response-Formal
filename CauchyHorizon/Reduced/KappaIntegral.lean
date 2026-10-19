import CauchyHorizon.Reduced.ConstraintIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The logarithmic incoming constraint at the actual mixed regularity. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.kappa_exponential {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v < 0)
    (haxis : ∀ v, Real.exp (x.1 ⟨0, le_rfl, hU⟩ v 2) =
      -4 * radialNuField hV e Λ zIn x.1 hr ⟨0, le_rfl, hU⟩ v)
    (v : Icc 0 V) :
    let N := radialNuField hV e Λ zIn x.1 hr
    let S := fun t => intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU N t v)
    IntervalIntegrable S volume 0 U ∧ ∀ u : Icc 0 U,
      -Real.exp (x.1 u v 2) / (4 * N u v) = Real.exp (-(∫ t in (0 : ℝ)..u, S t)) := by
  let N := radialNuField hV e Λ zIn x.1 hr
  let S : ℝ → ℝ := fun t => intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
    (-intervalExtension hU N t v)
  let L : ℝ → ℝ := fun t => Real.log (-intervalExtension hU N t v) - intervalExtension hU x.1 t v 2
  let G : C(Icc 0 V, WaveVector) → ℝ := fun z => Real.log (-radialNuOperator hV e Λ z v) - z v 2
  have hG : ∀ z ∈ (intervalExtension hU x.1) '' uIcc (0 : ℝ) U, ContDiffAt ℝ 1 G z := by
    rintro z ⟨t, _ht, rfl⟩
    have hN := (ContinuousMap.evalCLM ℝ v : C(Icc 0 V, ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp _
      (radialNuOperator_contDiffAt hV e Λ _ (hr (projIcc 0 U hU t)))
    have hn : -radialNuOperator hV e Λ (intervalExtension hU x.1 t) v ≠ 0 := by
      change -radialNuOperator hV e Λ (x.1 (projIcc 0 U hU t)) v ≠ 0
      rw [hx.radialNu_operator hr]
      exact neg_ne_zero.2 (ne_of_lt (hnu _ v))
    let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
    exact (hN.neg.log hn).sub T.contDiff.contDiffAt
  have hLG : G ∘ intervalExtension hU x.1 = L := by
    funext t
    change Real.log (-radialNuOperator hV e Λ (x.1 (projIcc 0 U hU t)) v) - _ = _
    rw [hx.radialNu_operator hr]
    rfl
  have hc : AbsolutelyContinuousOnInterval L 0 U :=
    hLG ▸ absolutelyContinuous_comp_contDiffAt (hx.horizontal_absolutelyContinuous hzin) hG
  have he : deriv L =ᵐ[volume.restrict (Icc 0 U)] S := by
    filter_upwards [hx.transverse_constraint hr hzin hinu hinell, hx.horizontal_derivative hzin,
      ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc 0 U)).ae_ne 0,
      (volume.restrict (Icc 0 U)).ae_ne U] with t hn hz ht ht0 htU
    let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
    have hl := T.hasFDerivAt.comp_hasDerivWithinAt t hz
    have hnn : intervalExtension hU N t v ≠ 0 := ne_of_lt (hnu _ v)
    have hh := ((hn v).neg.log (neg_ne_zero.2 hnn)).sub hl
    have hd : HasDerivWithinAt L (S t) (Icc 0 U) t := by
      apply hh.congr_deriv
      change -(x.2.2 t v 2 * N (projIcc 0 U hU t) v -
        x.1 (projIcc 0 U hU t) v 0 * (x.2.2 t v 1) ^ 2) /
        (-intervalExtension hU N t v) - x.2.2 t v 2 = S t
      dsimp only [S, intervalExtension_apply] at hnn ⊢
      field_simp [hnn]
      ring
    exact (hd.hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne ht.1 ht0.symm)
      (lt_of_le_of_ne ht.2 htU))).deriv
  have hs : uIoc (0 : ℝ) U ⊆ Icc 0 U := by rw [uIoc_of_le hU]; exact Ioc_subset_Icc_self
  refine ⟨hc.intervalIntegrable_deriv.congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) he), ?_⟩
  intro u
  have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le u.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl u.property.2
  have hp := (hc.mono hsub).integral_deriv_eq_sub
  have hs' : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
  rw [intervalIntegral.integral_of_le u.property.1,
    integral_congr_ae (ae_mono (Measure.restrict_mono hs' le_rfl) he),
    ← intervalIntegral.integral_of_le u.property.1] at hp
  have hlog : Real.log (-N u v) - x.1 u v 2 =
      Real.log (-N ⟨0, le_rfl, hU⟩ v) - x.1 ⟨0, le_rfl, hU⟩ v 2 + ∫ t in (0 : ℝ)..u, S t := by
    simp only [L, intervalExtension_apply, projIcc_of_mem hU u.property,
      projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩)] at hp
    linarith only [hp]
  have hexp := congrArg Real.exp hlog
  rw [Real.exp_add, Real.exp_sub, Real.exp_sub,
    Real.exp_log (neg_pos.2 (hnu u v)), Real.exp_log (neg_pos.2 (hnu ⟨0, le_rfl, hU⟩ v)), haxis v] at hexp
  have hn0 : N ⟨0, le_rfl, hU⟩ v ≠ 0 := ne_of_lt (hnu _ v)
  have hn : N u v ≠ 0 := ne_of_lt (hnu _ v)
  have hnorm : (-N ⟨0, le_rfl, hU⟩ v) / (-4 * N ⟨0, le_rfl, hU⟩ v) = 1 / 4 := by
    field_simp [hn0]
  change (-N u v) / Real.exp (x.1 u v 2) = _ at hexp
  rw [hnorm] at hexp
  change -Real.exp (x.1 u v 2) / (4 * N u v) = Real.exp (-(∫ t in (0 : ℝ)..u, S t))
  rw [Real.exp_neg]
  field_simp [hn, Real.exp_ne_zero] at hexp ⊢
  nlinarith only [hexp]

end CauchyHorizon
