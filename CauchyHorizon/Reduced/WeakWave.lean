import CauchyHorizon.Reduced.LongitudinalFlux
import CauchyHorizon.Reduced.SourceIntegrability
import CauchyHorizon.Analysis.WeakDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The integral solution satisfies the wave equations against general two-variable tests. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

structure WaveTest (U V : ℝ) where
  val : ℝ → ℝ → ℝ
  du : ℝ → ℝ → ℝ
  duv : ℝ → ℝ → ℝ
  continuous_val : Continuous val.uncurry
  continuous_du : Continuous du.uncurry
  continuous_duv : Continuous duv.uncurry
  smooth_u : ∀ v, ContDiff ℝ 1 (fun u => val u v)
  deriv_u : ∀ u v, HasDerivAt (fun t => val t v) (du u v) u
  deriv_du_v : ∀ u v, HasDerivAt (du u) (duv u v) v
  boundary_u : ∀ v, val 0 v = 0 ∧ val U v = 0
  boundary_du_v : ∀ u, du u 0 = 0 ∧ du u V = 0

def HasWeakWaveEquation {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (x : WaveState U V) : Prop :=
  let z := fun u v => x.1 (projIcc 0 U hU u) (projIcc 0 V hV v)
  let p := fun u v => x.2.1 (projIcc 0 U hU u) (projIcc 0 V hV v)
  let q := fun u v => x.2.2 u (projIcc 0 V hV v)
  ∀ ψ : WaveTest U V, ∀ i : Fin 3,
    IntegrableOn (fun w : ℝ × ℝ => waveSource e Λ (z w.1 w.2) (q w.1 w.2) (p w.1 w.2) i *
      ψ.val w.1 w.2) (Icc 0 U ×ˢ Icc 0 V) ∧
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, waveSource e Λ (z u v) (q u v) (p u v) i * ψ.val u v) =
      ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, z u v i * ψ.duv u v

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.weak_wave_equation {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) :
    HasWeakWaveEquation hU hV e Λ x := by
  intro ψ i
  let z := fun u v => x.1 (projIcc 0 U hU u) (projIcc 0 V hV v) i
  let p := fun u v => x.2.1 (projIcc 0 U hU u) (projIcc 0 V hV v) i
  let S := fun u v => waveSource e Λ
    (x.1 (projIcc 0 U hU u) (projIcc 0 V hV v))
    (x.2.2 u (projIcc 0 V hV v)) (x.2.1 (projIcc 0 U hU u) (projIcc 0 V hV v)) i
  have hSi : IntegrableOn (fun w : ℝ × ℝ => S w.1 w.2 * ψ.val w.1 w.2) (Icc 0 U ×ˢ Icc 0 V) :=
    (wave_source_integrable hU hV e Λ x hx.choose i).mul_continuousOn
      ψ.continuous_val.continuousOn (isCompact_Icc.prod isCompact_Icc)
  refine ⟨hSi, ?_⟩
  have hfirst (v : ℝ) : (∫ u in (0 : ℝ)..U, S u v * ψ.val u v) =
      -(∫ u in (0 : ℝ)..U, p u v * ψ.du u v) := by
    let E : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ (projIcc 0 V hV v))
    have hAC : AbsolutelyContinuousOnInterval (fun u => p u v) 0 U :=
      absolutelyContinuous_comp_contDiffAt (g := E) hx.velocity_horizontal_absolutelyContinuous
        (fun _ _ => E.contDiff.contDiffAt)
    have hd : ∀ᵐ u ∂volume.restrict (Icc 0 U),
        HasDerivWithinAt (fun t => p t v) (S u v) (Icc 0 U) u := by
      filter_upwards [hx.wave_equation] with u hu
      exact (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u
        (hu (projIcc 0 V hV v))
    exact (integral_weak_derivative hU hAC hd (ψ.smooth_u v)
      (fun u _ => (ψ.deriv_u u v).hasDerivWithinAt) (ψ.boundary_u v).1 (ψ.boundary_u v).2).2
  have hpcont : Continuous (fun w : ℝ × ℝ => p w.1 w.2 * ψ.du w.1 w.2) :=
    (by dsimp only [p]; fun_prop : Continuous (fun w : ℝ × ℝ => p w.1 w.2)).mul ψ.continuous_du
  have hsecond (u : ℝ) : (∫ v in (0 : ℝ)..V, p u v * ψ.du u v) =
      -(∫ v in (0 : ℝ)..V, z u v * ψ.duv u v) := by
    have hz (v : ℝ) (hv : v ∈ uIcc 0 V) :
        HasDerivWithinAt (z u) (p u v) (uIcc 0 V) v := by
      rw [uIcc_of_le hV] at hv ⊢
      have hh := (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt v
        (hx.longitudinal_derivative (projIcc 0 U hU u) hv)
      change HasDerivWithinAt (z u) (x.2.1 (projIcc 0 U hU u) ⟨v, hv⟩ i) (Icc 0 V) v at hh
      simpa only [p, projIcc_of_mem hV hv] using hh
    have hd (v : ℝ) (_hv : v ∈ uIcc 0 V) :
        HasDerivWithinAt (ψ.du u) (ψ.duv u v) (uIcc 0 V) v :=
      (ψ.deriv_du_v u v).hasDerivWithinAt
    have hi := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt hz hd
      ((by dsimp only [p]; fun_prop : Continuous (p u)).intervalIntegrable (0 : ℝ) V)
      ((ψ.continuous_duv.comp (continuous_const.prodMk continuous_id)).intervalIntegrable (0 : ℝ) V)
    have hpi : IntervalIntegrable (fun v => p u v * ψ.du u v) volume 0 V :=
      (hpcont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hzi : IntervalIntegrable (fun v => z u v * ψ.duv u v) volume 0 V :=
      ((by dsimp only [z]; fun_prop : Continuous (z u)).mul
        (ψ.continuous_duv.comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hpi hzi, (ψ.boundary_du_v u).1, (ψ.boundary_du_v u).2,
      mul_zero, mul_zero, sub_self] at hi
    linarith only [hi]
  have hs : uIoc (0 : ℝ) U ×ˢ uIoc (0 : ℝ) V ⊆ Icc 0 U ×ˢ Icc 0 V := by
    rw [uIoc_of_le hU, uIoc_of_le hV]
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hpint : IntegrableOn (fun w : ℝ × ℝ => p w.1 w.2 * ψ.du w.1 w.2)
      (uIoc 0 U ×ˢ uIoc 0 V) :=
    (hpcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set hs
  change (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, S u v * ψ.val u v) = _
  rw [intervalIntegral_intervalIntegral_swap (F := fun u v => S u v * ψ.val u v) (hSi.mono_set hs)]
  simp_rw [hfirst]
  rw [intervalIntegral.integral_neg,
    ← intervalIntegral_intervalIntegral_swap (F := fun u v => p u v * ψ.du u v) hpint]
  simp_rw [hsecond]
  rw [intervalIntegral.integral_neg, neg_neg]

end CauchyHorizon
