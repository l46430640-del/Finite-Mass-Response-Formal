import CauchyHorizon.Reduced.WeakComposition
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! The positive metric coefficients and their actual square-integrable weak derivatives. -/

open MeasureTheory Set

namespace CauchyHorizon

def HasL2MetricCoefficients {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) : Prop :=
  let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let p := fun w : ℝ × ℝ => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let q := fun w : ℝ × ℝ => x.2.2 w.1 (projIcc 0 V hV w.2)
  let H := fun w => Real.exp (z w 2)
  let R := fun w => (z w 0) ^ 2
  Continuous H ∧ Continuous R ∧ (∀ w, 0 < H w ∧ 0 < R w) ∧
    HasL2FirstDerivatives U V H (fun w => H w * q w 2) (fun w => H w * p w 2) ∧
    HasL2FirstDerivatives U V R (fun w => 2 * z w 0 * q w 0) (fun w => 2 * z w 0 * p w 0)

theorem IsWaveIntegral.metric_coefficients {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasL2MetricCoefficients hU hV x := by
  let E : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj 2
  let R : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hH := hx.weak_composition hzin (fun z => Real.exp (E z))
    (fun _ _ => (E.contDiff.exp).contDiffAt)
  have hR := hx.weak_composition hzin (fun z => (R z) ^ 2)
    (fun _ _ => (R.contDiff.pow 2).contDiffAt)
  have hdH (z : WaveVector) : fderiv ℝ (fun z => Real.exp (E z)) z = Real.exp (E z) • E :=
    E.hasFDerivAt.exp.fderiv
  have hdR (z : WaveVector) : fderiv ℝ (fun z => (R z) ^ 2) z = (2 * R z) • R := by
    simpa only [Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat] using
      (R.hasFDerivAt.pow 2).fderiv (x := z)
  simp only [hdH, smul_apply, smul_eq_mul] at hH
  simp only [hdR, smul_apply, smul_eq_mul] at hR
  refine ⟨by fun_prop, by fun_prop, ?_, hH, hR⟩
  intro w
  exact ⟨Real.exp_pos _, sq_pos_of_ne_zero (hx.choose _ _)⟩

end CauchyHorizon
