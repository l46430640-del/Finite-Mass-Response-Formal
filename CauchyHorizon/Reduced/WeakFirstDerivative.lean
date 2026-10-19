import CauchyHorizon.Reduced.DistributionWave
import CauchyHorizon.Reduced.WeakComposition

/-! The actual field and its two first distributional derivatives are square integrable. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

def HasL2WaveDerivatives {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V) : Prop :=
  let z := fun i (w : ℝ × ℝ) => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) i
  let p := fun i (w : ℝ × ℝ) => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) i
  let q := fun i (w : ℝ × ℝ) => x.2.2 w.1 (projIcc 0 V hV w.2) i
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  ∀ i : Fin 3, MemLp (z i) 2 μ ∧ MemLp (p i) 2 μ ∧ MemLp (q i) 2 μ ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1, 0) (rectangleDistribution U V (z i)) =
      rectangleDistribution U V (q i) ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, 1) (rectangleDistribution U V (z i)) =
      rectangleDistribution U V (p i)

theorem IsWaveIntegral.weak_first_derivatives {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasL2WaveDerivatives hU hV x := by
  intro i
  let E : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hh := hx.weak_composition hzin E (fun _ _ => E.contDiff.contDiffAt)
  simp only [HasL2FirstDerivatives, ContinuousLinearMap.fderiv] at hh
  exact ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2⟩

end CauchyHorizon
