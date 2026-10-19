import CauchyHorizon.Reduced.DistributionTest

/-! The nonlinear wave equations hold as equalities of distributions on the open rectangle. -/

open MeasureTheory Set
open scoped Distributions

namespace CauchyHorizon

def HasDistributionalWaveEquation {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (x : WaveState U V) : Prop :=
  let z := fun i (w : ℝ × ℝ) => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) i
  let S := fun i (w : ℝ × ℝ) => waveSource e Λ
    (x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2))
    (x.2.2 w.1 (projIcc 0 V hV w.2))
    (x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)) i
  ∀ i : Fin 3, IntegrableOn (S i) (Icc 0 U ×ˢ Icc 0 V) ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1, 0)
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, 1) (rectangleDistribution U V (z i))) =
        rectangleDistribution U V (S i)

theorem IsWaveIntegral.distributional_wave_equation {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) :
    HasDistributionalWaveEquation hU hV e Λ x := by
  intro i
  let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) i
  let S := fun w : ℝ × ℝ => waveSource e Λ
    (x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2))
    (x.2.2 w.1 (projIcc 0 V hV w.2))
    (x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)) i
  have hz : IntegrableOn z (Icc 0 U ×ˢ Icc 0 V) :=
    (by dsimp only [z]; fun_prop : Continuous z).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hS : IntegrableOn S (Icc 0 U ×ˢ Icc 0 V) :=
    wave_source_integrable hU hV e Λ x hx.choose i
  refine ⟨hS, ?_⟩
  change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1, 0)
    (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, 1) (rectangleDistribution U V z)) =
      rectangleDistribution U V S
  ext ψ
  rw [Distribution.lineDerivCLM_apply, Distribution.lineDerivCLM_apply, neg_neg,
    rectangleDistribution_apply hU hV hz, rectangleDistribution_apply hU hV hS]
  exact (hx.weak_wave_equation (WaveTest.ofTestFunction ψ) i).2.symm

end CauchyHorizon
