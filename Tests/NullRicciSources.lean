import CauchyHorizon.Reduced.NullRicciSources

open MeasureTheory Set
open scoped Distributions

namespace CauchyHorizon.Tests

-- The section-to-distribution step needs only L1 of the derivative.
example {U V A B : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) {F g : ℝ → ℝ}
    (hF : IntegrableOn F (Icc 0 U)) (hg : IntegrableOn g (Icc 0 U))
    (hAC : AbsolutelyContinuousOnInterval F 0 U)
    (hd : ∀ᵐ u ∂volume.restrict (Icc 0 U), HasDerivWithinAt F (g u) (Icc 0 U) u) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((1, 0), (0, 0))
      (rectangleProductDistribution U V A B (fun w => F w.1.1)) =
        rectangleProductDistribution U V A B (fun w => g w.1.1) := by
  have hFi : IntegrableOn (fun w : ℝ × ℝ => F w.1) (Icc 0 U ×ˢ Icc 0 V) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hF.comp_fst (volume.restrict (Icc 0 V))
  have hgi : IntegrableOn (fun w : ℝ × ℝ => g w.1) (Icc 0 U ×ˢ Icc 0 V) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hg.comp_fst (volume.restrict (Icc 0 V))
  exact (null_derivatives_of_sections (A := A) (B := B) hU hV hFi
    (f₂ := fun _ => 0) (g₂ := fun _ => 0) (by simp) hgi (by simp)
    (Filter.Eventually.of_forall fun _ => hAC) (Filter.Eventually.of_forall fun _ => hd)
    (Filter.Eventually.of_forall fun _ =>
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ))).contDiffOn.absolutelyContinuousOnInterval)
    (Filter.Eventually.of_forall fun _ =>
      Filter.Eventually.of_forall fun v => (hasDerivAt_const v (0 : ℝ)).hasDerivWithinAt)).1

section ActualSolution

variable {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
  (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
  (n : C(Icc 0 U, ℝ))
  (hn : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = n (projIcc 0 U hU u))
  (hnAC : AbsolutelyContinuousOnInterval (intervalExtension hU n) 0 U)
  (hnd : ∀ᵐ u ∂volume.restrict (Icc 0 U), HasDerivWithinAt (intervalExtension hU n)
    (uIn u 2 * n (projIcc 0 U hU u) - zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2) (Icc 0 U) u)
  (hout : ∀ v (hv : v ∈ Icc 0 V), HasDerivWithinAt (fun t => intervalExtension hV vOut t 0)
    (vOut ⟨v, hv⟩ 2 * vOut ⟨v, hv⟩ 0 -
      x.1 ⟨0, le_rfl, hU⟩ ⟨v, hv⟩ 0 * (vOut ⟨v, hv⟩ 1) ^ 2) (Icc 0 V) v)
  (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi)

-- The source is the actual rough scalar derivative squared, with coefficient two.
example :
    let source := fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      2 * (x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 1) ^ 2
    Integrable source (rectangleProductMeasure U V A B) ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 0 0 =
        rectangleProductDistribution U V A B source :=
  hx.null_ricci_sources hzin n hn hnAC hnd hout A B θ hA hB hθ hθA 0

-- The outgoing source uses p on the same original solution.
example :
    let source := fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      2 * (x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 1) ^ 2
    Integrable source (rectangleProductMeasure U V A B) ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 1 1 =
        rectangleProductDistribution U V A B source :=
  hx.null_ricci_sources hzin n hn hnAC hnd hout A B θ hA hB hθ hθA 1

end ActualSolution

end CauchyHorizon.Tests
