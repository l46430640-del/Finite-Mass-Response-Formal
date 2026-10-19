import CauchyHorizon.Analysis.ProductWeakDerivative

/-! Ricci distributions use derivatives of L1 connection coefficients and L1 quadratic terms. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

noncomputable def ricciTrace {ι : Type*} [Fintype ι] (Γ : ι → ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ k, Γ k i k

noncomputable def ricciQuadratic {ι : Type*} [Fintype ι] (Γ : ι → ι → ι → ℝ) (i j : ι) : ℝ :=
  ∑ k, ∑ l, (Γ k k l * Γ l i j - Γ k j l * Γ l i k)

noncomputable def ricciDistribution (U V A B : ℝ)
    (Γ : (ℝ × ℝ) × (ℝ × ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ) (i j : Fin 4) :
    𝓓'(openRectangleProduct U V A B, ℝ) :=
  (∑ k, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate k)
    (rectangleProductDistribution U V A B (fun w => Γ w k i j))) -
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate j)
      (rectangleProductDistribution U V A B (fun w => ricciTrace (Γ w) i)) +
    rectangleProductDistribution U V A B (fun w => ricciQuadratic (Γ w) i j)

def HasRicciPairing (U V A B : ℝ)
    (Γ : (ℝ × ℝ) × (ℝ × ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ i j, Integrable (fun w => ricciQuadratic (Γ w) i j) (rectangleProductMeasure U V A B)) ∧
    ∀ i j (ψ : 𝓓(openRectangleProduct U V A B, ℝ)),
      let dψ : Fin 4 → 𝓓(openRectangleProduct U V A B, ℝ) :=
        fun k => TestFunction.lineDerivCLM ℝ (productCoordinate k) ψ
      (∀ k, Integrable (fun w => Γ w k i j * dψ k w) (rectangleProductMeasure U V A B)) ∧
      Integrable (fun w => ricciTrace (Γ w) i * dψ j w) (rectangleProductMeasure U V A B) ∧
      Integrable (fun w => ricciQuadratic (Γ w) i j * ψ w) (rectangleProductMeasure U V A B) ∧
      ricciDistribution U V A B Γ i j ψ =
        (∑ k, -(∫ w, Γ w k i j * dψ k w ∂rectangleProductMeasure U V A B)) +
        (∫ w, ricciTrace (Γ w) i * dψ j w ∂rectangleProductMeasure U V A B) +
        ∫ w, ricciQuadratic (Γ w) i j * ψ w ∂rectangleProductMeasure U V A B

theorem ricci_distribution_pairing {U V A B : ℝ}
    {Γ : (ℝ × ℝ) × (ℝ × ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ}
    (hΓ : ∀ k i j, Integrable (fun w => Γ w k i j) (rectangleProductMeasure U V A B))
    (hprod : ∀ k i j l m n, Integrable (fun w => Γ w k i j * Γ w l m n)
      (rectangleProductMeasure U V A B)) : HasRicciPairing U V A B Γ := by
  have htrace (i : Fin 4) : Integrable (fun w => ricciTrace (Γ w) i)
      (rectangleProductMeasure U V A B) :=
    integrable_finsetSum Finset.univ fun k _ => hΓ k i k
  have hQ (i j : Fin 4) : Integrable (fun w => ricciQuadratic (Γ w) i j)
      (rectangleProductMeasure U V A B) :=
    integrable_finsetSum Finset.univ fun k _ => integrable_finsetSum Finset.univ fun l _ =>
      (hprod k k l l i j).sub (hprod k j l l i k)
  have htest {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ}
      (hf : Integrable f (rectangleProductMeasure U V A B))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      Integrable (fun w => f w * ψ w) (rectangleProductMeasure U V A B) := by
    obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
    exact hf.mul_bdd ψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hpair {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ}
      (hf : Integrable f (rectangleProductMeasure U V A B))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B f ψ =
        ∫ w, f w * ψ w ∂rectangleProductMeasure U V A B := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ)
      (rectangleProductMeasure U V A B) f ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  refine ⟨hQ, ?_⟩
  intro i j ψ
  refine ⟨fun k => htest (hΓ k i j) _, htest (htrace i) _, htest (hQ i j) ψ, ?_⟩
  simp only [ricciDistribution, add_apply, sub_apply, sum_apply, Distribution.lineDerivCLM_apply]
  simp_rw [hpair (hΓ _ _ _), hpair (htrace _), hpair (hQ _ _)]
  ring

end CauchyHorizon
