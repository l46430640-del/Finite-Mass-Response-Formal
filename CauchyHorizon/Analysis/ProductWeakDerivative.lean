import CauchyHorizon.Analysis.RectangleWeakDerivative
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Products of two planar weak fields have the four expected weak derivatives. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

def openRectangleProduct (U V A B : ℝ) : TopologicalSpace.Opens ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ⟨(openRectangle U V : Set (ℝ × ℝ)) ×ˢ openRectangle A B,
    (openRectangle U V).isOpen.prod (openRectangle A B).isOpen⟩

noncomputable def rectangleProductMeasure (U V A B : ℝ) : Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (volume.restrict (Icc 0 U ×ˢ Icc 0 V)).prod (volume.restrict (Icc 0 A ×ˢ Icc 0 B))

noncomputable def rectangleProductDistribution (U V A B : ℝ)
    (f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ) : 𝓓'(openRectangleProduct U V A B, ℝ) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ)
    (rectangleProductMeasure U V A B) f

def productCoordinate : Fin 4 → (ℝ × ℝ) × (ℝ × ℝ) :=
  ![((1, 0), (0, 0)), ((0, 1), (0, 0)), ((0, 0), (1, 0)), ((0, 0), (0, 1))]

def HasL2ProductDerivatives (U V A B : ℝ) (f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ)
    (df : Fin 4 → (ℝ × ℝ) × (ℝ × ℝ) → ℝ) : Prop :=
  MemLp f 2 (rectangleProductMeasure U V A B) ∧ ∀ i,
    MemLp (df i) 2 (rectangleProductMeasure U V A B) ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate i)
      (rectangleProductDistribution U V A B f) = rectangleProductDistribution U V A B (df i)

noncomputable def rectangleTestSliceLeft {U V A B : ℝ}
    (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) (y : ℝ × ℝ) : 𝓓(openRectangle U V, ℝ) :=
  ⟨fun x => ψ (x, y), ψ.contDiff.comp (contDiff_id.prodMk contDiff_const),
    (ψ.hasCompactSupport.image continuous_fst).of_isClosed_subset (isClosed_tsupport _)
      (fun x hx => ⟨(x, y),
        tsupport_comp_subset_preimage (f := fun x => (x, y)) ψ (by fun_prop) hx, rfl⟩),
    fun _ hx => (ψ.tsupport_subset
      (tsupport_comp_subset_preimage (f := fun x => (x, y)) ψ (by fun_prop) hx)).1⟩

noncomputable def rectangleTestSliceRight {U V A B : ℝ}
    (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) (x : ℝ × ℝ) : 𝓓(openRectangle A B, ℝ) :=
  ⟨fun y => ψ (x, y), ψ.contDiff.comp (contDiff_const.prodMk contDiff_id),
    (ψ.hasCompactSupport.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
      (fun y hy => ⟨(x, y),
        tsupport_comp_subset_preimage (f := fun y => (x, y)) ψ (by fun_prop) hy, rfl⟩),
    fun _ hy => (ψ.tsupport_subset
      (tsupport_comp_subset_preimage (f := fun y => (x, y)) ψ (by fun_prop) hy)).2⟩

set_option maxHeartbeats 1500000 in
theorem l2_product_derivatives {U V A B : ℝ} {f f₁ f₂ g g₁ g₂ : ℝ × ℝ → ℝ}
    (hf : HasL2FirstDerivatives U V f f₁ f₂) (hg : HasL2FirstDerivatives A B g g₁ g₂) :
    HasL2ProductDerivatives U V A B (fun w => f w.1 * g w.2)
      ![fun w => f₁ w.1 * g w.2, fun w => f₂ w.1 * g w.2,
        fun w => f w.1 * g₁ w.2, fun w => f w.1 * g₂ w.2] := by
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  let ν := volume.restrict (Icc 0 A ×ˢ Icc 0 B)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hp {a b : ℝ × ℝ → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 ν) :
      MemLp (fun w : (ℝ × ℝ) × (ℝ × ℝ) => a w.1 * b w.2) 2 (μ.prod ν) := by
    apply (memLp_two_iff_integrable_sq (ha.1.comp_fst.mul hb.1.comp_snd)).2
    simpa only [Pi.mul_apply, mul_pow] using
      ((memLp_two_iff_integrable_sq ha.1).1 ha).mul_prod ((memLp_two_iff_integrable_sq hb.1).1 hb)
  have htest {a : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (ha : Integrable a (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) : Integrable (fun w => a w * ψ w) (μ.prod ν) := by
    obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
    exact ha.mul_bdd ψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hpair {a : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (ha : Integrable a (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B a ψ = ∫ w, a w * ψ w ∂(μ.prod ν) := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) (μ.prod ν) a ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (ha.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hpairL {a : ℝ × ℝ → ℝ} (ha : Integrable a μ) (ψ : 𝓓(openRectangle U V, ℝ)) :
      rectangleDistribution U V a ψ = ∫ x, a x * ψ x ∂μ := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ a ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (ha.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hpairR {b : ℝ × ℝ → ℝ} (hb : Integrable b ν) (ψ : 𝓓(openRectangle A B, ℝ)) :
      rectangleDistribution A B b ψ = ∫ y, b y * ψ y ∂ν := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) ν b ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hb.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hleft {a a' b : ℝ × ℝ → ℝ} {v : ℝ × ℝ} (ha : MemLp a 2 μ)
      (ha' : MemLp a' 2 μ) (hb : MemLp b 2 ν)
      (hd : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v (rectangleDistribution U V a) =
        rectangleDistribution U V a') :
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (v, 0)
        (rectangleProductDistribution U V A B (fun w => a w.1 * b w.2)) =
        rectangleProductDistribution U V A B (fun w => a' w.1 * b w.2) := by
    ext ψ
    let dψ : 𝓓(openRectangleProduct U V A B, ℝ) := TestFunction.lineDerivCLM ℝ (v, 0) ψ
    have hslice (x y : ℝ × ℝ) :
        (TestFunction.lineDerivCLM ℝ v (rectangleTestSliceLeft ψ y) : 𝓓(openRectangle U V, ℝ)) x =
          dψ (x, y) := by
      simp only [dψ, TestFunction.lineDerivCLM_eq_fderivCLM,
        TestFunction.fderivCLM_apply_of_le _ le_top]
      change fderiv ℝ (fun t => ψ (t, y)) x v = fderiv ℝ ψ (x, y) (v, 0)
      exact congrArg (fun L => L v)
        (((ψ.contDiff.differentiable (by simp)) (x, y)).hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)).fderiv
    have hi (y : ℝ × ℝ) : -(∫ x, a x * dψ (x, y) ∂μ) = ∫ x, a' x * ψ (x, y) ∂μ := by
      have hh := congrArg (fun T : 𝓓'(openRectangle U V, ℝ) => T (rectangleTestSliceLeft ψ y)) hd
      rw [Distribution.lineDerivCLM_apply, hpairL (ha.integrable (by norm_num)),
        hpairL (ha'.integrable (by norm_num))] at hh
      simp_rw [hslice] at hh
      convert hh using 1
      rfl
    rw [Distribution.lineDerivCLM_apply, hpair ((hp ha hb).integrable (by norm_num)),
      hpair ((hp ha' hb).integrable (by norm_num))]
    change -(∫ w, a w.1 * b w.2 * dψ w ∂(μ.prod ν)) = _
    rw [integral_prod_symm _ (htest ((hp ha hb).integrable (by norm_num)) dψ),
      integral_prod_symm _ (htest ((hp ha' hb).integrable (by norm_num)) ψ), ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      simp_rw [mul_right_comm (a _) (b y), mul_right_comm (a' _) (b y)]
      rw [integral_mul_const, integral_mul_const, ← neg_mul, hi]
  have hright {a b b' : ℝ × ℝ → ℝ} {v : ℝ × ℝ} (ha : MemLp a 2 μ)
      (hb : MemLp b 2 ν) (hb' : MemLp b' 2 ν)
      (hd : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v (rectangleDistribution A B b) =
        rectangleDistribution A B b') :
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, v)
        (rectangleProductDistribution U V A B (fun w => a w.1 * b w.2)) =
        rectangleProductDistribution U V A B (fun w => a w.1 * b' w.2) := by
    ext ψ
    let dψ : 𝓓(openRectangleProduct U V A B, ℝ) := TestFunction.lineDerivCLM ℝ (0, v) ψ
    have hslice (x y : ℝ × ℝ) :
        (TestFunction.lineDerivCLM ℝ v (rectangleTestSliceRight ψ x) : 𝓓(openRectangle A B, ℝ)) y =
          dψ (x, y) := by
      simp only [dψ, TestFunction.lineDerivCLM_eq_fderivCLM,
        TestFunction.fderivCLM_apply_of_le _ le_top]
      change fderiv ℝ (fun t => ψ (x, t)) y v = fderiv ℝ ψ (x, y) (0, v)
      exact congrArg (fun L => L v)
        (((ψ.contDiff.differentiable (by simp)) (x, y)).hasFDerivAt.comp y
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)).fderiv
    have hi (x : ℝ × ℝ) : -(∫ y, b y * dψ (x, y) ∂ν) = ∫ y, b' y * ψ (x, y) ∂ν := by
      have hh := congrArg (fun T : 𝓓'(openRectangle A B, ℝ) => T (rectangleTestSliceRight ψ x)) hd
      rw [Distribution.lineDerivCLM_apply, hpairR (hb.integrable (by norm_num)),
        hpairR (hb'.integrable (by norm_num))] at hh
      simp_rw [hslice] at hh
      convert hh using 1
      rfl
    rw [Distribution.lineDerivCLM_apply, hpair ((hp ha hb).integrable (by norm_num)),
      hpair ((hp ha hb').integrable (by norm_num))]
    change -(∫ w, a w.1 * b w.2 * dψ w ∂(μ.prod ν)) = _
    rw [integral_prod _ (htest ((hp ha hb).integrable (by norm_num)) dψ),
      integral_prod _ (htest ((hp ha hb').integrable (by norm_num)) ψ), ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp_rw [mul_assoc]
      rw [integral_const_mul, integral_const_mul, ← mul_neg, hi]
  refine ⟨hp hf.1 hg.1, ?_⟩
  intro i
  fin_cases i
  · exact ⟨hp hf.2.1 hg.1, hleft hf.1 hf.2.1 hg.1 hf.2.2.2.1⟩
  · exact ⟨hp hf.2.2.1 hg.1, hleft hf.1 hf.2.2.1 hg.1 hf.2.2.2.2⟩
  · exact ⟨hp hf.1 hg.2.1, hright hf.1 hg.1 hg.2.1 hg.2.2.2.1⟩
  · exact ⟨hp hf.1 hg.2.2.1, hright hf.1 hg.1 hg.2.2.1 hg.2.2.2.2⟩

end CauchyHorizon
