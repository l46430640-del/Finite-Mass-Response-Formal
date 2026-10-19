import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.ContinuousMap.Compact

/-! Bounded operator coefficients act on the actual L2_u C_v space. -/

open MeasureTheory
open scoped ENNReal

namespace CauchyHorizon

variable {J E : Type*} [TopologicalSpace J] [CompactSpace J]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def pointwiseOperator (A : C(J, E →L[ℝ] E)) : C(J, E) →L[ℝ] C(J, E) :=
  LinearMap.mkContinuous
    { toFun := fun f : C(J, E) => ⟨fun x => A x (f x), A.continuous.clm_apply f.continuous⟩
      map_add' := fun f g => by ext x; simp
      map_smul' := fun c f => by ext x; simp }
    ‖A‖ (fun f => by
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro x
      exact ((A x).le_opNorm (f x)).trans
        (mul_le_mul (A.norm_coe_le_norm x) (f.norm_coe_le_norm x) (norm_nonneg (f x)) (norm_nonneg A)))

@[simp] theorem pointwiseOperator_apply (A : C(J, E →L[ℝ] E)) (f : C(J, E)) (x : J) :
    pointwiseOperator A f x = A x (f x) := rfl

theorem pointwiseOperator_norm_le (A : C(J, E →L[ℝ] E)) : ‖pointwiseOperator A‖ ≤ ‖A‖ := by
  apply (pointwiseOperator A).opNorm_le_bound (norm_nonneg A)
  intro f
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  exact ((A x).le_opNorm (f x)).trans
    (mul_le_mul (A.norm_coe_le_norm x) (f.norm_coe_le_norm x) (norm_nonneg (f x)) (norm_nonneg A))

noncomputable def pointwiseOperatorL : C(J, E →L[ℝ] E) →L[ℝ] (C(J, E) →L[ℝ] C(J, E)) :=
  LinearMap.mkContinuous
    { toFun := fun A : C(J, E →L[ℝ] E) => pointwiseOperator A
      map_add' := fun A B => by ext f x; simp
      map_smul' := fun c A => by ext f x; simp }
    1 (fun A => by
      change ‖pointwiseOperator A‖ ≤ 1 * ‖A‖
      rw [one_mul]
      exact pointwiseOperator_norm_le A)

@[simp] theorem pointwiseOperatorL_apply (A : C(J, E →L[ℝ] E)) :
    pointwiseOperatorL A = pointwiseOperator A := rfl

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

noncomputable def operatorProduct (A : Lp (E →L[ℝ] E) ∞ μ) (u : Lp E 2 μ) : Lp E 2 μ :=
  (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).holder 2 A u

theorem operatorProduct_ae (A : Lp (E →L[ℝ] E) ∞ μ) (u : Lp E 2 μ) :
    operatorProduct A u =ᵐ[μ] fun x => A x (u x) :=
  (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).coeFn_holder A u

theorem operatorProduct_norm_le (A : Lp (E →L[ℝ] E) ∞ μ) (u : Lp E 2 μ) :
    ‖operatorProduct A u‖ ≤ ‖A‖ * ‖u‖ := by
  calc
    _ ≤ ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ * ‖A‖ * ‖u‖ :=
      (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).norm_holder_apply_apply_le A u
    _ ≤ 1 * ‖A‖ * ‖u‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg A)) (norm_nonneg u)
    _ = _ := by rw [one_mul]

theorem operatorProduct_difference (A B : Lp (E →L[ℝ] E) ∞ μ) (u v : Lp E 2 μ) :
    operatorProduct A u - operatorProduct B v = operatorProduct (A - B) u + operatorProduct B (u - v) := by
  let T := (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).holderL μ ∞ 2 2
  change T A u - T B v = T (A - B) u + T B (u - v)
  simp only [map_sub, sub_apply]
  abel

noncomputable def affineMixedSource (g : Lp E 2 μ) (A : Lp (E →L[ℝ] E) ∞ μ)
    (u : Lp E 2 μ) : Lp E 2 μ := g + operatorProduct A u

theorem affineMixedSource_ae (g : Lp E 2 μ) (A : Lp (E →L[ℝ] E) ∞ μ) (u : Lp E 2 μ) :
    affineMixedSource g A u =ᵐ[μ] fun x => g x + A x (u x) := by
  filter_upwards [Lp.coeFn_add g (operatorProduct A u), operatorProduct_ae A u] with x hx hA
  exact hx.trans (congrArg (fun y => g x + y) hA)

theorem affineMixedSource_difference_bound (g h : Lp E 2 μ)
    (A B : Lp (E →L[ℝ] E) ∞ μ) (u v : Lp E 2 μ) :
    ‖affineMixedSource g A u - affineMixedSource h B v‖ ≤
      ‖g - h‖ + ‖A - B‖ * ‖u‖ + ‖B‖ * ‖u - v‖ := by
  have he : affineMixedSource g A u - affineMixedSource h B v =
      (g - h) + operatorProduct (A - B) u + operatorProduct B (u - v) := by
    unfold affineMixedSource
    calc
      _ = (g - h) + (operatorProduct A u - operatorProduct B v) := by abel
      _ = _ := by rw [operatorProduct_difference]; abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add_right (operatorProduct_norm_le (A - B) u) _))
    (operatorProduct_norm_le B (u - v)))

end CauchyHorizon
