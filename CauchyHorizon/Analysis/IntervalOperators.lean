import CauchyHorizon.Analysis.MixedPrimitive
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.Order.ProjIcc

/-! Continuous and L2 characteristic integrals use the same restricted Lebesgue measure. -/

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace CauchyHorizon

variable {a b : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def intervalExtension (hab : a ≤ b) : C(Icc a b, E) →L[ℝ] (ℝ →ᵇ E) :=
  (BoundedContinuousFunction.compContinuousCLM E ℝ
    ⟨projIcc a b hab, continuous_projIcc⟩).comp
    (ContinuousMap.linearIsometryBoundedOfCompact (Icc a b) E ℝ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem intervalExtension_apply (hab : a ≤ b) (f : C(Icc a b, E)) (t : ℝ) :
    intervalExtension hab f t = f (projIcc a b hab t) := rfl

theorem intervalExtension_norm_le (hab : a ≤ b) (f : C(Icc a b, E)) :
    ‖intervalExtension hab f‖ ≤ ‖f‖ :=
  BoundedContinuousFunction.norm_compContinuous_le _ _

noncomputable def intervalToLp (hab : a ≤ b) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    C(Icc a b, E) →L[ℝ] Lp E p (volume.restrict (Icc a b)) :=
  (BoundedContinuousFunction.toLp p (volume.restrict (Icc a b)) ℝ).comp (intervalExtension hab)

theorem intervalToLp_ae (hab : a ≤ b) (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : C(Icc a b, E)) :
    intervalToLp hab p f =ᵐ[volume.restrict (Icc a b)] fun t => f (projIcc a b hab t) :=
  BoundedContinuousFunction.coeFn_toLp p (volume.restrict (Icc a b)) ℝ (intervalExtension hab f)

theorem intervalToLp_norm_le (hab : a ≤ b) (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : C(Icc a b, E)) :
    ‖intervalToLp hab p f‖ ≤ (b - a) ^ p.toReal⁻¹ * ‖f‖ := by
  have h := BoundedContinuousFunction.Lp_norm_le (p := p) (μ := volume.restrict (Icc a b))
    (intervalExtension hab f)
  change ‖intervalToLp hab p f‖ ≤ _ at h
  have hm : (measureUnivNNReal (volume.restrict (Icc a b)) : ℝ) = b - a := by
    change (volume.restrict (Icc a b)).real univ = b - a
    rw [measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
  rw [hm] at h
  exact h.trans (mul_le_mul_of_nonneg_left (intervalExtension_norm_le hab f) (Real.rpow_nonneg (sub_nonneg.2 hab) _))

theorem intervalToL2_norm_le (hab : a ≤ b) (f : C(Icc a b, E)) :
    ‖intervalToLp hab 2 f‖ ≤ Real.sqrt (b - a) * ‖f‖ := by
  simpa only [ENNReal.toReal_ofNat, Real.sqrt_eq_rpow, one_div] using intervalToLp_norm_le hab 2 f

theorem intervalToLinf_norm_le (hab : a ≤ b) (f : C(Icc a b, E)) :
    ‖intervalToLp hab ∞ f‖ ≤ ‖f‖ := by
  simpa only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, one_mul] using intervalToLp_norm_le hab ∞ f

noncomputable def continuousPrimitive (hab : a ≤ b) (f : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := ∫ x in a..(t : ℝ), intervalExtension hab f x
  continuous_toFun := by
    have hc := (intervalExtension hab f).continuous
    have h := intervalIntegral.continuousOn_primitive_interval' (hc.intervalIntegrable (μ := volume) a b) left_mem_uIcc
    rw [uIcc_of_le hab] at h
    exact h.domRestrict

theorem continuousPrimitive_norm_le (hab : a ≤ b) (f : C(Icc a b, E)) :
    ‖continuousPrimitive hab f‖ ≤ (b - a) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (sub_nonneg.2 hab) (norm_nonneg f))).2
  intro t
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := (t : ℝ)) (f := fun x => intervalExtension hab f x)
    (fun x _ => f.norm_coe_le_norm (projIcc a b hab x))
  rw [abs_of_nonneg (sub_nonneg.2 t.property.1)] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (sub_le_sub_right t.property.2 a) (norm_nonneg f)).trans_eq (mul_comm _ _))

noncomputable def continuousPrimitiveL (hab : a ≤ b) : C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
  LinearMap.mkContinuous
    { toFun := fun f : C(Icc a b, E) => continuousPrimitive hab f
      map_add' := fun f g => by
        ext t
        change (∫ x in a..(t : ℝ), intervalExtension hab (f + g) x) = _
        simp only [map_add, BoundedContinuousFunction.add_apply]
        exact intervalIntegral.integral_add ((intervalExtension hab f).continuous.intervalIntegrable _ _)
          ((intervalExtension hab g).continuous.intervalIntegrable _ _)
      map_smul' := fun c f => by
        ext t
        change (∫ x in a..(t : ℝ), intervalExtension hab (c • f) x) = _
        simp only [map_smul, BoundedContinuousFunction.smul_apply]
        exact intervalIntegral.integral_smul c _ }
    (b - a) (fun f => by
      change ‖continuousPrimitive hab f‖ ≤ (b - a) * ‖f‖
      exact continuousPrimitive_norm_le hab f)

@[simp] theorem continuousPrimitiveL_apply (hab : a ≤ b) (f : C(Icc a b, E)) :
    continuousPrimitiveL hab f = continuousPrimitive hab f := rfl

theorem continuousPrimitiveL_norm_le (hab : a ≤ b) :
    ‖continuousPrimitiveL (E := E) hab‖ ≤ b - a :=
  (continuousPrimitiveL (E := E) hab).opNorm_le_bound (sub_nonneg.2 hab) (continuousPrimitive_norm_le hab)

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

noncomputable def verticalPrimitive (hab : a ≤ b) : Lp C(Icc a b, E) 2 μ →L[ℝ] Lp C(Icc a b, E) 2 μ :=
  (continuousPrimitiveL (E := E) hab).compLpL 2 μ

theorem verticalPrimitive_norm_le (hab : a ≤ b) (f : Lp C(Icc a b, E) 2 μ) :
    ‖verticalPrimitive hab f‖ ≤ (b - a) * ‖f‖ := by
  change ‖(continuousPrimitiveL (E := E) hab).compLp f‖ ≤ _
  exact ((continuousPrimitiveL (E := E) hab).norm_compLp_le f).trans
    (mul_le_mul_of_nonneg_right (continuousPrimitiveL_norm_le (E := E) hab) (norm_nonneg f))

theorem verticalPrimitive_ae (hab : a ≤ b) (f : Lp C(Icc a b, E) 2 μ) :
    verticalPrimitive hab f =ᵐ[μ] fun x => continuousPrimitive hab (f x) := by
  simpa only [verticalPrimitive, continuousPrimitiveL_apply] using
    (continuousPrimitiveL (E := E) hab).coeFn_compLpL f

end CauchyHorizon
