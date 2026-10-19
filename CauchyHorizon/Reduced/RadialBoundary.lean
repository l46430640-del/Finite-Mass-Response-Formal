import CauchyHorizon.Reduced.BoundaryTrace
import CauchyHorizon.Reduced.RadialRestriction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Quantitative radial traces from compatible finite flux integrals. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def radialProductField {U V : ℝ} (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (z : WaveRectangle U V) (hr : ∀ u v, z u v 0 ≠ 0) :
    C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  (⟨fun q : Icc 0 U × Icc 0 V => z q.1 q.2 0 * radialNuField hV e Λ zIn z hr q.1 q.2,
    by fun_prop⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry

theorem radialProductField_tail_bound {U V e Λ C η : ℝ} {hV : 0 ≤ V}
    (zIn : C(Icc 0 U, WaveVector)) (z : WaveRectangle U V) (hr : ∀ u v, z u v 0 ≠ 0)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (hC : 0 ≤ C) (hη : 0 < η)
    (hdec : ∀ t ∈ Icc a b, |radialFluxField e Λ z hr u t| ≤ C * Real.exp (-η * t)) :
    |radialProductField hV e Λ zIn z hr u b - radialProductField hV e Λ zIn z hr u a| ≤
      C / η * Real.exp (-η * a) := by
  let F := radialFluxField e Λ z hr u
  have he (v : Icc 0 V) : radialProductField hV e Λ zIn z hr u v =
      -zIn u 0 + continuousPrimitive hV F v := by
    change z u v 0 * ((-zIn u 0 + continuousPrimitive hV F v) / z u v 0) = _
    field_simp [hr u v]
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((intervalExtension hV F).continuous.intervalIntegrable (0 : ℝ) a)
    ((intervalExtension hV F).continuous.intervalIntegrable (a : ℝ) b)
  have hd : radialProductField hV e Λ zIn z hr u b - radialProductField hV e Λ zIn z hr u a =
      ∫ t in (a : ℝ)..b, intervalExtension hV F t := by
    rw [he, he]
    change (-zIn u 0 + (∫ t in (0 : ℝ)..b, intervalExtension hV F t)) -
      (-zIn u 0 + (∫ t in (0 : ℝ)..a, intervalExtension hV F t)) = _
    linarith only [hs]
  rw [hd]
  have hec : Continuous (fun t : ℝ => C * Real.exp (-η * t)) := by fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (show (a : ℝ) ≤ b from hab) (f := intervalExtension hV F) (g := fun t => C * Real.exp (-η * t))
    (Eventually.of_forall (by
      intro t ht
      have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.trans b.property.2⟩
      simpa only [F, Real.norm_eq_abs, intervalExtension_apply, projIcc_of_mem hV htV] using
        hdec ⟨t, htV⟩ ⟨ht.1.le, ht.2⟩)) (hec.intervalIntegrable _ _)
  rw [Real.norm_eq_abs] at hi
  apply hi.trans
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.2 hη.ne'), integral_exp, smul_eq_mul]
  have hh := mul_nonneg (div_nonneg hC hη.le) (Real.exp_pos (-η * (b : ℝ))).le
  simp only [inv_neg, div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

noncomputable def scalarBoundaryRow {U ε : ℝ} (hε : 0 ≤ ε)
    (Y : (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ))) (t : ℝ) : C(Icc ε U, ℝ) :=
  let T : Ici (0 : ℝ) := ⟨max 0 t, le_max_left (0 : ℝ) t⟩
  ⟨fun u => Y T ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨T, T.property, le_rfl⟩, by fun_prop⟩

theorem scalarBoundaryRow_apply {U ε : ℝ} (hε : 0 ≤ ε)
    (Y : (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      Y S u v = Y T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (T : Ici (0 : ℝ)) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U) :
    scalarBoundaryRow hε Y t u = Y T ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htT⟩ := by
  have he := hcompat ⟨max 0 t, le_max_left (0 : ℝ) t⟩ T (max_le T.property htT)
    ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩
  change Y ⟨max 0 t, le_max_left (0 : ℝ) t⟩ ⟨u, hε.trans u.property.1, u.property.2⟩
    ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ = _
  simpa only [max_eq_right ht] using he

theorem exists_scalar_boundary_limit {U ε C η T₀ : ℝ} (hε : 0 ≤ ε)
    (hT₀ : 0 ≤ T₀) (hC : 0 ≤ C) (hη : 0 < η)
    (Y : (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      Y S u v = Y T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (htail : ∀ (T : Ici (0 : ℝ)) (u : Icc ε U) (a b : Icc 0 (T : ℝ)), T₀ ≤ a → a ≤ b →
      |Y T ⟨u, hε.trans u.property.1, u.property.2⟩ b -
        Y T ⟨u, hε.trans u.property.1, u.property.2⟩ a| ≤ C * Real.exp (-η * a)) :
    ∃ z : C(Icc ε U, ℝ), Tendsto (scalarBoundaryRow hε Y) atTop (𝓝 z) ∧
      ∀ t ≥ T₀, ‖scalarBoundaryRow hε Y t - z‖ ≤ C * Real.exp (-η * t) := by
  have hb : Tendsto (fun t : ℝ => C * Real.exp (-η * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq, mul_zero] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hη))).const_mul C
  obtain ⟨z, hz, hzbound⟩ := exists_limit_of_tail_bound hb (T := T₀) (f := scalarBoundaryRow hε Y) (by
    intro a ha b hab
    rw [dist_comm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (mul_nonneg hC (Real.exp_pos _).le)).2
    intro u
    have ha0 := hT₀.trans ha
    have hb0 := ha0.trans hab
    simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs,
      scalarBoundaryRow_apply hε Y hcompat ⟨b, hb0⟩ hb0 le_rfl,
      scalarBoundaryRow_apply hε Y hcompat ⟨b, hb0⟩ ha0 hab] using
        htail ⟨b, hb0⟩ u ⟨a, ha0, hab⟩ ⟨b, hb0, le_rfl⟩ ha hab)
  exact ⟨z, hz, fun t ht => by simpa only [dist_eq_norm] using hzbound t ht⟩

end CauchyHorizon
