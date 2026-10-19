import CauchyHorizon.Reduced.OuterRadiation

/-! A continuous radiation envelope on the shrinking outer region. -/

open MeasureTheory Set

namespace CauchyHorizon

noncomputable def outerRadiationRows {U V δ : ℝ} (hδ : 0 ≤ δ) (a k : ℝ)
    (x : WaveState U V) : C(Icc 0 V, C(Icc 0 U, ℝ)) :=
  (⟨fun q : Icc 0 V × Icc 0 U =>
    let u : Icc 0 U := ⟨min (q.2 : ℝ) (δ * Real.exp (-a * q.1)),
      le_min q.2.property.1 (mul_nonneg hδ (Real.exp_pos _).le),
      (min_le_left _ _).trans q.2.property.2⟩
    Real.exp (k * q.1) * (x.1 u q.1 0 * x.2.1 u q.1 1), by
      fun_prop⟩ : C(Icc 0 V × Icc 0 U, ℝ)).curry

noncomputable def outerRadiationEnvelope {U V δ : ℝ} (hδ : 0 ≤ δ) (a k : ℝ)
    (x : WaveState U V) : C(Icc 0 V, ℝ) :=
  ⟨fun v => ‖outerRadiationRows hδ a k x v‖, (outerRadiationRows hδ a k x).continuous.norm⟩

theorem outerRadiationEnvelope_le_iff {U V δ a k C : ℝ} (hU : 0 ≤ U) (hδ : 0 ≤ δ)
    (x : WaveState U V) (v : Icc 0 V) :
    outerRadiationEnvelope hδ a k x v ≤ C ↔
      ∀ u : Icc 0 U, (u : ℝ) ≤ δ * Real.exp (-a * v) →
        Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ C := by
  let : Nonempty (Icc 0 U) := ⟨⟨0, le_rfl, hU⟩⟩
  change ‖outerRadiationRows hδ a k x v‖ ≤ C ↔ _
  rw [ContinuousMap.norm_le_of_nonempty]
  constructor
  · intro hb u hu
    have hh := hb u
    simpa only [outerRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
      min_eq_left hu, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using hh
  · intro hb u
    dsimp only [outerRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    rw [Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact hb _ (min_le_right _ _)

theorem outerRadiationEnvelope_nonneg {U V δ : ℝ} (hδ : 0 ≤ δ) (a k : ℝ)
    (x : WaveState U V) (v : Icc 0 V) : 0 ≤ outerRadiationEnvelope hδ a k x v := by
  exact norm_nonneg (outerRadiationRows hδ a k x v)

theorem outerRadiationEnvelope_curve_energy {U V δ a k l w : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hδ : 0 ≤ δ) (hl : 0 ≤ l) (hlw : l ≤ w) (hw : w ≤ V)
    (x : WaveState U V) {g : ℝ → ℝ} (hc : ContinuousOn g (Icc l w))
    (hgu : ∀ t ∈ Icc l w, g t ∈ Icc 0 U)
    (hwidth : ∀ t ∈ Icc l w, g t ≤ δ * Real.exp (-a * t)) :
    (∫ t in l..w, (Real.exp (k * t) *
      (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
        intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1)) ^ 2) ≤
      ∫ t in (0 : ℝ)..V, (outerRadiationEnvelope hδ a k x (projIcc 0 V hV t)) ^ 2 := by
  let Θ := fun t => Real.exp (k * t) *
    (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
      intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1)
  let M := fun t => outerRadiationEnvelope hδ a k x (projIcc 0 V hV t)
  have hΘc : ContinuousOn Θ (Icc l w) := by dsimp only [Θ]; fun_prop
  have hMc : Continuous M := by dsimp only [M]; fun_prop
  have hs (t : ℝ) (ht : t ∈ Icc l w) : Θ t ^ 2 ≤ M t ^ 2 := by
    have htv : t ∈ Icc (0 : ℝ) V := ⟨hl.trans ht.1, ht.2.trans hw⟩
    have hh := (outerRadiationEnvelope_le_iff (a := a) (k := k) hU hδ x ⟨t, htv⟩).1 le_rfl
      ⟨g t, hgu t ht⟩ (hwidth t ht)
    have he : |Θ t| ≤ M t := by
      simpa only [Θ, M, intervalExtension_apply, projIcc_of_mem hU (hgu t ht),
        projIcc_of_mem hV htv, abs_mul, abs_of_pos (Real.exp_pos _)] using hh
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Θ t))
      (outerRadiationEnvelope_nonneg hδ a k x (projIcc 0 V hV t))).2 he
  have hi := intervalIntegral.integral_mono_on (μ := volume) hlw
    ((hΘc.pow 2).intervalIntegrable_of_Icc hlw) ((hMc.pow 2).intervalIntegrable _ _) hs
  exact hi.trans (intervalIntegral.integral_mono_interval hl hlw hw
    (Filter.Eventually.of_forall (fun t => sq_nonneg (M t))) ((hMc.pow 2).intervalIntegrable _ _))

theorem causalExpIntegral_prefix {V W d : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W) (hWV : W ≤ V)
    (M : C(Icc 0 V, ℝ)) :
    causalExpIntegral hW d
      (M.comp ⟨fun t => ⟨t, t.property.1, t.property.2.trans hWV⟩, by fun_prop⟩)
      ⟨W, hW, le_rfl⟩ = causalExpIntegral hV d M ⟨W, hW, hWV⟩ := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hW] at ht
  simp only [projIcc_of_mem hW ht, projIcc_of_mem hV ⟨ht.1, ht.2.trans hWV⟩,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]

end CauchyHorizon
