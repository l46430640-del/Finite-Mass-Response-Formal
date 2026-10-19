import CauchyHorizon.Characteristic.ConstraintWave
import CauchyHorizon.Reduced.FiniteRadialRate

/-! The finite-time geometric constants are chosen before the incoming scalar data. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem radialPotential_bounded (e Λ : ℝ) {ρ R : ℝ} (hρ : 0 < ρ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc ρ R, |radialPotential r e Λ| ≤ B := by
  have hc : ContinuousOn (fun r => radialPotential r e Λ) (Icc ρ R) := by
    intro r hr
    have hrp : 0 < r := hρ.trans_le hr.1
    unfold radialPotential
    fun_prop (disch := positivity)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, fun r hr => ?_⟩
  have hb : |radialPotential r e Λ| ≤ B := by simpa only [Real.norm_eq_abs] using hB r hr
  exact hb.trans (le_max_left _ _)

theorem horizonWaveVelocity_norm_mono {M e Λ V Vmax : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) (hVmax : V ≤ Vmax) :
    ‖horizonWaveVelocity M e Λ V hc hi hrc hr0‖ ≤ ‖horizonWaveVelocity M e Λ Vmax hc hi hrc hr0‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro v
  exact (horizonWaveVelocity M e Λ Vmax hc hi hrc hr0).norm_coe_le_norm
    ⟨v, v.property.1, v.property.2.trans hVmax⟩

theorem exists_uniform_finite_geometry_on_subrectangles {M e Λ Vmax : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ R A C : ℝ, 0 < R ∧ 0 ≤ A ∧ 0 ≤ C ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), V ≤ Vmax → ∀ hUR : U < r 0,
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
        {x : WaveState U V}
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ u v, ρ ≤ x.1 u v 0) → ∀ u : Icc 0 U, ∀ v : Icc 0 V,
          let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          x.1 u v 0 ≤ R ∧
            (∫ t in (0 : ℝ)..u, Real.exp (intervalExtension hU x.1 t v 2)) ≤ 4 * R ∧
            |x.2.1 u v 0| ≤ A ∧
            Real.exp (-C * v) ≤ -N u v ∧ -N u v ≤ Real.exp (C * v) ∧
            Real.exp (x.1 u v 2) ≤ 4 * Real.exp (C * v) := by
  obtain ⟨R₀, hR₀⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) Vmax)).exists_bound_of_continuousOn hrc.continuousOn
  let R := max ρ R₀
  have hR : ρ ≤ R := le_max_left _ _
  have hRp : 0 < R := hρ.trans_le hR
  have haxis (v : Icc 0 Vmax) : r v ≤ R := by
    have hb : |r v| ≤ R₀ := by simpa only [Real.norm_eq_abs] using hR₀ v v.property
    exact (le_abs_self _).trans (hb.trans (le_max_right _ _))
  let w := horizonWaveVelocity M e Λ Vmax hc hi hrc hr0
  let L := ‖w‖
  have hL : 0 ≤ L := norm_nonneg _
  have hvel (v : Icc 0 Vmax) : |w v 0| ≤ L := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (w v) 0).trans (w.norm_coe_le_norm v)
  obtain ⟨B, hB, hP⟩ := radialPotential_bounded e Λ (R := R) hρ
  let A := (R * L + 4 * R ^ 2 * B) / ρ
  let C := 4 * B + A / ρ
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨R, A, C, hRp, hA, hC, ?_⟩
  intro U V hU hV hVmax hUR p hp f hf x hx hlo
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hnu (u : Icc 0 U) (v : Icc 0 V) : N u v < 0 :=
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1
  have homega (u : Icc 0 U) (v : Icc 0 V) : Real.exp (x.1 u v 2) ≤ -4 * N u v := by
    have hk := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.2.2
    have hd : 4 * N u v < 0 := mul_neg_of_pos_of_neg (by norm_num) (hnu u v)
    have hh := (div_le_iff_of_neg hd).1 hk
    dsimp only [N] at hh ⊢
    linarith only [hh]
  have hax (v : Icc 0 V) : x.1 ⟨0, le_rfl, hU⟩ v 0 ≤ R := by
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
    exact haxis ⟨v, v.property.1, v.property.2.trans hVmax⟩
  have hflux := hx.finite_radial_flux_bound hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1
    hρ hR hB hP hlo hax (fun v => hvel ⟨v, v.property.1, v.property.2.trans hVmax⟩)
      (fun u v => (hnu u v).le) homega
  have hrate := hx.finite_radial_rate_bound hx.choose hρ hA hlo
    (fun u v => hP _ ⟨hlo u v, (hflux u v).1⟩) (fun u v => (hflux u v).2.2) hnu homega
  intro u v
  exact ⟨(hflux u v).1, (hflux u v).2.1, (hflux u v).2.2, hrate u v⟩

theorem exists_uniform_finite_geometry {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ R A C : ℝ, 0 < R ∧ 0 ≤ A ∧ 0 ≤ C ∧
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
        {x : WaveState U V}
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ u v, ρ ≤ x.1 u v 0) → ∀ u : Icc 0 U, ∀ v : Icc 0 V,
          let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          x.1 u v 0 ≤ R ∧
            (∫ t in (0 : ℝ)..u, Real.exp (intervalExtension hU x.1 t v 2)) ≤ 4 * R ∧
            |x.2.1 u v 0| ≤ A ∧
            Real.exp (-C * v) ≤ -N u v ∧ -N u v ≤ Real.exp (C * v) ∧
            Real.exp (x.1 u v 2) ≤ 4 * Real.exp (C * v) := by
  obtain ⟨R, A, C, hR, hA, hC, hb⟩ :=
    exists_uniform_finite_geometry_on_subrectangles (Vmax := V) hc hi hrc hr0 hφ hrd hρ
  exact ⟨R, A, C, hR, hA, hC, hb hU hV le_rfl hUR⟩

end CauchyHorizon
