import CauchyHorizon.Characteristic.FiniteGeometry
import CauchyHorizon.Reduced.FiniteScalar

/-! Uniform finite-time scalar estimates for the actual characteristic data. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem scalar_section_lp_bound {U V B : ℝ} (hU1 : U ≤ 1) (hB : 0 ≤ B)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {d : WaveTransverse U V}
    (hb : ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, |d u v 1| ≤ B * (|f u| + 1)) :
    (eLpNorm (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (1 : Fin 3))) (d u)) p (volume.restrict (Icc 0 U))).toReal ≤
        B * ((eLpNorm f p (volume.restrict (Icc 0 U))).toReal + 1) := by
  let μ := volume.restrict (Icc (0 : ℝ) U)
  have hμ : μ univ ≤ 1 := by
    simpa only [μ, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_le_one] using hU1
  have hconst : eLpNorm (fun _ : ℝ => (1 : ℝ)) p μ ≤ 1 := by
    have hh := eLpNorm_le_of_ae_bound (p := p) (μ := μ)
      (Filter.Eventually.of_forall (fun _ : ℝ => (show ‖(1 : ℝ)‖ ≤ 1 by norm_num)))
    simpa only [ENNReal.ofReal_one, mul_one] using
      hh.trans (by simpa only [ENNReal.ofReal_one, mul_one] using
        (ENNReal.rpow_le_one hμ (inv_nonneg.2 ENNReal.toReal_nonneg)))
  have hsection : ∀ᵐ u ∂μ,
      ‖(ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
        (ContinuousLinearMap.proj (1 : Fin 3))) (d u)‖ ≤ B * (|f u| + 1) := by
    filter_upwards [hb] with u hu
    apply (ContinuousMap.norm_le _ (mul_nonneg hB (add_nonneg (abs_nonneg _) zero_le_one))).2
    intro v
    exact hu v
  have hnorm := eLpNorm_mono_ae_real (p := p) hsection
  change _ ≤ eLpNorm (B • (fun u => ‖f u‖ + (1 : ℝ))) p μ at hnorm
  rw [eLpNorm_const_smul] at hnorm
  have hadd := eLpNorm_add_le (g := fun _ : ℝ => (1 : ℝ))
    hf.aestronglyMeasurable.norm aestronglyMeasurable_const hp
  have hle := hnorm.trans (mul_le_mul_of_nonneg_left
    (hadd.trans (add_le_add_right hconst _)) (zero_le : (0 : ℝ≥0∞) ≤ ‖B‖ₑ))
  rw [eLpNorm_norm] at hle
  have hfin : ‖B‖ₑ * (eLpNorm f p μ + 1) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨hf.2.ne, by simp⟩)
  have hh := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (show eLpNorm f p μ ≠ ∞ from hf.2.ne) (by simp)] at hh
  simpa only [ENNReal.toReal_one, toReal_enorm, Real.norm_eq_abs, abs_of_nonneg hB] using hh

theorem exists_uniform_finite_scalar_on_subrectangles {M e Λ Vmax : ℝ} {h r : ℝ → ℝ}
    (hVmax0 : 0 ≤ Vmax) (hrp : 0 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ B : ℝ, 0 < B ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (_hU1 : U ≤ 1) (hV : 0 ≤ V), V ≤ Vmax → ∀ hUR : U < r 0,
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ J →
      ∀ {x : WaveState U V}
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ u v, ρ ≤ x.1 u v 0) →
        (∀ u : Icc 0 U, ‖waveCoordinateField 1 x.2.1 u‖ ≤ B) ∧
        (∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
          |x.2.2 u v 1| ≤ B * (|f u| + 1)) ∧
        (eLpNorm (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
          (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u)) p
          (volume.restrict (Icc 0 U))).toReal ≤ B * (J + 1) := by
  obtain ⟨R, A, C, _hR, hA, hC, hgeom⟩ :=
    exists_uniform_finite_geometry_on_subrectangles (Vmax := Vmax) hc hi hrc hr0 hφ hrd hρ
  obtain ⟨H₀, hH₀⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) Vmax)).exists_bound_of_continuousOn hc.continuousOn
  let H := max H₀ 0
  have hH : 0 ≤ H := le_max_right _ _
  have hHbound (v : Icc 0 Vmax) : |h v| ≤ H := by
    have hh : |h v| ≤ H₀ := by simpa only [Real.norm_eq_abs] using hH₀ v v.property
    exact hh.trans (le_max_left _ _)
  let N := Real.exp (C * Vmax)
  let α := r 0 / ρ
  let β := Vmax * N / ρ
  let E := ((H + A * α * J) / ρ) * Real.exp (A * β / ρ)
  let B := 1 + E + α + β * E
  have hN : 0 ≤ N := (Real.exp_pos _).le
  have hα : 0 ≤ α := div_nonneg hrp.le hρ.le
  have hβ : 0 ≤ β := div_nonneg (mul_nonneg hVmax0 hN) hρ.le
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hBE : E ≤ B := by dsimp only [B]; linarith [mul_nonneg hβ hE]
  have hBα : α ≤ B := by dsimp only [B]; linarith [mul_nonneg hβ hE]
  have hBβ : β * E ≤ B := by dsimp only [B]; linarith
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro U V hU hU1 hV hVmax hUR p hp f hf hfn x hx hlo
  have hg := hgeom hU hV hVmax hUR hp hf hx hlo
  have hnu (u : Icc 0 U) (v : Icc 0 V) :
      |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v| ≤ N := by
    have hpos := (Real.exp_pos (-C * (v : ℝ))).trans_le (hg u v).2.2.2.1
    have hneg : radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        x.1 hx.choose u v < 0 := neg_pos.1 hpos
    rw [abs_of_neg hneg]
    exact (hg u v).2.2.2.2.1.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (v.property.2.trans hVmax) hC))
  have hin (u : Icc 0 U) : |incomingWaveCurve hU hUR hp hf (horizonPhi h r 0) u 0| ≤ r 0 := by
    rw [incomingWaveCurve_apply]
    change |r 0 - (u : ℝ)| ≤ r 0
    rw [abs_of_pos (sub_pos.2 (u.property.2.trans_lt hUR))]
    linarith [u.property.1]
  have hout (v : Icc 0 V) :
      |x.1 ⟨0, le_rfl, hU⟩ v 0 * horizonWaveVelocity M e Λ V hc hi hrc hr0 v 1| ≤ H := by
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
    change |r v * (h v / r v)| ≤ H
    have hh : r v * (h v / r v) = h v := by field_simp [hr0 v]
    rw [hh]
    exact hHbound ⟨v, v.property.1, v.property.2.trans hVmax⟩
  have hinput : (∫ t in (0 : ℝ)..U, |incomingWaveVelocity hUR hp hf t 1|) ≤ J := by
    have heq : (∫ t in (0 : ℝ)..U, |incomingWaveVelocity hUR hp hf t 1|) =
        ∫ t in (0 : ℝ)..U, |f t| := by
      simp only [intervalIntegral.integral_of_le hU]
      apply integral_congr_ae
      filter_upwards [ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
        (incomingWaveVelocity_ae hUR hp hf)] with t ht
      rw [ht]
      rfl
    rw [heq]
    exact (incoming_integral_abs_le_lp hU hU1 ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp) hf).trans hfn
  have hs := hx.finite_scalar_bound hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1
    hρ hrp.le hN hA hH hJ hlo hin hnu (fun u v => (hg u v).2.2.1) hout hinput
  let Euv := ((H + A * α * J) / ρ) * Real.exp ((A * (V * N / ρ) / ρ) * U)
  have hβle : V * N / ρ ≤ β := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hVmax hN) hρ.le
  have hEuv : Euv ≤ E := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    calc
      (A * (V * N / ρ) / ρ) * U ≤ A * (V * N / ρ) / ρ := mul_le_of_le_one_right (by positivity) hU1
      _ ≤ A * β / ρ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβle hA) hρ.le
  have hcor : (V * N / ρ) * Euv ≤ β * E := mul_le_mul hβle hEuv (by dsimp only [Euv]; positivity) hβ
  have htrans : ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      |x.2.2 u v 1| ≤ B * (|f u| + 1) := by
    filter_upwards [hs.2, incomingWaveVelocity_ae hUR hp hf] with u hu hfEq
    intro v
    have hu' := hu v
    rw [hfEq] at hu'
    change |x.2.2 u v 1| ≤ α * |f u| + (V * N / ρ) * Euv at hu'
    calc
      _ ≤ α * |f u| + β * E := hu'.trans (add_le_add_right hcor _)
      _ ≤ B * |f u| + B := add_le_add (mul_le_mul_of_nonneg_right hBα (abs_nonneg _)) hBβ
      _ = _ := by ring
  refine ⟨fun u => (hs.1 u).trans (hEuv.trans hBE), htrans, ?_⟩
  exact (scalar_section_lp_bound hU1 hB.le ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp) hf htrans).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left hfn 1) hB.le)

theorem exists_uniform_finite_scalar {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ B : ℝ, 0 < B ∧
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ J →
      ∀ {x : WaveState U V}
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ u v, ρ ≤ x.1 u v 0) →
        (∀ u : Icc 0 U, ‖waveCoordinateField 1 x.2.1 u‖ ≤ B) ∧
        (∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, |x.2.2 u v 1| ≤ B * (|f u| + 1)) ∧
        (eLpNorm (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
          (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u)) p
          (volume.restrict (Icc 0 U))).toReal ≤ B * (J + 1) := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_finite_scalar_on_subrectangles hV (hU.trans_lt hUR) hc hi hrc hr0 hφ hrd hρ hJ
  exact ⟨B, hB, hb hU hU1 hV le_rfl hUR⟩

end CauchyHorizon
