import CauchyHorizon.Characteristic.TwoAxisWave
import CauchyHorizon.Reduced.ConformalRegularity
import CauchyHorizon.Reduced.ScalarIntegral

/-! Scalar transport and preserved exponents with the actual characteristic data. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.incoming_transverse_regularity {U V R e Λ φ₀ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x) :
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u)) p (volume.restrict (Icc 0 U)) ∧
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (2 : Fin 3))) (x.2.2 u)) (p / 2) (volume.restrict (Icc 0 U)) := by
  have hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 0 = -1 := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]
    rfl
  have hf1 : MemLp (fun u => incomingWaveVelocity hUR hp hf u 1) p (volume.restrict (Icc 0 U)) := by
    apply hf.ae_eq
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]
    rfl
  have hs : MemLp (fun u => f u ^ 2) (p / 2) (volume.restrict (Icc 0 U)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hf.norm_rpow_div (2 : ℝ≥0∞)
  have hw : MemLp (fun u : ℝ => -(R - u)) ∞ (volume.restrict (Icc 0 U)) := by
    apply memLp_top_of_bound (by fun_prop) R
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (sub_pos.2 (hu.2.trans_lt hUR))]
    linarith [hu.1]
  have hℓ : MemLp (fun u => incomingWaveVelocity hUR hp hf u 2) (p / 2) (volume.restrict (Icc 0 U)) := by
    apply (hs.mul' hw).ae_eq
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]
    rfl
  have hpq : p / 2 ≤ p := by
    rw [div_eq_mul_inv]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (by norm_num : (2 : ℝ≥0∞)⁻¹ ≤ 1) (zero_le : 0 ≤ p)
  exact ⟨hx.scalar_transverse_memLp hx.choose hinu hf1,
    hx.conformal_transverse_memLp hx.choose hinu (hf1.mono_exponent hpq) hℓ⟩

theorem IsWaveIntegral.incoming_zeta_transport {U V R e Λ φ₀ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      x.1 (projIcc 0 U hU u) v 0 * x.2.2 u v 1 = (R - u) * f u +
        scalarTransportCorrection hV
          (radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose)
          x.2.1 (projIcc 0 U hU u) v := by
  have hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 0 = -1 := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]
    rfl
  filter_upwards [hx.zeta_transport hx.choose hinu, incomingWaveVelocity_ae hUR hp hf,
    ae_restrict_mem measurableSet_Icc] with u hu hf hm
  intro v
  have he := hu v
  rw [incomingWaveCurve_apply, hf, projIcc_of_mem hU hm] at he
  rw [projIcc_of_mem hU hm]
  exact he

theorem IsWaveIntegral.horizon_theta_integral {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.1 u v 0 * x.2.1 u v 1 = h v +
      ∫ s in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU s) v 0 * x.2.2 s v 1 := by
  have he := hx.theta_integral (c := ![r 0, horizonPhi h r 0, Real.log 4]) rfl u v
  rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v] at he
  change x.1 u v 0 * x.2.1 u v 1 = r v * (h v / r v) + _ at he
  have hh : r v * (h v / r v) = h v := by field_simp [hr0 v]
  rwa [hh] at he

end CauchyHorizon
