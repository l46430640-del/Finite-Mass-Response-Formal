import CauchyHorizon.Characteristic.ConstraintWave
import CauchyHorizon.Characteristic.ScalarWave
import CauchyHorizon.Reduced.OuterScalar

/-! The outer scalar estimate with one Lp budget, independent of the final time. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem incoming_weighted_integral_le_lp {U V a c δ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hcb : c ≤ a * (1 - 1 / p.toReal)) (hwidth : U * Real.exp (a * V) ≤ δ) :
    Real.exp (c * V) * (∫ t in (0 : ℝ)..U, |f t|) ≤
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal * δ ^ (1 - 1 / p.toReal) := by
  let b := 1 - 1 / p.toReal
  have hb : 0 ≤ b := by
    by_cases ht : p = ∞
    · simp [b, ht]
    · have hp' : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono ht hp
      simpa only [b, div_one] using sub_nonneg.2 (one_div_le_one_div_of_le zero_lt_one hp')
  have hpow : Real.exp (c * V) * U ^ b ≤ δ ^ b := by
    calc
      _ ≤ Real.exp ((a * V) * b) * U ^ b := by
        apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hU _)
        nlinarith only [mul_le_mul_of_nonneg_right hcb hV]
      _ = (U * Real.exp (a * V)) ^ b := by
        rw [Real.mul_rpow hU (Real.exp_pos _).le, ← Real.exp_mul]
        ring
      _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hU (Real.exp_pos _).le) hwidth hb
  have hi := mul_le_mul_of_nonneg_left (incoming_integral_abs_le_lp_power hU hp hf) (Real.exp_pos (c * V)).le
  have hj := mul_le_mul_of_nonneg_left hpow (eLpNorm f p (volume.restrict (Icc 0 U))).toReal_nonneg
  nlinarith only [hi, hj]

theorem IsWaveIntegral.horizon_outer_scalar {M e Λ U V a c ρ N L H A δ : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hA : 0 ≤ A) (hfn : (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A)
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hc0 : 0 ≤ c) (hac : c < a) (hcb : c ≤ a * (1 - 1 / p.toReal))
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0)
    (hν : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hout : ∀ v : Icc 0 V, Real.exp (c * v) * |h v| ≤ H)
    (hwidth : U * Real.exp (a * V) ≤ δ) (hsmall : L * N * δ / (ρ ^ 2 * (a - c)) ≤ 1 / 2) :
    let E := 2 * (H + L * (r 0 / ρ) * (A * δ ^ (1 - 1 / p.toReal))) / ρ
    (∀ u v, |x.2.1 u v 1| ≤ E * Real.exp (-c * v)) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        |x.2.2 u v 1| ≤ (r 0 / ρ) * |f u| + (N / (ρ * (a - c))) * E * Real.exp ((a - c) * v) := by
  have hin (u : Icc 0 U) : |incomingWaveCurve hU hUR hp hf (horizonPhi h r 0) u 0| ≤ r 0 := by
    rw [incomingWaveCurve_apply]
    change |r 0 - (u : ℝ)| ≤ r 0
    rw [abs_of_pos (sub_pos.2 (u.property.2.trans_lt hUR))]
    linarith [u.property.1]
  have hhor (v : Icc 0 V) : Real.exp (c * v) *
      |x.1 ⟨0, le_rfl, hU⟩ v 0 * horizonWaveVelocity M e Λ V hc hi hrc hr0 v 1| ≤ H := by
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
    change Real.exp (c * v) * |r v * (h v / r v)| ≤ H
    have he : r v * (h v / r v) = h v := by field_simp [hr0 v]
    rw [he]
    exact hout v
  have hinput : Real.exp (c * V) * (∫ t in (0 : ℝ)..U, |incomingWaveVelocity hUR hp hf t 1|) ≤
      A * δ ^ (1 - 1 / p.toReal) := by
    have heq : (∫ t in (0 : ℝ)..U, |incomingWaveVelocity hUR hp hf t 1|) = ∫ t in (0 : ℝ)..U, |f t| := by
      simp only [intervalIntegral.integral_of_le hU]
      apply integral_congr_ae
      filter_upwards [ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
        (incomingWaveVelocity_ae hUR hp hf)] with t ht
      rw [ht]
      rfl
    rw [heq]
    exact (incoming_weighted_integral_le_lp hU hV ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp) hf hcb hwidth).trans
      (mul_le_mul_of_nonneg_right hfn (Real.rpow_nonneg hδ _))
  have hs := hx.outer_scalar_bound hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 hc0 hac hρ (hU.trans hUR.le)
    hN hL hH (mul_nonneg hA (Real.rpow_nonneg hδ _)) hδ hlo hin hν hlam hhor hinput hwidth hsmall
  refine ⟨hs.1, ?_⟩
  filter_upwards [hs.2, incomingWaveVelocity_ae hUR hp hf] with u hu hfEq
  intro v
  have ht := hu v
  rw [hfEq] at ht
  exact ht

end CauchyHorizon
