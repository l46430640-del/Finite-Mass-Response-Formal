import CauchyHorizon.Characteristic.WeightedScalar

/-! Zero incoming scalar data remove the Holder restriction on the time weight. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_zero_weighted_scalar {M e Λ U V a c ρ N L H D : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hf : MemLp (fun _ : ℝ => (0 : ℝ)) p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hc0 : 0 ≤ c) (hca : c < a) (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0)
    (hν : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hout : ∀ v : Icc 0 V, Real.exp (c * v) * |h v| ≤ H)
    (hwidth : U * Real.exp (a * V) ≤ D) :
    let E := H / ρ * Real.exp (L * N * D / (ρ ^ 2 * (a - c)))
    (∀ u v, |x.2.1 u v 1| ≤ E * Real.exp (-c * v)) ∧
      ∀ u v, |scalarTransportCorrection hV
        (radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose)
        x.2.1 u v| ≤ N * E / (a - c) * Real.exp ((a - c) * v) := by
  intro E
  have hin (u : Icc 0 U) : |incomingWaveCurve hU hUR hp hf (horizonPhi h r 0) u 0| ≤ r 0 := by
    rw [incomingWaveCurve_apply]
    change |r 0 - (u : ℝ)| ≤ r 0
    rw [abs_of_pos (sub_pos.2 (u.property.2.trans_lt hUR))]
    linarith only [u.property.1]
  have hhor (v : Icc 0 V) : Real.exp (c * v) *
      |x.1 ⟨0, le_rfl, hU⟩ v 0 * horizonWaveVelocity M e Λ V hc hi hrc hr0 v 1| ≤ H := by
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
    change Real.exp (c * v) * |r v * (h v / r v)| ≤ H
    rw [mul_div_cancel₀ _ (hr0 v)]
    exact hout v
  have hinput : Real.exp (c * V) * (∫ t in (0 : ℝ)..U, |incomingWaveVelocity hUR hp hf t 1|) ≤ 0 := by
    have heq : (∫ t in (0 : ℝ)..U, |incomingWaveVelocity hUR hp hf t 1|) = ∫ _t in (0 : ℝ)..U, (0 : ℝ) := by
      simp only [intervalIntegral.integral_of_le hU]
      apply integral_congr_ae
      filter_upwards [ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
        (incomingWaveVelocity_ae hUR hp hf)] with t ht
      rw [ht]
      change |(0 : ℝ)| = 0
      exact abs_zero
    rw [heq]
    simp
  have hscalar : ∀ u v, |x.2.1 u v 1| ≤ E * Real.exp (-c * v) := by
    simpa only [mul_zero, add_zero] using
      (hx.weighted_scalar_bound hx.choose rfl
        (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 hc0 hca hρ
        (hU.trans hUR.le) hN hL hH le_rfl hlo hin hν hlam hhor hinput hwidth).1
  refine ⟨hscalar, ?_⟩
  exact scalarTransportCorrection_weighted_bound hca hN
    (mul_nonneg (div_nonneg hH hρ.le) (Real.exp_pos _).le) _ _ hν hscalar

end CauchyHorizon
