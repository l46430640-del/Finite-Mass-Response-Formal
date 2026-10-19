import CauchyHorizon.Characteristic.HorizonGauge
import CauchyHorizon.Reduced.ConstraintIntegral

/-! The actual characteristic data give the integral constraint and interior gauge signs. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem incomingWave_constraint_data {R U : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (φ₀ : ℝ) :
    (∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 0 = -1) ∧
    (∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 2 =
      -incomingWaveCurve hU hUR hp hf φ₀ (projIcc 0 U hU u) 0 *
        (incomingWaveVelocity hUR hp hf u 1) ^ 2) := by
  constructor
  · filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]
    rfl
  · filter_upwards [incomingWaveVelocity_ae hUR hp hf, ae_restrict_mem measurableSet_Icc] with u hu hm
    rw [hu, incomingWaveCurve_apply, projIcc_of_mem hU hm]
    rfl

theorem IsWaveIntegral.incoming_radius_pos {U V R e Λ φ₀ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x) (u : Icc 0 U) (v : Icc 0 V) :
    0 < x.1 u v 0 := by
  have hz := waveIteration_incoming_value hU hV e Λ
    (incomingWaveCurve hU hUR hp hf φ₀) vOut (incomingWaveVelocity hUR hp hf) x hx.choose u
  rw [hx.choose_spec] at hz
  have h0 : 0 < x.1 u ⟨0, le_rfl, hV⟩ 0 := by
    rw [hz]
    exact (sub_pos.2 hUR).trans_le (incomingWaveCurve_radius hU hUR hp hf φ₀ u)
  by_contra hpos
  have hc : Continuous (fun t => intervalExtension hV (x.1 u) t 0) := by fun_prop
  have htgt : (0 : ℝ) ∈ Icc (intervalExtension hV (x.1 u) v 0)
      (intervalExtension hV (x.1 u) 0 0) := by
    simpa only [mem_Icc, intervalExtension_apply, projIcc_of_mem hV v.property,
      projIcc_of_mem hV (show (0 : ℝ) ∈ Icc 0 V from ⟨le_rfl, hV⟩)] using
      And.intro (le_of_not_gt hpos) h0.le
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc' v.property.1 hc.continuousOn htgt
  exact hx.choose u (projIcc 0 V hV t) ht

theorem IsWaveIntegral.interior_gauge {M e Λ U V : ℝ} {h r : ℝ → ℝ}
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
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v
    ν * Real.exp (-x.1 u v 2) = -1 / 4 - ∫ t in (0 : ℝ)..u,
        intervalExtension hU x.1 t v 0 * Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2 ∧
      0 < x.1 u v 0 ∧ ν < 0 ∧
        0 < -Real.exp (x.1 u v 2) / (4 * ν) ∧ -Real.exp (x.1 u v 2) / (4 * ν) ≤ 1 := by
  dsimp only
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)
  have hI := (hx.transverse_constraint_integral hx.choose rfl hn hl v).2 u
  have hg := hx.horizon_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
  have haxis : N ⟨0, le_rfl, hU⟩ v * Real.exp (-x.1 ⟨0, le_rfl, hU⟩ v 2) = -1 / 4 := by
    have hν0 : N ⟨0, le_rfl, hU⟩ v ≠ 0 := ne_of_lt hg.1
    rw [Real.exp_neg, hg.2.1]
    change N ⟨0, le_rfl, hU⟩ v * (-4 * N ⟨0, le_rfl, hU⟩ v)⁻¹ = -1 / 4
    field_simp [hν0]
  rw [haxis] at hI
  refine ⟨hI, hx.incoming_radius_pos hU hV hUR hp hf u v, ?_⟩
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..u,
      intervalExtension hU x.1 t v 0 * Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2 := by
    apply intervalIntegral.integral_nonneg u.property.1
    intro t _ht
    exact mul_nonneg (mul_nonneg
      (hx.incoming_radius_pos hU hV hUR hp hf (projIcc 0 U hU t) v).le (Real.exp_pos _).le) (sq_nonneg _)
  have hbound : N u v * Real.exp (-x.1 u v 2) ≤ -1 / 4 := by linarith only [hI, hnonneg]
  have hν : N u v < 0 := by
    by_contra hn
    have hh := mul_nonneg (le_of_not_gt hn) (Real.exp_pos (-x.1 u v 2)).le
    linarith only [hh, hbound]
  refine ⟨hν, div_pos_of_neg_of_neg (neg_lt_zero.2 (Real.exp_pos _))
    (mul_neg_of_pos_of_neg (by norm_num) hν), ?_⟩
  apply (div_le_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hν)).2
  have he := Real.exp_pos (x.1 u v 2)
  have hb := mul_le_mul_of_nonneg_right hbound he.le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hb
  nlinarith only [hb]

end CauchyHorizon
