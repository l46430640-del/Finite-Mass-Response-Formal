import CauchyHorizon.Characteristic.OuterEnergy
import CauchyHorizon.Analysis.LogarithmicEnergy

/-! Actual nonlinear outer radiation has a common finite-time L2 bound. -/

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace CauchyHorizon

set_option maxHeartbeats 600000 in
theorem exists_horizon_outer_energy_bound {m e Λ a b k s ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) (hcrit : k = a * b) (hks : k < s) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), |h t| ≤ H * Real.exp (-s * t))
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass m h t) e Λ| ≤ W) :
    ∃ (δ C D : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧ 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (B : ℝ →ᵇ ℝ)
        (hB : Integrable (fun t => B t ^ 2))
        (hf : MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 U))).toReal ≤ A →
        k ≤ a * (1 - 1 / p.toReal) →
        let M := outerRadiationEnvelope hδ.le a k x
        ((∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
          4 * H ^ 2 / (s - k) + 8 * C ^ 2 * δ ^ (2 * b) / a * ∫ t, B t ^ 2) ∧
        ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ δ * Real.exp (-a * v) →
          (u : ℝ) * Real.exp (k * v) * |scalarTransportCorrection hV
            (radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
              x.1 hx.choose) x.2.1 u v| ≤ D * causalExpIntegral hV (a - k) M v := by
  have hk : 0 ≤ k := by rw [hcrit]; positivity
  have hka : k < a := by rw [hcrit]; nlinarith only [ha, hb1]
  have hwout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : Real.exp (k * t) * |h t| ≤ H := by
    calc
      _ ≤ Real.exp (k * t) * (H * Real.exp (-s * t)) :=
        mul_le_mul_of_nonneg_left (hout t ht) (Real.exp_pos _).le
      _ = H * (Real.exp (k * t) * Real.exp (-s * t)) := by ring
      _ = H * Real.exp ((k - s) * t) := by rw [← Real.exp_add]; congr 2; ring
      _ ≤ H * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hks.le) ht)) hH
      _ = H := mul_one _
  obtain ⟨δ, C, D, hδ, hδ1, hδr, hC, hD, hbound⟩ :=
    exists_horizon_outer_radiation_energy hc hi hrc hr0 hφ hrd hk hka hρ
      hnH hNH hH hW hA haxis hνaxis hwout hlout
  refine ⟨δ, C, D, hδ, hδ1, hδr, hC, hD, ?_⟩
  intro U V hU hV hUR p hp ℓ B hB hf x hx hfn hkp M
  refine ⟨?_, (hbound U V hU hV hUR p hp (logarithmicIncoming b ℓ B) hf x hx hfn hkp).2⟩
  let O := fun t => Real.exp (k * t) * |h t|
  let G := fun t => Real.exp (k * t) *
    (∫ u in (0 : ℝ)..min U (δ * Real.exp (-a * t)), |logarithmicIncoming b ℓ B u|)
  have hOi := weighted_exponential_energy hV hks hH hc hout
  have hGi := logarithmicIncoming_outer_energy_bound hU hV hδ ha hb hcrit ℓ B hB
  have hpc : ContinuousOn (fun u => ∫ w in (0 : ℝ)..u, |logarithmicIncoming b ℓ B w|)
      (Icc 0 U) := by
    simpa only [uIcc_of_le hU] using intervalIntegral.continuousOn_primitive_interval'
      (logarithmicIncoming_primitive hb hU ℓ B).1.abs left_mem_uIcc
  let S : ℝ → Icc 0 U := fun t => ⟨min U (δ * Real.exp (-a * t)),
    le_min hU (mul_nonneg hδ.le (Real.exp_pos _).le), min_le_left _ _⟩
  have hSc : Continuous S := by fun_prop
  have hGc : Continuous G := by
    have hh := hpc.domRestrict.comp hSc
    change Continuous (fun t => ∫ w in (0 : ℝ)..min U (δ * Real.exp (-a * t)),
      |logarithmicIncoming b ℓ B w|) at hh
    unfold G
    fun_prop
  have hOc : Continuous O := by unfold O; fun_prop
  have hsum : (∫ t in (0 : ℝ)..V, (O t + C * G t) ^ 2) ≤
      2 * (∫ t in (0 : ℝ)..V, O t ^ 2) + 2 * C ^ 2 * ∫ t in (0 : ℝ)..V, G t ^ 2 := by
    have hFc : Continuous (fun t => (O t + C * G t) ^ 2) := by fun_prop
    have hRc : Continuous (fun t => 2 * O t ^ 2 + 2 * C ^ 2 * G t ^ 2) := by fun_prop
    have hh := intervalIntegral.integral_mono_on (μ := volume) hV (hFc.intervalIntegrable _ _)
      (hRc.intervalIntegrable _ _) (fun t _ => by nlinarith only [sq_nonneg (O t - C * G t)])
    have hiO : IntervalIntegrable (fun t => 2 * O t ^ 2) volume 0 V :=
      ((hOc.pow 2).const_mul 2).intervalIntegrable _ _
    have hiG : IntervalIntegrable (fun t => 2 * C ^ 2 * G t ^ 2) volume 0 V :=
      ((hGc.pow 2).const_mul (2 * C ^ 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hiO hiG,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hh
    exact hh
  have hactual := (hbound U V hU hV hUR p hp (logarithmicIncoming b ℓ B) hf x hx hfn hkp).1
  simp only [mul_assoc] at hactual
  change (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
    4 * ∫ t in (0 : ℝ)..V, (O t + C * G t) ^ 2 at hactual
  have hin := mul_le_mul_of_nonneg_left hGi (by positivity : 0 ≤ 2 * C ^ 2)
  have hout' := mul_le_mul_of_nonneg_left hOi (by norm_num : (0 : ℝ) ≤ 2)
  have hs := hsum.trans (add_le_add hout' hin)
  exact (hactual.trans (mul_le_mul_of_nonneg_left hs (by norm_num))).trans_eq
    (by field_simp; ring)

end CauchyHorizon
