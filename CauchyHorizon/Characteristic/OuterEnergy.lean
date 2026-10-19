import CauchyHorizon.Characteristic.MovingRadiation
import CauchyHorizon.Reduced.RadiationEnergy

/-! Absorbing the actual moving outer radiation on every finite time interval. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_horizon_outer_radiation_energy {m e Λ a k ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (hk : 0 ≤ k) (hka : k < a) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (k * t) * |h t| ≤ H)
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass m h t) e Λ| ≤ W) :
    ∃ (δ C D : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧ 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        k ≤ a * (1 - 1 / p.toReal) →
        let M := outerRadiationEnvelope hδ.le a k x
        ((∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
          4 * ∫ t in (0 : ℝ)..V, (Real.exp (k * t) * |h t| +
            C * Real.exp (k * t) * (∫ s in (0 : ℝ)..min U (δ * Real.exp (-a * t)), |f s|)) ^ 2) ∧
        ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ δ * Real.exp (-a * v) →
          (u : ℝ) * Real.exp (k * v) * |scalarTransportCorrection hV
            (radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
              x.1 hx.choose) x.2.1 u v| ≤ D * causalExpIntegral hV (a - k) M v := by
  obtain ⟨δ, L, N, hδ, hδ1, hδr, hL, hN, hsmall, hb⟩ :=
    exists_horizon_moving_outer_radiation hc hi hrc hr0 hφ hrd hk hka hρ
      hnH hNH hH hW hA haxis hνaxis hout hlout
  let C := L * r 0 / ρ
  have hrpos : 0 < r 0 := (by positivity : 0 < 2 * ρ).trans_le (haxis 0 (by simp)).1
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hL hrpos.le) hρ.le
  refine ⟨δ, C, N * δ / ρ, hδ, hδ1, hδr, hC, by positivity, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hkp M
  let F := fun t => Real.exp (k * t) * |h t| +
    C * Real.exp (k * t) * (∫ s in (0 : ℝ)..min U (δ * Real.exp (-a * t)), |f s|)
  have hfi : IntervalIntegrable (fun s => |f s|) volume 0 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      (hf.integrable ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp)).abs
  have hpc : ContinuousOn (fun s => ∫ w in (0 : ℝ)..s, |f w|) (Icc 0 U) := by
    simpa only [uIcc_of_le hU] using
      intervalIntegral.continuousOn_primitive_interval' hfi left_mem_uIcc
  let S : ℝ → Icc 0 U := fun t => ⟨min U (δ * Real.exp (-a * t)),
    le_min hU (mul_nonneg hδ.le (Real.exp_pos _).le), min_le_left _ _⟩
  have hSc : Continuous S := by fun_prop
  have hFc : Continuous F := by
    have hp := hpc.domRestrict.comp hSc
    change Continuous (fun t => ∫ s in (0 : ℝ)..min U (δ * Real.exp (-a * t)), |f s|) at hp
    unfold F
    fun_prop
  let ε := L * N * δ / ρ ^ 2
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hs : ε ≤ (a - k) / 2 := by
    have hh : ε / (a - k) ≤ 1 / 4 := by simpa only [ε, div_div] using hsmall
    have hh' := (div_le_iff₀ (sub_pos.2 hka)).1 hh
    linarith only [hh', hka]
  refine ⟨?_, fun u v hu => (hb U V hU hV hUR p hp f hf x hx hfn hkp v).2 u hu⟩
  exact causalExpIntegral_absorb_sq hV (sub_pos.2 hka) hε hs M
    (outerRadiationEnvelope_nonneg hδ.le a k x)
    ((hFc.pow 2).intervalIntegrable _ _) (fun v => (hb U V hU hV hUR p hp f hf x hx hfn hkp v).1)

end CauchyHorizon
