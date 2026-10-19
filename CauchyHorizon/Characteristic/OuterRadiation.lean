import CauchyHorizon.Characteristic.OuterClosure
import CauchyHorizon.Reduced.OuterRadiation

/-! Physical outer geometry supplies a small radiation feedback coefficient. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_horizon_outer_radiation_kernel {m e Λ a k ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
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
    ∃ δ L N : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧ 0 ≤ L ∧ 0 < N ∧
      L * N * δ / (ρ ^ 2 * (a - k)) ≤ 1 / 4 ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        k ≤ a * (1 - 1 / p.toReal) → U * Real.exp (a * V) ≤ δ →
        ∀ M : C(Icc 0 V, ℝ),
          (∀ (u : Icc 0 U) (v : Icc 0 V), Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v) →
          let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          (∀ (u : Icc 0 U) (v : Icc 0 V),
            (u : ℝ) * Real.exp (k * v) * |scalarTransportCorrection hV ν x.2.1 u v| ≤
              (N * δ / ρ) * causalExpIntegral hV (a - k) M v) ∧
            ∀ (u : Icc 0 U) (v : Icc 0 V),
              Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤
                Real.exp (k * v) * |h v| + (L * r 0 / ρ) * Real.exp (k * v) *
                  (∫ t in (0 : ℝ)..u, |f t|) +
                (L * N * δ / ρ ^ 2) * causalExpIntegral hV (a - k) M v := by
  have ha := hk.trans_lt hka
  obtain ⟨δ₀, L, hδ₀, hδ₀1, hδ₀r, hL, hb⟩ := exists_horizon_outer_bounds
    hc hi hrc hr0 hφ hrd ha hk hka hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  let N := (5 / 3) * NH
  let δ := min δ₀ (ρ ^ 2 * (a - k) / (4 * (L * N + 1)))
  have hN : 0 < N := by dsimp only [N]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδδ : δ ≤ δ₀ := min_le_left _ _
  have hsmall : L * N * δ / (ρ ^ 2 * (a - k)) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hρ) (sub_pos.2 hka))).2
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (L * N + 1))).1
      (show δ ≤ ρ ^ 2 * (a - k) / (4 * (L * N + 1)) from min_le_right _ _)
    nlinarith only [hh, hδ]
  refine ⟨δ, L, N, hδ, hδδ.trans hδ₀1, hδδ.trans hδ₀r, hL, hN, hsmall, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hkp hwidth M hM
  have hg := hb U V hU hV hUR p hp f hf x hx hfn hkp (hwidth.trans hδδ)
  have hlo (u : Icc 0 U) (v : Icc 0 V) : ρ ≤ x.1 u v 0 := by
    have hh := (hg u v).1
    linarith only [hh, hρ]
  have hin (u : Icc 0 U) : |incomingWaveCurve hU hUR hp hf (horizonPhi h r 0) u 0| ≤ r 0 := by
    rw [incomingWaveCurve_apply]
    change |r 0 - (u : ℝ)| ≤ r 0
    rw [abs_of_pos (sub_pos.2 (u.property.2.trans_lt hUR))]
    linarith only [u.property.1]
  have hν (u : Icc 0 U) (v : Icc 0 V) :
      |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v| ≤
        N * Real.exp (a * v) := by
    rw [abs_of_neg (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1]
    exact (hg u v).2.2.2.2
  have ht := hx.outer_radiation_kernel hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1
    ha.le hρ hN.le hL hlo hin hν (fun u v => (hg u v).2.2.1) hwidth M hM
  have he (v : Icc 0 V) :
      x.1 ⟨0, le_rfl, hU⟩ v 0 * horizonWaveVelocity m e Λ V hc hi hrc hr0 v 1 = h v := by
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
    change r v * (h v / r v) = h v
    field_simp [hr0 v]
  have hinput (u : Icc 0 U) :
      (∫ t in (0 : ℝ)..u, |incomingWaveVelocity hUR hp hf t 1|) = ∫ t in (0 : ℝ)..u, |f t| := by
    simp only [intervalIntegral.integral_of_le u.property.1]
    apply integral_congr_ae
    have hs : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
    filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) (incomingWaveVelocity_ae hUR hp hf)] with t ht
    rw [ht]
    rfl
  exact ⟨ht.1, fun u v => by simpa only [he v, hinput u] using ht.2 u v⟩

end CauchyHorizon
