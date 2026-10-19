import CauchyHorizon.Reduced.FiniteUniqueness
import CauchyHorizon.Characteristic.ConstraintWave
import CauchyHorizon.Characteristic.RowExtension

/-! Physical uniqueness on every finite rectangle and compatibility of continuations. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.incoming_unique {U V R e Λ φ₀ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x y : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut (incomingWaveVelocity hUR hp hf) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut (incomingWaveVelocity hUR hp hf) y) : x = y :=
  hx.unique_of_positive_radius hy (hx.incoming_radius_pos hU hV hUR hp hf) (hy.incoming_radius_pos hU hV hUR hp hf)

theorem IsWaveIntegral.horizon_prefix_unique {M e Λ A B U V : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hUA : U ≤ A) (hVB : V ≤ B)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hfA : MemLp f p (volume.restrict (Icc 0 A)))
    (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState A B} {y : WaveState U V}
    (hx : IsWaveIntegral hA hB e Λ (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ B hc hi hrc hr0) (incomingWaveVelocity hAR hp hfA) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU (hUA.trans_lt hAR) hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity (hUA.trans_lt hAR) hp hfU) y) :
    waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by linarith) x = y :=
  (hx.horizon_prefix hA hB hAR hU hV hUA hVB hc hi hrc hr0 hp hfA).incoming_unique hU hV
    (hUA.trans_lt hAR) hp hfU hy

theorem exists_horizon_continuation {M e Λ U T ρ J : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hT : 0 < T) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (hρ : 0 < ρ) (hJ : 0 ≤ J)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hfn : (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ J)
    (hex : ∀ V : ℝ, ∀ hV : 0 ≤ V, V < T → ∃ x : WaveState U V,
      IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x ∧
      ∀ u v, ρ ≤ x.1 u v 0) :
    ∃ H : ℝ, ∃ hH : 0 < H, ∃ y : WaveState U (T + H),
      IsWaveIntegral hU (add_nonneg hT.le hH.le) e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ (T + H) hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) y ∧
      (∀ u v, ρ / 2 ≤ y.1 u v 0) ∧
      ∀ {V : ℝ} (hV : 0 ≤ V) (hVT : V < T) {x : WaveState U V},
        IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x →
        waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) y = x := by
  obtain ⟨H, hH, y, hy, hr, _hold⟩ := exists_horizon_past_finite_time hU hU1 hT hUR hc hi hrc hr0 hφ hrd hρ hJ hp hf hfn hex
  refine ⟨H, hH, y, hy, hr, ?_⟩
  intro V hV hVT x hx
  exact hy.horizon_prefix_unique hU (add_nonneg hT.le hH.le) hUR hU hV le_rfl (by linarith)
    hc hi hrc hr0 hp hf hf hx

end CauchyHorizon
