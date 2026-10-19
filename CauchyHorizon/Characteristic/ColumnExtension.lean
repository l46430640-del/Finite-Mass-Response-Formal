import CauchyHorizon.Characteristic.FiniteState
import CauchyHorizon.Characteristic.PrefixData
import CauchyHorizon.Reduced.CornerExtension
import CauchyHorizon.Reduced.PrefixExtension

/-! A physical first column with uniform size, using finite-time state bounds. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_horizon_column_extension {M e Λ Vmax : ℝ} {h r : ℝ → ℝ}
    (hVmax0 : 0 ≤ Vmax) (hrp : 0 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {U V H : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hH : 0 ≤ H),
        U ≤ d → H ≤ d → V + H ≤ Vmax → ∀ hUR : U < r 0,
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ J →
      ∀ {x : WaveState U V},
        IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x →
        (∀ u v, ρ ≤ x.1 u v 0) →
      ∃ y : WaveState U (V + H),
        IsWaveIntegral hU (add_nonneg hV hH) e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ (V + H) hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) y ∧
        waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp)
          le_rfl (by linarith) y = x ∧
        ∀ u v, ρ / 2 ≤ y.1 u v 0 := by
  obtain ⟨T, hT, hb⟩ := exists_uniform_finite_state_on_subrectangles hVmax0 hrp hc hi hrc hr0 hφ hrd hρ hJ
  let N := max T ‖horizonWaveVelocity M e Λ Vmax hc hi hrc hr0‖
  obtain ⟨d, hd, hd1, hext⟩ := exists_vertical_wave_extension e Λ ρ N hρ (hT.le.trans (le_max_left _ _))
  refine ⟨d, hd, hd1, ?_⟩
  intro U V H hU hV hH hUd hHd hVH hUR p hp f hf hfn x hx hrx
  have hxn : ‖x‖ ≤ N := (hb hU (hUd.trans hd1) hV (by linarith) hUR hp hf hfn hx hrx).1.trans (le_max_left _ _)
  have hvn : ‖horizonWaveVelocity M e Λ (V + H) hc hi hrc hr0‖ ≤ N :=
    (horizonWaveVelocity_norm_mono hc hi hrc hr0 hVH).trans (le_max_right _ _)
  exact hext hU hV hH hUd hHd _ _ _ x _ hx hxn hvn hrx
    (horizonWaveVelocity_prefix (by linarith) hc hi hrc hr0).symm

theorem exists_horizon_prefix_step {M e Λ Vmax : ℝ} {h r : ℝ → ℝ}
    (hVmax0 : 0 ≤ Vmax) (hrp : 0 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {A W V H : ℝ} (hA : 0 ≤ A) (hW : 0 ≤ W) (hV : 0 ≤ V) (hH : 0 ≤ H),
        A + W ≤ 1 → W ≤ d → H ≤ d → V + H ≤ Vmax → ∀ hAR : A + W < r 0,
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 (A + W)))),
        (eLpNorm f p (volume.restrict (Icc 0 (A + W)))).toReal ≤ J →
      let hfA := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (show A ≤ A + W by linarith)) le_rfl)
      ∀ {x : WaveState A (V + H)} {y : WaveState (A + W) V},
        IsWaveIntegral hA (add_nonneg hV hH) e Λ (incomingWaveCurve hA (by linarith : A < r 0) hp hfA (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ (V + H) hc hi hrc hr0) (incomingWaveVelocity (by linarith : A < r 0) hp hfA) x →
        IsWaveIntegral (add_nonneg hA hW) hV e Λ (incomingWaveCurve (add_nonneg hA hW) hAR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hAR hp hf) y →
        (∀ u v, ρ / 2 ≤ x.1 u v 0) → (∀ u v, ρ ≤ y.1 u v 0) →
        waveTranslate (a := 0) (U := A) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) x =
          waveTranslate (a := 0) (U := A) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) y →
      ∃ s : WaveState (A + W) (V + H),
        IsWaveIntegral (add_nonneg hA hW) (add_nonneg hV hH) e Λ
          (incomingWaveCurve (add_nonneg hA hW) hAR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ (V + H) hc hi hrc hr0) (incomingWaveVelocity hAR hp hf) s ∧
        waveTranslate (a := 0) (U := A + W) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) s = y ∧
        waveTranslate (a := 0) (U := A) (b := 0) (V := V + H) le_rfl (by linarith) le_rfl (by simp) s = x ∧
        ∀ u v, ρ / 2 ≤ s.1 u v 0 := by
  obtain ⟨T, hT, hb⟩ := exists_uniform_finite_state_on_subrectangles hVmax0 hrp hc hi hrc hr0 hφ hrd (half_pos hρ) hJ
  obtain ⟨d, hd, hd1, hext⟩ := exists_prefix_wave_extension e Λ ρ T hρ hT.le
  refine ⟨d, hd, hd1, ?_⟩
  intro A W V H hA hW hV hH hAW1 hWd hHd hVH hAR p hp f hf hfn hfA x y hx hy hxr hyr hbot
  have hxn := (hb hA (by linarith) (add_nonneg hV hH) hVH (by linarith) hp hfA
    ((scalar_prefix_norm_le (show A ≤ A + W by linarith) hf).trans hfn) hx hxr).1
  have hyn := (hb (add_nonneg hA hW) hAW1 hV (by linarith) hAR hp hf hfn hy
    (fun u v => (half_le_self hρ.le).trans (hyr u v))).1
  exact hext hA hW hV hH hWd hHd _ _ _ x _ _ _ y hx hy hxn hyn hxr hyr hbot

end CauchyHorizon
