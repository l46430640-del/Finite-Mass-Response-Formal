import CauchyHorizon.Characteristic.ColumnExtension
import CauchyHorizon.Analysis.FiniteSubdivision

/-! Finite horizontal subdivision extends a complete physical rectangle by a uniform time step. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_horizon_row_extension {M e Λ Vmax : ℝ} {h r : ℝ → ℝ}
    (hVmax0 : 0 ≤ Vmax) (hrp : 0 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {U V H : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hH : 0 ≤ H),
        U ≤ 1 → H ≤ d → V + H ≤ Vmax → ∀ hUR : U < r 0,
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
  obtain ⟨d₀, hd₀, hd₀1, hstart⟩ := exists_horizon_column_extension hVmax0 hrp hc hi hrc hr0 hφ hrd hρ hJ
  obtain ⟨d₁, hd₁, _hd₁1, hnext⟩ := exists_horizon_prefix_step hVmax0 hrp hc hi hrc hr0 hφ hrd hρ hJ
  let d := min d₀ d₁
  have hd : 0 < d := lt_min hd₀ hd₁
  refine ⟨d, hd, (min_le_left _ _).trans hd₀1, ?_⟩
  intro U V H hU hV hH hU1 hHd hVH hUR p hp f hf hfn x hx hrx
  let P (a : ℝ) : Prop := ∃ ha : 0 ≤ a, ∃ haU : a ≤ U, ∃ z : WaveState a (V + H),
    let hfa := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl haU) le_rfl)
    IsWaveIntegral ha (add_nonneg hV hH) e Λ (incomingWaveCurve ha (haU.trans_lt hUR) hp hfa (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ (V + H) hc hi hrc hr0) (incomingWaveVelocity (haU.trans_lt hUR) hp hfa) z ∧
    waveTranslate (a := 0) (U := a) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) z =
      waveTranslate (a := 0) (U := a) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) x ∧
    ∀ u v, ρ / 2 ≤ z.1 u v 0
  have hbase : P 0 := by
    let hf0 := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hU) le_rfl)
    have hy := hx.horizon_prefix hU hV hUR le_rfl hV hU le_rfl hc hi hrc hr0 hp hf
    obtain ⟨z, hz, hb, hr⟩ := hstart le_rfl hV hH hd₀.le (hHd.trans (min_le_left _ _)) hVH hrp hp hf0
      ((scalar_prefix_norm_le hU hf).trans hfn) hy (fun u v => hrx _ _)
    exact ⟨le_rfl, hU, z, hz, hb, hr⟩
  have hstep (a W : ℝ) (_ha : 0 ≤ a) (hW : 0 ≤ W) (haW : a + W ≤ U) (hWd : W ≤ d) (hPa : P a) : P (a + W) := by
    obtain ⟨ha, haU, z, hz, hb, hr⟩ := hPa
    let hfW := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl haW) le_rfl)
    let old := waveTranslate (a := 0) (U := a + W) (b := 0) (V := V)
      le_rfl (show 0 + (a + W) ≤ U by linarith) le_rfl (show 0 + V ≤ V by simp) x
    have hold := hx.horizon_prefix hU hV hUR (add_nonneg ha hW) hV haW le_rfl hc hi hrc hr0 hp hf
    have hmatch : waveTranslate (a := 0) (U := a) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith) z =
        waveTranslate (a := 0) (U := a) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by simp) old := by
      rw [hb]
      simp only [old, waveTranslate_comp, zero_add]
    obtain ⟨s, hs, hsb, _hsl, hsr⟩ := hnext ha hW hV hH (haW.trans hU1)
      (hWd.trans (min_le_right _ _)) (hHd.trans (min_le_right _ _)) hVH (haW.trans_lt hUR) hp hfW
      ((scalar_prefix_norm_le haW hf).trans hfn) hz hold hr (fun u v => hrx _ _) hmatch
    exact ⟨add_nonneg ha hW, haW, s, hs, hsb, hsr⟩
  have hfull : P U := interval_subdivision_induction hU hd hbase hstep
  obtain ⟨_ha, _haU, y, hy, hb, hr⟩ := hfull
  exact ⟨y, hy, hb.trans (waveTranslate_zero x), hr⟩

theorem exists_horizon_past_finite_time {M e Λ U T ρ J : ℝ} {h r : ℝ → ℝ}
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
      ∃ V : ℝ, ∃ hV : 0 ≤ V, ∃ hVT : V < T, ∃ x : WaveState U V,
        IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x ∧
        (∀ u v, ρ ≤ x.1 u v 0) ∧
        waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp) le_rfl (by linarith [hVT]) y = x := by
  obtain ⟨d, hd, hd1, hext⟩ := exists_horizon_row_extension (Vmax := T + 1) (by linarith)
    (hU.trans_lt hUR) hc hi hrc hr0 hφ hrd hρ hJ
  let V := max 0 (T - d / 2)
  have hV : 0 ≤ V := le_max_left _ _
  have hVT : V < T := max_lt hT (by linarith)
  have hVlo : T - d / 2 ≤ V := le_max_right _ _
  obtain ⟨x, hx, hrx⟩ := hex V hV hVT
  let H := d / 4
  have hH : 0 < H := by dsimp only [H]; positivity
  have ht : 0 ≤ T + H - V := by linarith
  obtain ⟨y, hy, hb, hry⟩ := hext hU hV ht hU1 (by dsimp only [H]; linarith)
    (by dsimp only [H]; linarith) hUR hp hf hfn hx hrx
  let z := waveTranslate (a := 0) (U := U) (b := 0) (V := T + H)
    le_rfl (show 0 + U ≤ U by simp) le_rfl (show 0 + (T + H) ≤ V + (T + H - V) by linarith) y
  have hz := hy.horizon_prefix hU (add_nonneg hV ht) hUR hU (add_nonneg hT.le hH.le)
    le_rfl (by linarith) hc hi hrc hr0 hp hf
  have hzb : waveTranslate (a := 0) (U := U) (b := 0) (V := V)
      le_rfl (by simp) le_rfl (by linarith) z = x := by
    simpa only [z, waveTranslate_comp, zero_add] using hb
  exact ⟨H, hH, z, hz, fun u v => hry _ _, V, hV, hVT, x, hx, hrx, hzb⟩

end CauchyHorizon
