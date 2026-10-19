import CauchyHorizon.Characteristic.TwoAxisWave
import CauchyHorizon.Reduced.RectangleRestriction

/-! Physical characteristic data and their budgets agree on unshifted prefixes. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.data_unique {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {z z' : C(Icc 0 U, WaveVector)} {v v' : C(Icc 0 V, WaveVector)}
    {d d' : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ z v d x) (hx' : IsWaveIntegral hU hV e Λ z' v' d' x) :
    z = z' ∧ v = v' ∧ d = d' := by
  have hz := waveIteration_incoming_value hU hV e Λ z v d x hx.choose
  have hz' := waveIteration_incoming_value hU hV e Λ z' v' d' x hx'.choose
  have hv := waveIteration_outgoing_derivative hU hV e Λ z v d x hx.choose
  have hv' := waveIteration_outgoing_derivative hU hV e Λ z' v' d' x hx'.choose
  have hd := waveIteration_incoming_derivative hU hV e Λ z v d x hx.choose
  have hd' := waveIteration_incoming_derivative hU hV e Λ z' v' d' x hx'.choose
  rw [hx.choose_spec] at hz hv hd
  rw [hx'.choose_spec] at hz' hv' hd'
  refine ⟨ContinuousMap.ext (fun u => (hz u).symm.trans (hz' u)), hv.symm.trans hv', ?_⟩
  apply Lp.ext
  filter_upwards [hd, hd'] with u hu hu'
  exact hu.symm.trans hu'

theorem scalar_prefix_norm_le {A U : ℝ} (hUA : U ≤ A) {p : ℝ≥0∞} {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 A))) :
    (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ (eLpNorm f p (volume.restrict (Icc 0 A))).toReal :=
  ENNReal.toReal_mono hf.2.ne (eLpNorm_mono_measure f (Measure.restrict_mono (Icc_subset_Icc le_rfl hUA) le_rfl))

theorem incomingWaveCurve_prefix {R A U : ℝ} (hA : 0 ≤ A) (hU : 0 ≤ U) (hAR : A < R) (hUA : U ≤ A)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hfA : MemLp f p (volume.restrict (Icc 0 A)))
    (hfU : MemLp f p (volume.restrict (Icc 0 U))) (φ₀ : ℝ) :
    (incomingWaveCurve hA hAR hp hfA φ₀).comp (intervalTranslate (a := 0) le_rfl (by linarith)) =
      incomingWaveCurve hU (hUA.trans_lt hAR) hp hfU φ₀ := by
  apply ContinuousMap.ext
  intro u
  change incomingWaveCurve hA hAR hp hfA φ₀ _ = _
  rw [incomingWaveCurve_apply, incomingWaveCurve_apply]
  change ![incomingRadius R (0 + u), incomingPhi φ₀ f (0 + u), incomingLogOmega R f (0 + u)] = _
  rw [zero_add]

theorem incomingWaveVelocity_prefix {R A U : ℝ} (hAR : A < R) (hUA : U ≤ A)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hfA : MemLp f p (volume.restrict (Icc 0 A)))
    (hfU : MemLp f p (volume.restrict (Icc 0 U))) :
    intervalTranslateLp (a := 0) (U := U) le_rfl (by linarith) (incomingWaveVelocity hAR hp hfA) =
      incomingWaveVelocity (hUA.trans_lt hAR) hp hfU := by
  apply Lp.ext
  filter_upwards [intervalTranslateLp_ae (a := 0) (U := U) le_rfl (by linarith) (incomingWaveVelocity hAR hp hfA),
    intervalTranslate_ae (a := 0) (U := U) le_rfl (by linarith) (incomingWaveVelocity_ae hAR hp hfA),
    incomingWaveVelocity_ae (hUA.trans_lt hAR) hp hfU] with u ht hA hU
  rw [ht, hA, hU, zero_add]

theorem horizonWaveVelocity_prefix {M e Λ B V : ℝ} {h r : ℝ → ℝ} (hVB : V ≤ B)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) :
    (horizonWaveVelocity M e Λ B hc hi hrc hr0).comp (intervalTranslate (a := 0) le_rfl (by linarith)) =
      horizonWaveVelocity M e Λ V hc hi hrc hr0 := by
  apply ContinuousMap.ext
  intro v
  change horizonVelocity M e Λ h r (0 + v) = horizonVelocity M e Λ h r v
  rw [zero_add]

theorem IsWaveIntegral.incoming_translate {A B a U V : ℝ} {hA : 0 ≤ A} {hB : 0 ≤ B} {e Λ : ℝ}
    {zIn : C(Icc 0 A, WaveVector)} {vOut : C(Icc 0 B, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 A))} {x : WaveState A B}
    (hx : IsWaveIntegral hA hB e Λ zIn vOut uIn x)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (ha : 0 ≤ a) (haU : a + U ≤ A) (hVB : V ≤ B) :
    IsWaveIntegral hU hV e Λ (zIn.comp (intervalTranslate ha haU))
      ((x.2.1 ⟨a, ha, by linarith⟩).comp (intervalTranslate (a := 0) le_rfl (by linarith)))
      (intervalTranslateLp ha haU uIn)
      (waveTranslate ha haU (b := 0) (V := V) le_rfl (by linarith) x) := by
  let au := intervalTranslate ha haU
  let bv := intervalTranslate (a := 0) (U := V) le_rfl (show 0 + V ≤ B by linarith)
  let y := waveTranslate ha haU (b := 0) (V := V)
    le_rfl (show 0 + V ≤ B by linarith) x
  let E := ContinuousMap.evalCLM ℝ (⟨0, le_rfl, hV⟩ : Icc 0 V) (M := WaveVector)
  have ha0 : au ⟨0, le_rfl, hU⟩ = ⟨a, ha, by linarith⟩ := Subtype.ext (add_zero _)
  have hb0 : bv ⟨0, le_rfl, hV⟩ = ⟨0, le_rfl, hB⟩ := Subtype.ext (zero_add _)
  have hz := waveIteration_incoming_value hA hB e Λ zIn vOut uIn x hx.choose
  have hd := waveIteration_incoming_derivative hA hB e Λ zIn vOut uIn x hx.choose
  rw [hx.choose_spec] at hz hd
  have hz' : ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) E y.1 = zIn.comp au := by
    apply ContinuousMap.ext
    intro u
    change x.1 (au u) (bv ⟨0, le_rfl, hV⟩) = zIn (au u)
    rw [hb0, hz]
  have hv' : y.2.1 ⟨0, le_rfl, hU⟩ = (x.2.1 ⟨a, ha, by linarith⟩).comp bv := by
    apply ContinuousMap.ext
    intro v
    change x.2.1 (au ⟨0, le_rfl, hU⟩) (bv v) = x.2.1 ⟨a, ha, by linarith⟩ (bv v)
    rw [ha0]
  have hd' : E.compLpL 2 (volume.restrict (Icc 0 U)) y.2.2 =
      intervalTranslateLp ha haU uIn := by
    apply Lp.ext
    filter_upwards [E.coeFn_compLpL y.2.2,
      transverseTranslate_ae ha haU (b := 0) (V := V) le_rfl (by linarith) x.2.2,
      intervalTranslate_ae ha haU hd,
      intervalTranslateLp_ae ha haU uIn] with u he ht hd hu
    rw [he, hu]
    change transverseTranslate ha haU (b := 0) (V := V)
      le_rfl (by linarith) x.2.2 u ⟨0, le_rfl, hV⟩ = uIn (a + u)
    rw [ht]
    change x.2.2 (a + u) (bv ⟨0, le_rfl, hV⟩) = uIn (a + u)
    rw [hb0, hd]
  have hy := hx.translate hU hV ha haU (b := 0) le_rfl (by linarith)
  change IsWaveIntegral hU hV e Λ (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) E y.1)
    (y.2.1 ⟨0, le_rfl, hU⟩) (E.compLpL 2 (volume.restrict (Icc 0 U)) y.2.2) y at hy
  rw [hz', hv', hd'] at hy
  exact hy

theorem IsWaveIntegral.prefix {A B U V : ℝ} {hA : 0 ≤ A} {hB : 0 ≤ B} {e Λ : ℝ}
    {zIn : C(Icc 0 A, WaveVector)} {vOut : C(Icc 0 B, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 A))} {x : WaveState A B}
    (hx : IsWaveIntegral hA hB e Λ zIn vOut uIn x)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUA : U ≤ A) (hVB : V ≤ B) :
    IsWaveIntegral hU hV e Λ (zIn.comp (intervalTranslate (a := 0) le_rfl (by linarith)))
      (vOut.comp (intervalTranslate (a := 0) le_rfl (by linarith)))
      (intervalTranslateLp (a := 0) (U := U) le_rfl (by linarith) uIn)
      (waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by linarith) x) := by
  have hv := waveIteration_outgoing_derivative hA hB e Λ zIn vOut uIn x hx.choose
  rw [hx.choose_spec] at hv
  simpa only [hv] using hx.incoming_translate hU hV (a := 0) le_rfl (by linarith) hVB

theorem IsWaveIntegral.horizon_prefix {M e Λ A B U V : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hUA : U ≤ A) (hVB : V ≤ B)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hfA : MemLp f p (volume.restrict (Icc 0 A)))
    {x : WaveState A B}
    (hx : IsWaveIntegral hA hB e Λ (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ B hc hi hrc hr0) (incomingWaveVelocity hAR hp hfA) x) :
    let hfU := hfA.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hUA) le_rfl)
    IsWaveIntegral hU hV e Λ (incomingWaveCurve hU (hUA.trans_lt hAR) hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity (hUA.trans_lt hAR) hp hfU)
      (waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by linarith) le_rfl (by linarith) x) := by
  have hy := hx.prefix hU hV hUA hVB
  rw [incomingWaveCurve_prefix hA hU hAR hUA hp hfA,
    incomingWaveVelocity_prefix hAR hUA hp hfA, horizonWaveVelocity_prefix hVB hc hi hrc hr0] at hy
  exact hy

theorem IsWaveIntegral.of_vertical_prefix {U B V e Λ : ℝ} {hU : 0 ≤ U} {hB : 0 ≤ B}
    {z z' : C(Icc 0 U, WaveVector)} {v : C(Icc 0 B, WaveVector)} {v' : C(Icc 0 V, WaveVector)}
    {d d' : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U B} {y : WaveState U V}
    (hx : IsWaveIntegral hU hB e Λ z v d x) (hV : 0 ≤ V) (hVB : V ≤ B)
    (hy : IsWaveIntegral hU hV e Λ z' v' d' y)
    (hr : waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp)
      le_rfl (by linarith) x = y) :
    IsWaveIntegral hU hB e Λ z' v d' x := by
  have hp := hx.prefix hU hV le_rfl hVB
  simp only [intervalTranslate_zero, ContinuousMap.comp_id, intervalTranslateLp_zero, hr] at hp
  obtain ⟨hz, _hv, hd⟩ := hp.data_unique hy
  rwa [hz, hd] at hx

end CauchyHorizon
