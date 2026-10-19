import CauchyHorizon.Reduced.HorizontalPasting
import CauchyHorizon.Reduced.LocalPasting

/-! Fill a missing upper-right characteristic rectangle and retain both old pieces. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem intervalSplice_property {V W : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hV : 0 ≤ V) (hW : 0 ≤ W) (f : C(Icc 0 V, E)) (g : C(Icc 0 W, E))
    (hm : f ⟨V, hV, le_rfl⟩ = g ⟨0, le_rfl, hW⟩) {P : E → Prop}
    (hf : ∀ t, P (f t)) (hg : ∀ t, P (g t)) : ∀ t, P (intervalSplice hV hW f g t) := by
  intro t
  by_cases ht : (t : ℝ) ≤ V
  · let s : Icc 0 V := ⟨t, t.property.1, ht⟩
    have he : intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V + W by linarith) s = t :=
      Subtype.ext (by simp [intervalTranslate, s])
    rw [← he, intervalSplice_left]
    exact hf s
  · let s : Icc 0 W := ⟨t - V, by linarith, by linarith [t.property.2]⟩
    have he : intervalTranslate hV (le_refl (V + W)) s = t := Subtype.ext (by dsimp [intervalTranslate, s]; ring)
    rw [← he, intervalSplice_right_of_match hV hW _ _ hm]
    exact hg s

theorem intervalSplice_reconstruct {V W : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hV : 0 ≤ V) (hW : 0 ≤ W) (f : C(Icc 0 (V + W), E)) :
    intervalSplice hV hW (f.comp (intervalTranslate (a := 0) le_rfl (by linarith)))
      (f.comp (intervalTranslate hV le_rfl)) = f := by
  have hm : (f.comp (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V + W by linarith))) ⟨V, hV, le_rfl⟩ =
      (f.comp (intervalTranslate hV (le_refl (V + W)))) ⟨0, le_rfl, hW⟩ := by
    apply congrArg f
    exact Subtype.ext (by simp [intervalTranslate])
  apply continuousMap_ext_adjacent hV hW
  · intro t
    rw [intervalSplice_left]
    rfl
  · intro t
    rw [intervalSplice_right_of_match hV hW _ _ hm]
    rfl

theorem exists_vertical_wave_extension (e Λ ρ M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {W V H : ℝ} (hW : 0 ≤ W) (hV : 0 ≤ V) (hH : 0 ≤ H), W ≤ d → H ≤ d →
      ∀ (zy : C(Icc 0 W, WaveVector)) (vy : C(Icc 0 V, WaveVector))
        (uy : Lp WaveVector 2 (volume.restrict (Icc 0 W))) (y : WaveState W V)
        (vOut : C(Icc 0 (V + H), WaveVector)),
        IsWaveIntegral hW hV e Λ zy vy uy y → ‖y‖ ≤ M → ‖vOut‖ ≤ M →
        (∀ u v, ρ ≤ y.1 u v 0) →
        vy = vOut.comp (intervalTranslate (a := 0) le_rfl (by linarith)) →
      ∃ z : WaveState W (V + H),
        IsWaveIntegral hW (add_nonneg hV hH) e Λ zy vOut uy z ∧
        waveTranslate (a := 0) (U := W) (b := 0) (V := V) le_rfl (by linarith)
          le_rfl (by linarith) z = y ∧
        ∀ u v, ρ / 2 ≤ z.1 u v 0 := by
  obtain ⟨δ, _hδ, hδρ, d₀, hd₀, hd₀1, hsolve⟩ := exists_local_wave_integral e Λ (ρ / 2) M M (half_pos hρ) hM hM
  obtain ⟨d₁, hd₁, _hd₁1, hpaste⟩ := exists_vertical_pasting_width e Λ (ρ / 2) (M + ρ / 2) (half_pos hρ)
  refine ⟨min d₀ d₁, lt_min hd₀ hd₁, (min_le_left _ _).trans hd₀1, ?_⟩
  intro W V H hW hV hH hWd hHd zy vy uy y vOut hy hyn hvn hyr hv
  let E := ContinuousMap.evalCLM ℝ (⟨V, hV, le_rfl⟩ : Icc 0 V) (M := WaveVector)
  let zt := ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 W) E y.1
  let ut := E.compLpL 2 (volume.restrict (Icc 0 W)) y.2.2
  let vt := vOut.comp (intervalTranslate hV (le_refl (V + H)))
  have hzt : ‖zt‖ ≤ M := (ContinuousMap.norm_le _ hM).2 (fun u =>
    ((y.1 u).norm_coe_le_norm _).trans ((y.1.norm_coe_le_norm u).trans ((norm_fst_le y).trans hyn)))
  have hEt : ‖E‖ ≤ 1 := E.opNorm_le_bound zero_le_one (fun f => by
    change ‖f ⟨V, hV, le_rfl⟩‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using f.norm_coe_le_norm ⟨V, hV, le_rfl⟩)
  have hut : ‖ut‖ ≤ M := (E.norm_compLp_le y.2.2).trans
    ((mul_le_mul_of_nonneg_right hEt (norm_nonneg y.2.2)).trans (by
      simpa only [one_mul] using ((norm_snd_le y.2).trans (norm_snd_le y)).trans hyn))
  have hvt : ‖vt‖ ≤ M := (ContinuousMap.norm_le _ hM).2 (fun v => (vOut.norm_coe_le_norm _).trans hvn)
  have hztr (u : Icc 0 W) : ρ ≤ zt u 0 := hyr u ⟨V, hV, le_rfl⟩
  obtain ⟨t, ⟨htball, ht⟩, _htuniq⟩ := hsolve hW hH (hWd.trans (min_le_left _ _)) (hHd.trans (min_le_left _ _))
    zt vt ut (fun u => (half_le_self hρ.le).trans (hztr u)) hzt hvt hut
  have htr (u : Icc 0 W) (v : Icc 0 H) : ρ / 2 ≤ t.1 u v 0 := by
    have hb := (waveSeed_ball_range zt vt ut hztr hzt hvt htball u v).1.1 0
    change ρ - δ ≤ t.1 u v 0 at hb
    linarith
  have htn : ‖t‖ ≤ M + ρ / 2 := by
    obtain ⟨hz, hw, hd⟩ := waveSeed_component_bounds zt vt ut htball
    exact norm_prod_le_iff.2 ⟨by linarith, norm_prod_le_iff.2 ⟨by linarith, by linarith⟩⟩
  have hzin := waveIteration_incoming_value hW hH e Λ zt vt ut t ht.choose
  have hdin := waveIteration_incoming_derivative hW hH e Λ zt vt ut t ht.choose
  rw [ht.choose_spec] at hzin hdin
  have hzm (u : Icc 0 W) : y.1 u ⟨V, hV, le_rfl⟩ = t.1 u ⟨0, le_rfl, hH⟩ := (hzin u).symm
  have hdm : ∀ᵐ u ∂volume.restrict (Icc 0 W), y.2.2 u ⟨V, hV, le_rfl⟩ = t.2.2 u ⟨0, le_rfl, hH⟩ := by
    filter_upwards [hdin, E.coeFn_compLpL y.2.2] with u hd he
    exact he.symm.trans hd.symm
  have hcorner : vy ⟨V, hV, le_rfl⟩ = vt ⟨0, le_rfl, hH⟩ := by
    rw [hv]
    apply congrArg vOut
    exact Subtype.ext (by simp [intervalTranslate])
  let z := waveSplice hV hH y t
  have hz := hpaste hW hV hH (hWd.trans (min_le_right _ _)) zy zt vy vt uy ut y t hy ht
    (fun u v => (half_le_self hρ.le).trans (hyr u v)) htr (by linarith) htn hzm hdm hcorner
  have hvjoin : intervalSplice hV hH vy vt = vOut := by
    rw [hv]
    exact intervalSplice_reconstruct hV hH _
  rw [hvjoin] at hz
  refine ⟨z, hz, waveSplice_restrict_left hV hH y t, fun u => ?_⟩
  exact intervalSplice_property hV hH (y.1 u) (t.1 u) (hzm u) (P := fun q : WaveVector => ρ / 2 ≤ q 0)
    (fun v => (half_le_self hρ.le).trans (hyr u v)) (htr u)

theorem exists_corner_wave_extension (e Λ ρ M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {A W V H : ℝ} (hA : 0 ≤ A) (hW : 0 ≤ W) (hV : 0 ≤ V) (hH : 0 ≤ H), W ≤ d → H ≤ d →
      ∀ (zx : C(Icc 0 A, WaveVector)) (vx : C(Icc 0 (V + H), WaveVector))
        (ux : Lp WaveVector 2 (volume.restrict (Icc 0 A))) (x : WaveState A (V + H))
        (zy : C(Icc 0 W, WaveVector)) (vy : C(Icc 0 V, WaveVector))
        (uy : Lp WaveVector 2 (volume.restrict (Icc 0 W))) (y : WaveState W V),
        IsWaveIntegral hA (add_nonneg hV hH) e Λ zx vx ux x → IsWaveIntegral hW hV e Λ zy vy uy y →
        ‖x‖ ≤ M → ‖y‖ ≤ M → (∀ u v, ρ / 2 ≤ x.1 u v 0) → (∀ u v, ρ ≤ y.1 u v 0) →
        vy = (x.2.1 ⟨A, hA, le_rfl⟩).comp (intervalTranslate (a := 0) le_rfl (by linarith)) →
        zx ⟨A, hA, le_rfl⟩ = zy ⟨0, le_rfl, hW⟩ →
      ∃ z : WaveState W (V + H),
        IsWaveIntegral hW (add_nonneg hV hH) e Λ zy (x.2.1 ⟨A, hA, le_rfl⟩) uy z ∧
        waveTranslate (a := 0) (U := W) (b := 0) (V := V) le_rfl (by linarith)
          le_rfl (by linarith) z = y ∧
        (∀ u v, ρ / 2 ≤ z.1 u v 0) ∧
        IsWaveIntegral (add_nonneg hA hW) (add_nonneg hV hH) e Λ (intervalSplice hA hW zx zy) vx
          (intervalJoinLp hW ux uy) (waveJoin hA hW x z) ∧
        waveTranslate (a := 0) (U := A) (b := 0) (V := V + H) le_rfl (by linarith)
          le_rfl (by linarith) (waveJoin hA hW x z) = x ∧
        waveTranslate (a := A) (U := W) (b := 0) (V := V + H) hA le_rfl
          le_rfl (by linarith) (waveJoin hA hW x z) = z ∧
        ∀ u v, ρ / 2 ≤ (waveJoin hA hW x z).1 u v 0 := by
  obtain ⟨d, hd, hd1, hext⟩ := exists_vertical_wave_extension e Λ ρ M hρ hM
  refine ⟨d, hd, hd1, ?_⟩
  intro A W V H hA hW hV hH hWd hHd zx vx ux x zy vy uy y hx hy hxn hyn hxr hyr hv hc
  have hvn : ‖x.2.1 ⟨A, hA, le_rfl⟩‖ ≤ M :=
    (x.2.1.norm_coe_le_norm _).trans (((norm_fst_le x.2).trans (norm_snd_le x)).trans hxn)
  obtain ⟨z, hz, hb, hzr⟩ := hext hW hV hH hWd hHd zy vy uy y _ hy hyn hvn hyr hv
  have hm := hx.horizontal_match hz rfl hc
  refine ⟨z, hz, hb, hzr, hx.join_of_data hz rfl hc,
    waveJoin_restrict_left hA hW x z, waveJoin_restrict_right hA hW x z hm.1 hm.2, ?_⟩
  exact intervalSplice_property hA hW x.1 z.1 hm.1
    (P := fun q : C(Icc 0 (V + H), WaveVector) => ∀ v, ρ / 2 ≤ q v 0) hxr hzr

end CauchyHorizon
