import CauchyHorizon.Characteristic.CompactBandNormalization

/-! A single inner arrival curve normalizes bands with any outer radius below the event horizon. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_band_normalization_to_event (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ T : ℝ, ∃ τ σ : Ioi (0 : ℝ) → ℝ,
          0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ (∀ ε, T ≤ τ ε) ∧ (∀ W, T ≤ σ W) ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
            MemLp f p (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∃ g : ℝ → ℝ,
              ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧ Tendsto g atTop (𝓝 0) ∧
              (∀ t ∈ Ici T, 0 < g t) ∧
              (∀ (W : Ioi (0 : ℝ)) (t : ℝ), σ W ≤ t → g t < W) ∧
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
                ∀ (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
                  (hx : IsWaveIntegral hU hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR hp hfU) x),
                  (∀ v : Icc 0 V, T ≤ (v : ℝ) → g v ≤ U →
                    ∀ y ∈ Icc Y Z, ∃! u : Icc 0 U,
                      0 < (u : ℝ) ∧ (u : ℝ) ≤ g v ∧ x.1 u v 0 = y) ∧
                  ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
                    (u : ℝ) ≤ g v → x.1 u v 0 ≤ Z →
                    let ν := radialNuField hV B.charge B.cosmological
                      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                    x.1 u v 0 ∈ Icc Y Z ∧ ∀ ε : Ioi (0 : ℝ), τ ε ≤ (v : ℝ) →
                      |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F (x.1 u v 0)))| +
                        |Real.log (B.z (x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (B.outerRate * v))))| +
                          |x.2.1 u v 0 / ((u : ℝ) * ν u v) - B.outerRate| < ε := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let c := min s a / 2
  have hc0 : 0 < c := half_pos (lt_min hs ha)
  have hca : c < a := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  have hcs : c ≤ s := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (half_le_self hs.le)
  have hcHalf : c ≤ a / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨δ, R, hδ, hδr, hR, _hRr, hdomain⟩ := B.exists_band_radiation_domain
    hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, TY, _jY, D, _ηY, _CY, N, _LY,
    hU₀, hUδ, hTY, _hjY, hD, _hηY, _hCY, hN, _hLY, hsolve⟩ := hdomain Y hY hYR
  let j := (B.event - Z) / (2 * N)
  have hj : 0 < j := div_pos (sub_pos.2 hZ) (mul_pos (by norm_num) hN)
  have hnorm (ε : Ioi (0 : ℝ)) := B.exists_compact_prefix_normalization
    hs hH hdH hdHR hA hY hYZ.le hZ hj hD hc hb hrc hrb hrd hrdec hOut ε ε.property
  choose τ₀ _hτ₀ hnorm using hnorm
  have hdec : Tendsto (fun t : ℝ => dH * Real.exp (-(2 * s) * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith only [hs] : -(2 * s) < 0))).const_mul dH
  obtain ⟨TZ, hTZ⟩ := eventually_atTop.1 (hdec.eventually_lt_const (half_pos (sub_pos.2 hZ)))
  let T := max TY TZ
  have haxis (t : ℝ) (ht : T ≤ t) : (B.event + Z) / 2 < r t := by
    have he := hrdec t (hTY.le.trans ((le_max_left _ _).trans ht))
    rw [Real.norm_eq_abs] at he
    have hlo := (abs_le.1 he).1
    have hh := hTZ t ((le_max_right _ _).trans ht)
    linarith only [hlo, hh]
  have hzero : Tendsto (fun t : ℝ => D * Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha))).const_mul D
  have hentry (W : Ioi (0 : ℝ)) := eventually_atTop.1 (hzero.eventually_lt_const W.property)
  choose σ₀ hσ₀ using hentry
  refine ⟨U₀, T, (fun ε => max T (τ₀ ε)), (fun W => max T (σ₀ W)), hU₀, hUδ,
    hTY.trans_le (le_max_left _ _), (fun _ => le_max_left _ _), (fun _ => le_max_left _ _), ?_⟩
  intro p hp f hf hfn
  have hcp : c ≤ a * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le
    linarith only [hcHalf, hh, ha]
  obtain ⟨g, hgc, hga, hgl, _hgdc, _hgstart, hpoint, hphysical⟩ := hsolve p hp f hf hfn hcp
  have hsub : Ici T ⊆ Ici TY := fun _ ht => (le_max_left TY TZ).trans ht
  refine ⟨g, hgc.mono hsub, hga.mono hsub, hgl, fun t ht => (hpoint t (hsub ht)).1.1, ?_, ?_⟩
  · intro W t ht
    have hh := mul_le_mul_of_nonneg_right (hpoint t (hsub ((le_max_left _ _).trans ht))).2.1
      (Real.exp_pos (-a * t)).le
    have he : g t ≤ D * Real.exp (-a * t) := by
      simpa only [a, mul_assoc, ← Real.exp_add, show B.outerRate * t + -B.outerRate * t = 0 by ring,
        Real.exp_zero, mul_one] using hh
    exact he.trans_lt (hσ₀ W t ((le_max_right _ _).trans ht))
  intro U V hU hV hUR hUU hfU x hx
  have hphys := hphysical U V hU hV hUR hUU hfU x hx
  have hanti (v : Icc 0 V) := hx.radial_strictAnti hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hfU (horizonPhi h r 0)).1 v
    (fun q => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU q v).2.2.1)
  refine ⟨?_, ?_⟩
  · intro v hv hgv y hyz
    have hg : g v ∈ Icc 0 U := ⟨(hpoint v (hsub hv)).1.1.le, hgv⟩
    have hhit := hphys.2.1 v ⟨hsub hv, v.property.2⟩ hgv
    have htr := (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hfU).2 v
    have htr0 : x.1 ⟨0, le_rfl, hU⟩ v 0 = r v := by rw [htr]; rfl
    simp only [intervalExtension_apply, projIcc_of_mem hV v.property] at hhit
    have haxisv : y < r v := by linarith only [hyz.2, haxis v hv, hZ]
    have hcR : Continuous (fun t => intervalExtension hU x.1 t v 0) := by fun_prop
    have hyR : y ∈ Icc (intervalExtension hU x.1 (g v) v 0)
        (intervalExtension hU x.1 0 v 0) := by
      simpa only [mem_Icc, intervalExtension_apply, hhit,
        projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩), htr0] using
          And.intro hyz.1 haxisv.le
    obtain ⟨q, hq, heq⟩ := intermediate_value_Icc' hg.1 hcR.continuousOn hyR
    have hqU : q ∈ Icc 0 U := ⟨hq.1, hq.2.trans hgv⟩
    have hqhit : x.1 ⟨q, hqU⟩ v 0 = y := by
      simpa only [intervalExtension_apply, projIcc_of_mem hU hqU] using heq
    have hqpos : 0 < q := by
      by_contra hn
      have hq0 : q = 0 := le_antisymm (not_lt.1 hn) hq.1
      subst q
      exact haxisv.ne (hqhit.symm.trans htr0)
    exact ⟨⟨q, hqU⟩, ⟨hqpos, hq.2, hqhit⟩,
      fun w hw => (hanti v).injective (hw.2.2.trans hqhit.symm)⟩
  intro u v hv hug hrZ
  have hvY : TY ≤ (v : ℝ) := hsub hv
  have hfloor : Y ≤ x.1 u v 0 := by
    apply (hphys.1 u v ?_).1
    simpa only [max_eq_right hvY] using hug
  refine ⟨⟨hfloor, hrZ⟩, ?_⟩
  intro ε hεv
  let hf' := hfU.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
  let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (v : ℝ))
    le_rfl (by simpa only [zero_add] using u.property.2) le_rfl (by simpa only [zero_add] using v.property.2) x
  have hy := hx.horizon_prefix hU hV hUR u.property.1 v.property.1 u.property.2 v.property.2 hc hi hrc hr0 hp hfU
  let uu : Icc 0 (u : ℝ) := ⟨u, u.property.1, le_rfl⟩
  let vv : Icc 0 (v : ℝ) := ⟨v, v.property.1, le_rfl⟩
  have hpre := hphysical u v u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    (u.property.2.trans hUU) hf' y hy
  have hdom (q : Icc 0 (u : ℝ)) (w : Icc 0 (v : ℝ)) : (q : ℝ) ≤ g (max TY (w : ℝ)) :=
    q.property.2.trans (hug.trans
      (hga.antitoneOn (le_max_left TY (w : ℝ))
        hvY (max_le hvY w.property.2)))
  have he := hy.horizon_overlap u.property.1 v.property.1 (u.property.2.trans_lt hUR) hU hV hUR
    hc hi hrc hr0 hp hf' hfU hx uu.property u.property vv.property v.property
  have hne := hy.horizon_overlap_nu u.property.1 v.property.1 (u.property.2.trans_lt hUR) hU hV hUR
    hc hi hrc hr0 hp hf' hfU hx uu.property u.property vv.property v.property
  have hhit : y.1 uu vv 0 ≤ Z := by rw [he.1]; exact hrZ
  have hg := hy.radial_gap_weighted_bound hy.choose rfl
    (incomingWave_constraint_data u.property.1 (u.property.2.trans_lt hUR) hp hf' (horizonPhi h r 0)).1
    (fun q w => (hy.interior_gauge u.property.1 v.property.1 (u.property.2.trans_lt hUR)
      hc hi hrc hr0 hφ hrd hp hf' q w).2.2.1.le)
    (fun q w => (hpre.1 q w (hdom q w)).2.1) uu vv
  have htr := (hy.horizon_traces u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    hc hi hrc hr0 hφ hrd hp hf').2 vv
  rw [htr] at hg
  have hgap := hg.2
  change r (v : ℝ) - y.1 uu vv 0 ≤ N * (u : ℝ) * Real.exp (B.outerRate * (v : ℝ)) at hgap
  have hjwidth : j ≤ (uu : ℝ) * Real.exp (B.outerRate * (v : ℝ)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hN)).2
    nlinarith only [hgap, hhit, haxis v hv]
  have hwidth := (mul_le_mul_of_nonneg_right hug (Real.exp_pos _).le).trans (hpoint v (hsub hv)).2.1
  have hnormf := (scalar_prefix_norm_le (u.property.2.trans (hUU.trans hUδ)) hf).trans hfn
  have hh := hnorm ε u v u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    p hp f hf' y hy hnormf ((le_max_right _ _).trans hεv)
    (fun q w => (hpre.1 q w (hdom q w)).1) hwidth uu hjwidth hhit
  rw [he.1, he.2, hne] at hh
  exact hh

end CauchyHorizon.Background
