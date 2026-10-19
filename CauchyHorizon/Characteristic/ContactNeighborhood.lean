import CauchyHorizon.Characteristic.RadiusCrossing
import Mathlib.Analysis.Calculus.MeanValue

/-! Nearby wider first-contact prefixes provide an interior physical neighborhood. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem IsWaveIntegral.exists_contact_neighborhood {M e Λ U T Umax Y A a N : ℝ} {h r : ℝ → ℝ}
    (hU : 0 < U) (hT : 0 < T) (hUR : U < r 0) (hUU : U < Umax) (hUmax1 : Umax ≤ 1)
    (hUmaxR : Umax < r 0) (hY : 0 < Y) (hA : 0 ≤ A) (ha : 0 ≤ a) (hN : 0 < N)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 Umax)))
    (hfn : (eLpNorm f p (volume.restrict (Icc 0 Umax))).toReal ≤ A)
    (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U T}
    (hx : IsWaveIntegral hU.le hT.le e Λ (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ T hc hi hrc hr0) (incomingWaveVelocity hUR hp hfU) x)
    (hhit : x.1 ⟨U, hU.le, le_rfl⟩ ⟨T, hT.le, le_rfl⟩ 0 = Y)
    (hfirst : ∀ (u : Icc 0 U) (v : Icc 0 T), (v : ℝ) < T → Y < x.1 u v 0)
    (hfamily : ∀ (W : ℝ) (hW : 0 ≤ W) (hWR : W < r 0) (hfW : MemLp f p (volume.restrict (Icc 0 W))),
      W ∈ Ioc U Umax → ∃ S : ℝ, ∃ hS : 0 < S, ∃ y : WaveState W S,
        ∃ hy : IsWaveIntegral hW hS.le e Λ (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ S hc hi hrc hr0) (incomingWaveVelocity hWR hp hfW) y,
        (∀ u v, Y ≤ y.1 u v 0) ∧ y.1 ⟨W, hW, le_rfl⟩ ⟨S, hS.le, le_rfl⟩ 0 = Y ∧
        (∀ (u : Icc 0 W) (v : Icc 0 S), (v : ℝ) < S → Y < y.1 u v 0) ∧
        ∀ u, -radialNuField hS.le e Λ (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
          y.1 hy.choose u ⟨S, hS.le, le_rfl⟩ ≤ N * Real.exp (a * S)) :
    ∃ W V : ℝ, ∃ hW : 0 ≤ W, ∃ hV : 0 ≤ V, ∃ hWR : W < r 0,
      ∃ hfW : MemLp f p (volume.restrict (Icc 0 W)), ∃ z : WaveState W V,
        IsWaveIntegral hW hV e Λ (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hWR hp hfW) z ∧
        U < W ∧ W ≤ Umax ∧ T < V ∧ (∀ u v, Y / 2 ≤ z.1 u v 0) := by
  obtain ⟨d, hd, hd1, hext⟩ := exists_horizon_row_extension (Vmax := T + 1) (by linarith)
    (hU.trans hUR) hc hi hrc hr0 hφ hrd hY hA
  let b := max 0 (T - d / 2)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hbT : b < T := max_lt hT (by linarith only [hd])
  let g : ℝ → ℝ := fun t => intervalExtension hT.le (x.1 ⟨U, hU.le, le_rfl⟩) t 0 - Y
  have hgc : Continuous g := by fun_prop
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) b)).exists_isMinOn
    (nonempty_Icc.2 hb0) hgc.continuousOn
  let ε := g t₀
  have hε : 0 < ε := by
    have htT : t₀ ∈ Icc 0 T := ⟨ht₀.1, ht₀.2.trans hbT.le⟩
    have hh := hfirst ⟨U, hU.le, le_rfl⟩ ⟨t₀, htT⟩ (ht₀.2.trans_lt hbT)
    simpa only [ε, g, intervalExtension_apply, projIcc_of_mem hT.le htT, sub_pos] using hh
  let η := min ((Umax - U) / 2) (ε / (2 * N * Real.exp (a * T)))
  have hη : 0 < η := by dsimp only [η]; positivity
  let W := U + η
  have hUW : U < W := by dsimp only [W]; linarith only [hη]
  have hW : 0 ≤ W := (hU.trans hUW).le
  have hWmax : W ≤ Umax := by
    have hh : η ≤ (Umax - U) / 2 := min_le_left _ _
    dsimp only [W]
    linarith only [hh, hUU]
  have hWR := hWmax.trans_lt hUmaxR
  let hfW := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hWmax) le_rfl)
  obtain ⟨S, hS, y, hy, hfloor, hyhit, hyfirst, hν⟩ := hfamily W hW hWR hfW ⟨hUW, hWmax⟩
  have hST : S < T := (hy.first_contact_time_order hW hS.le hWR hU.le hT.le hUR hUW.le
    hc hi hrc hr0 hφ hrd hp hfW hfU hx hyhit hyfirst hhit).2 hUW
  let ν := radialNuField hS.le e Λ (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) y.1 hy.choose
  let vS : Icc 0 S := ⟨S, hS.le, le_rfl⟩
  let rad : ℝ → ℝ := fun w => intervalExtension hW y.1 w vS 0
  have hdiff : rad U - rad W ≤ (N * Real.exp (a * S)) * (W - U) := by
    have hdif (w : ℝ) (hw : w ∈ Icc U W) : HasDerivWithinAt rad
        (intervalExtension hW ν w vS) (Icc U W) w := by
      have hw' : w ∈ Icc 0 W := ⟨hU.le.trans hw.1, hw.2⟩
      have hh := (hy.radial_hasDerivWithinAt hy.choose rfl
        (incomingWave_constraint_data hW hWR hp hfW (horizonPhi h r 0)).1 vS hw').mono
        (Icc_subset_Icc hU.le le_rfl)
      simpa only [rad, ν, intervalExtension_apply, projIcc_of_mem hW hw'] using hh
    have hbnd (w : ℝ) (hw : w ∈ Icc U W) : ‖intervalExtension hW ν w vS‖ ≤ N * Real.exp (a * S) := by
      have hw' : w ∈ Icc 0 W := ⟨hU.le.trans hw.1, hw.2⟩
      simp only [Real.norm_eq_abs, intervalExtension_apply, projIcc_of_mem hW hw']
      rw [abs_of_neg (hy.interior_gauge hW hS.le hWR hc hi hrc hr0 hφ hrd hp hfW ⟨w, hw'⟩ vS).2.2.1]
      exact hν ⟨w, hw'⟩
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hdif hbnd (convex_Icc _ _)
      (left_mem_Icc.2 hUW.le) (right_mem_Icc.2 hUW.le)
    simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hUW.le)] at hh
    exact (show rad U - rad W ≤ |rad W - rad U| by rw [abs_sub_comm]; exact le_abs_self _).trans hh
  have hsmall : (N * Real.exp (a * S)) * (W - U) ≤ ε / 2 := by
    have he := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hST.le ha)
    have heN := mul_le_mul_of_nonneg_left he hN.le
    have hηb : η ≤ ε / (2 * N * Real.exp (a * T)) := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * N * Real.exp (a * T))).1 hηb
    have hm := mul_le_mul_of_nonneg_right heN hη.le
    change (N * Real.exp (a * S)) * ((U + η) - U) ≤ ε / 2
    nlinarith only [hh, hm]
  have hSb : b < S := by
    by_contra hnot
    have hSb' : S ≤ b := le_of_not_gt hnot
    have he := (hx.horizon_overlap hU.le hT.le hUR hW hS.le hWR hc hi hrc hr0 hp hfU hfW hy
      ⟨hU.le, le_rfl⟩ ⟨hU.le, hUW.le⟩ ⟨hS.le, hST.le⟩ ⟨hS.le, le_rfl⟩).1
    have heq : g S = rad U - rad W := by
      simp only [g, rad, vS, intervalExtension_apply,
        projIcc_of_mem hT.le (show S ∈ Icc 0 T from ⟨hS.le, hST.le⟩),
        projIcc_of_mem hW (show U ∈ Icc 0 W from ⟨hU.le, hUW.le⟩),
        projIcc_of_mem hW (show W ∈ Icc 0 W from ⟨hW, le_rfl⟩), he, hyhit]
    have hh := hmin (show S ∈ Icc (0 : ℝ) b from ⟨hS.le, hSb'⟩)
    change ε ≤ g S at hh
    rw [heq] at hh
    linarith only [hh, hdiff, hsmall, hε]
  have hTV : T < S + d := by
    have hh : T - d / 2 ≤ b := le_max_right _ _
    linarith only [hh, hSb, hd]
  obtain ⟨z, hz, _hmatch, hzfloor⟩ := hext hW hS.le hd.le (hWmax.trans hUmax1) le_rfl
    (by linarith only [hST, hd1]) hWR hp hfW ((scalar_prefix_norm_le hWmax hf).trans hfn) hy hfloor
  exact ⟨W, S + d, hW, add_nonneg hS.le hd.le, hWR, hfW, z, hz, hUW, hWmax, hTV, hzfloor⟩

end CauchyHorizon
