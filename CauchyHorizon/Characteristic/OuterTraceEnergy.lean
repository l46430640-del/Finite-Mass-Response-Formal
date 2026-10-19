import CauchyHorizon.Characteristic.OuterEnergyBound
import CauchyHorizon.Characteristic.ArrivalEnergy
import CauchyHorizon.Reduced.ScalarRegularity

/-! Both actual scalar radiation traces on one fixed-radius curve have uniform energy. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_outer_trace_energy (G : Background) {s H dH A b k : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event)
    (hA : 0 ≤ A) (hb : 0 < b) (hb1 : b < 1) (hcrit : k = G.outerRate * b) (hks : k < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀) :
    let hi := horizon_mass_integrable hs hH hc hout
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y T η E₀ E₁ E₂ E₃ : ℝ, 0 < δ ∧ δ ≤ Δ₀ ∧ δ ≤ r 0 / 4 ∧ Y ∈ Ioo G.inner G.event ∧
      0 ≤ T ∧ 0 < η ∧ 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ 0 ≤ E₂ ∧ 0 ≤ E₃ ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (B : ℝ →ᵇ ℝ)
        (_hB : Integrable (fun t => B t ^ 2))
        (_hf : MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 δ))),
        (eLpNorm (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        k ≤ G.outerRate * (1 - 1 / p.toReal) →
        ∃ g : ℝ → ℝ, ContinuousOn g (Ioi T) ∧ StrictAntiOn g (Ioi T) ∧ Tendsto g atTop (𝓝 0) ∧
          (∀ t ∈ Ioi T, 0 < g t ∧ g t * Real.exp (G.outerRate * t) ≤ δ ∧
            DifferentiableAt ℝ g t ∧ η ≤ -deriv g t / g t) ∧
          (∀ l w : ℝ, T < l → l ≤ w →
            (∫ t in l..w, (g t * Real.exp (k * t) * (r 0 - g t) *
              logarithmicIncoming b ℓ B (g t)) ^ 2) ≤ E₂ * ∫ t, B t ^ 2) ∧
          ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0) (_hUδ : U ≤ δ)
            (hfU : MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 U)))
            (x : WaveState U V)
            (hx : IsWaveIntegral hU hV G.charge G.cosmological
              (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x)
            (l w : ℝ), T < l → l ≤ w → w ≤ V → g l ≤ U →
            let C := scalarTransportCorrection hV (radialNuField hV G.charge G.cosmological
              (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose) x.2.1
            (∀ t ∈ Icc l w, intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 = Y) ∧
              ((∫ t in l..w, (Real.exp (k * t) *
                (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                  intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1)) ^ 2) ≤
                    E₀ + E₁ * ∫ t, B t ^ 2) ∧
              ((∫ t in l..w, (g t * Real.exp (k * t) *
                intervalExtension hV (intervalExtension hU C (g t)) t) ^ 2) ≤
                  E₃ * (E₀ + E₁ * ∫ t, B t ^ 2)) ∧
              (∫ t in l..w, (g t * Real.exp (k * t) *
                (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                  derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                    (Icc 0 U) (g t))) ^ 2) ≤
                      2 * E₃ * E₀ + 2 * (E₂ + E₃ * E₁) * ∫ t, B t ^ 2 := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hout
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hout hrb
  have hk : 0 < k := by rw [hcrit]; exact mul_pos G.outerRate_pos hb
  have hka : k < G.outerRate := by rw [hcrit]; nlinarith only [G.outerRate_pos, hb1]
  let ρ := (G.event - dH) / 2
  have hρ : 0 < ρ := half_pos (sub_pos.2 hdHR)
  obtain ⟨W₀, hW₀, haxis₀⟩ := G.horizon_radius_lambda_bounds hs hH hdH hdHR hout hrdec
  have haxis (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : r t ∈ Icc (2 * ρ) (G.event + dH) := by
    have hh := (haxis₀ t ht).1
    exact ⟨by dsimp only [ρ]; linarith only [hh.1], hh.2⟩
  have hlout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      |horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological| ≤ W₀ :=
    (haxis₀ t ht).2.trans (mul_le_of_le_one_right hW₀ (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) ht)))
  obtain ⟨nH, NH, hnH, _hnH1, hNH, hνaxis⟩ := hOut.nu_bounds hs hc hi hrc hr0
  obtain ⟨Δ, L, D, hΔ, _hΔ1, _hΔr, _hL, _hD, henergy⟩ := exists_horizon_outer_energy_bound
    hc hi hrc hr0 hφ hrd G.outerRate_pos hb hb1 hcrit hks hρ
    hnH (zero_lt_one.trans_le hNH) hH hW₀ hA haxis hνaxis
    (fun t _ => by simpa only [Real.norm_eq_abs] using hout t) hlout
  obtain ⟨δ, Y, T, j, J, η, Q, ε, hδ, hδcap, hδr, hY, hT, _hj, hJ, hJδ, hη, _hQ, _hε, hsolve⟩ :=
    G.exists_outer_arrival_le hs hH hdH hdHR hc hout hrc hrb hrd hrdec hOut hk.le hka hks.le hA
      (min Δ Δ₀) (lt_min hΔ hΔ₀)
  have hδΔ : δ ≤ Δ := hδcap.trans (min_le_left _ _)
  let E₀ := 4 * H ^ 2 / (s - k)
  let E₁ := 8 * L ^ 2 * Δ ^ (2 * b) / G.outerRate
  let E₂ := (b * r 0 * J ^ b) ^ 2 / η
  let E₃ := (D / (G.outerRate - k)) ^ 2
  refine ⟨δ, Y, T, η, E₀, E₁, E₂, E₃, hδ, hδcap.trans (min_le_right _ _), hδr, hY, hT, hη,
    div_nonneg (by positivity) (sub_pos.2 hks).le,
    div_nonneg (by positivity) G.outerRate_pos.le, div_nonneg (sq_nonneg _) hη.le, sq_nonneg _, ?_⟩
  intro p hp ℓ B hB hf hfn hkp
  obtain ⟨g, inv, hgc, hga, hgl, _hic, _hil, _hir, _hil', hpoint⟩ :=
    hsolve p hp (logarithmicIncoming b ℓ B) hf hfn hkp
  have hdiff (t : ℝ) (ht : t ∈ Ioi T) : DifferentiableAt ℝ g t := by
    obtain ⟨W, Z, hW, hZ, hWR, hfW, z, hz, u, v,
      _hu, _hv, _hui, _hvi, _hr, _hw, hd, _hjac⟩ := (hpoint t ht).2.2.2.2.2
    exact hd.differentiableAt
  have hJd : J ≤ δ := hJδ.le.trans (half_le_self hδ.le)
  have hgr (t : ℝ) (ht : t ∈ Ioi T) : g t ≤ r 0 := by
    have hpt := hpoint t ht
    have he : 1 ≤ Real.exp (G.outerRate * t) := Real.one_le_exp_iff.2
      (mul_nonneg G.outerRate_pos.le (hT.trans ht.le))
    have hh := (le_mul_of_one_le_right hpt.1.le he).trans (hpt.2.2.1.trans hJd)
    have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
    linarith only [hh, hδr, hrp]
  have hdirect (l w : ℝ) (hl : T < l) (hw : l ≤ w) :
      (∫ t in l..w, (g t * Real.exp (k * t) * (r 0 - g t) *
        logarithmicIncoming b ℓ B (g t)) ^ 2) ≤ E₂ * ∫ t, B t ^ 2 := by
    have hsub : Icc l w ⊆ Ioi T := fun _ ht => hl.trans_le ht.1
    exact logarithmicIncoming_trace_energy hw hb hJ hη hcrit (hgc.mono hsub)
      (fun t ht => hdiff t (hsub ht)) (fun t ht => (hpoint t (hsub ht)).1)
      (fun t ht => hgr t (hsub ht)) (fun t ht => (hpoint t (hsub ht)).2.2.1)
      (fun t ht => (hpoint t (hsub ht)).2.2.2.1) B hB
  refine ⟨g, hgc, hga, hgl, fun t ht =>
    ⟨(hpoint t ht).1, (hpoint t ht).2.2.1.trans hJd, hdiff t ht, (hpoint t ht).2.2.2.1⟩, hdirect, ?_⟩
  · intro U V hU hV hUR hUδ hfU x hx l w hl hlw hwV hglU
    let C := scalarTransportCorrection hV (radialNuField hV G.charge G.cosmological
      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose) x.2.1
    have hsub : Icc l w ⊆ Ioi T := fun _ ht => hl.trans_le ht.1
    have hgu (t : ℝ) (ht : t ∈ Icc l w) : g t ∈ Icc 0 U :=
      ⟨(hpoint t (hsub ht)).1.le, (hga.antitoneOn hl (hsub ht) ht.1).trans hglU⟩
    have htv (t : ℝ) (ht : t ∈ Icc l w) : t ∈ Icc (0 : ℝ) V :=
      ⟨(hT.trans hl.le).trans ht.1, ht.2.trans hwV⟩
    have hwidth (t : ℝ) (ht : t ∈ Icc l w) : g t ≤ Δ * Real.exp (-G.outerRate * t) := by
      have hh := mul_le_mul_of_nonneg_right ((hpoint t (hsub ht)).2.2.1.trans (hJd.trans hδΔ))
        (Real.exp_pos (-G.outerRate * t)).le
      simpa only [mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one] using hh
    have hactual := henergy U V hU hV hUR p hp ℓ B hB hfU x hx
      ((scalar_prefix_norm_le hUδ hf).trans hfn) hkp
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨W, Z, hW, hZ, hWR, hfW, z, hz, u, v, hu, hv, _hui, _hvi, hhit, _hw, _hd, _hjac⟩ :=
        (hpoint t (hsub ht)).2.2.2.2.2
      have huW : g t ∈ Icc 0 W := by rw [← hu]; exact u.property
      have hvZ : t ∈ Icc 0 Z := by rw [← hv]; exact v.property
      have ho := hz.horizon_overlap hW hZ hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
        huW (hgu t ht) hvZ (htv t ht)
      have hh : z.1 ⟨g t, huW⟩ ⟨t, hvZ⟩ 0 = Y := by
        rw [show (⟨g t, huW⟩ : Icc 0 W) = u from Subtype.ext hu.symm,
          show (⟨t, hvZ⟩ : Icc 0 Z) = v from Subtype.ext hv.symm]
        exact hhit
      rw [intervalExtension_apply, intervalExtension_apply, projIcc_of_mem hU (hgu t ht),
        projIcc_of_mem hV (htv t ht)]
      exact (congrArg (fun q : WaveVector => q 0) ho.1).symm.trans hh
    · have hh := outerRadiationEnvelope_curve_energy (k := k) hU hV hΔ.le (hT.trans hl.le) hlw hwV
        x (hgc.mono hsub) hgu hwidth
      exact hh.trans hactual.1
    · have hcorr : (∫ t in l..w, (g t * Real.exp (k * t) *
          intervalExtension hV (intervalExtension hU C (g t)) t) ^ 2) ≤
            E₃ * (E₀ + E₁ * ∫ t, B t ^ 2) := by
        let F := fun t => g t * Real.exp (k * t) *
          intervalExtension hV (intervalExtension hU C (g t)) t
        have hFc : ContinuousOn F (Icc l w) := by
          have hgc' := hgc.mono hsub
          dsimp only [F]
          fun_prop
        have hh := causalExpIntegral_dominated_energy hV (sub_pos.2 hka)
          (hT.trans hl.le) hlw hwV (outerRadiationEnvelope hΔ.le G.outerRate k x) hFc
          (C := D) (fun t ht => ?_)
        · exact hh.trans (mul_le_mul_of_nonneg_left hactual.1 (sq_nonneg _))
        · have hbnd := hactual.2 ⟨g t, hgu t ht⟩ ⟨t, htv t ht⟩ (hwidth t ht)
          simpa only [F, C, abs_mul, abs_of_nonneg (hgu t ht).1, abs_of_pos (Real.exp_pos _),
            intervalExtension_apply, projIcc_of_mem hU (hgu t ht), projIcc_of_mem hV (htv t ht)] using hbnd
      refine ⟨hcorr, ?_⟩
      have hfc : ContinuousOn (logarithmicIncoming b ℓ B) (Ioi 0) := by
        apply ContinuousOn.mul
        · exact continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl ht.ne'))
        · exact B.continuous.comp_continuousOn
            (continuousOn_const.sub (continuousOn_id.log (fun t ht => ht.ne')))
      have hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hfU u 0 = -1 := by
        filter_upwards [incomingWaveVelocity_ae hUR hp hfU] with u hu
        rw [hu]
        rfl
      have hif : ∀ᵐ u ∂volume.restrict (Icc 0 U),
          incomingWaveVelocity hUR hp hfU u 1 = logarithmicIncoming b ℓ B u := by
        filter_upwards [incomingWaveVelocity_ae hUR hp hfU] with u hu
        rw [hu]
        rfl
      have hin : (∫ t in l..w, (g t * Real.exp (k * t) *
          incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0) (projIcc 0 U hU (g t)) 0 *
            logarithmicIncoming b ℓ B (g t)) ^ 2) ≤ E₂ * ∫ t, B t ^ 2 := by
        convert hdirect l w hl hlw using 1
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hlw] at ht
        simp only [projIcc_of_mem hU (hgu t ht), incomingWaveCurve_apply, incomingRadius,
          Matrix.cons_val_zero]
      have hh := hx.scalar_curve_energy rfl hinu hfc hif hlw (hgc.mono hsub)
        (fun t ht => ⟨(hpoint t (hsub ht)).1, (hgu t ht).2⟩) hin hcorr
      exact hh.trans_eq (by ring)

end CauchyHorizon.Background
