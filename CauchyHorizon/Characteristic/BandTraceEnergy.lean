import CauchyHorizon.Characteristic.BandRadiationDomain
import CauchyHorizon.Characteristic.SpatialEnergy
import CauchyHorizon.Reduced.ScalarRegularity
import CauchyHorizon.Analysis.ArrivalEnergy

/-! Both actual radiation traces have uniform energy at every sufficiently inner matching radius. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 2000000 in
theorem exists_band_trace_energy (G : Background) {s H dH A b k : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event)
    (hA : 0 ≤ A) (hb : 0 < b) (hb1 : b < 1) (hcrit : k = G.outerRate * b) (hks : k < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t) (hrinit : G.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hout
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo G.inner G.event ∧ R < r 0 ∧
      ∀ Y : ℝ, G.inner < Y → Y ≤ R → ∃ U₀ T j D η C E₀ E₁ E₂ E₃ : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ 0 < j ∧ 0 < D ∧ 0 < η ∧ 0 < C ∧
        0 ≤ E₀ ∧ 0 ≤ E₁ ∧ 0 ≤ E₂ ∧ 0 ≤ E₃ ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (B : ℝ →ᵇ ℝ),
          Integrable (fun t => B t ^ 2) →
          MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 δ)) →
          (eLpNorm (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 δ))).toReal ≤ A →
          k ≤ G.outerRate * (1 - 1 / p.toReal) →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧ Tendsto g atTop (𝓝 0) ∧
            ContinuousOn (deriv g) (Ici T) ∧ U₀ < g T ∧
            (∀ t ∈ Ici T, g t ∈ Ioo 0 (r 0) ∧ g t * Real.exp (G.outerRate * t) ≤ D ∧
              DifferentiableAt ℝ g t ∧ η ≤ -deriv g t / g t ∧
              j ≤ g t * Real.exp (G.outerRate * t) ∧ -deriv g t / g t ≤ C) ∧
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 U)))
                (x : WaveState U V)
                (hx : IsWaveIntegral hU hV G.charge G.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x),
                ∃ (w : C(Icc 0 V, ℝ)) (hw0 : ∀ v, 0 ≤ w v),
                  (∀ v, w v = g (max T (v : ℝ))) ∧
                  ((∫ t in (0 : ℝ)..V,
                    (movingSpatialRadiationEnvelope w hw0 G.outerRate k 0 x (projIcc 0 V hV t)) ^ 2) ≤
                      E₀ + E₁ * ∫ t, B t ^ 2) ∧
                  (∀ (u : Icc 0 U) (v : Icc 0 V), 0 < (u : ℝ) →
                    x.1 u v 0 = Y → x.2.1 u v 0 < 0 → g v = u) ∧
                  (∀ v : Icc 0 V, T ≤ v → g v ≤ U →
                    g v * |radialNuField hV G.charge G.cosmological
                      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                        (projIcc 0 U hU (g v)) v| ≤ D) ∧
                  ∀ l q : ℝ, T ≤ l → l ≤ q → q ≤ V → g l ≤ U →
                    let C := scalarTransportCorrection hV (radialNuField hV G.charge G.cosmological
                      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose) x.2.1
                    (∀ t ∈ Icc l q, intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 = Y) ∧
                      ((∫ t in l..q, (Real.exp (k * t) *
                        (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                          intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1)) ^ 2) ≤
                            E₀ + E₁ * ∫ t, B t ^ 2) ∧
                      ((∫ t in l..q, (g t * Real.exp (k * t) *
                        intervalExtension hV (intervalExtension hU C (g t)) t) ^ 2) ≤
                          E₃ * (E₀ + E₁ * ∫ t, B t ^ 2)) ∧
                      (∫ t in l..q, (g t * Real.exp (k * t) *
                        (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                          derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                            (Icc 0 U) (g t))) ^ 2) ≤
                              2 * E₃ * E₀ + 2 * (E₂ + E₃ * E₁) * ∫ t, B t ^ 2 := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hout
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hout hrb
  have ha := G.outerRate_pos
  have hk : 0 < k := by rw [hcrit]; exact mul_pos G.outerRate_pos hb
  have hka : k < G.outerRate := by rw [hcrit]; nlinarith only [G.outerRate_pos, hb1]
  obtain ⟨δ, R, hδ, hδr, hR, hRr, hdomain⟩ := G.exists_band_radiation_domain
    hs hH hdH hdHR hA hk hka hks.le hc hout hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, hRr, ?_⟩
  intro Y hY hYR
  have hY0 := G.inner_pos.trans hY
  obtain ⟨U₀, T, j, D, η, C, N, L, hU₀, hU₀δ, hT, hj, hD, hη, hC, hN, hL, hsolve⟩ := hdomain Y hY hYR
  let σ := 1 + 4 * L * N / (Y ^ 2 * (G.outerRate - k))
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hsmall : L * N / (σ * Y ^ 2) ≤ (G.outerRate - k) / 2 := by
    apply (div_le_iff₀ (mul_pos hσ (sq_pos_of_pos hY0))).2
    have he : (G.outerRate - k) / 2 * (σ * Y ^ 2) =
        (G.outerRate - k) * Y ^ 2 / 2 + 2 * L * N := by
      dsimp only [σ]
      field_simp [(sub_pos.2 hka).ne', hY0.ne']
      ring
    rw [he]
    nlinarith only [mul_nonneg hL hN.le, mul_nonneg (sub_pos.2 hka).le (sq_nonneg Y)]
  let W := Real.exp (σ * D)
  let E₀ := W ^ 2 * (4 * H ^ 2 / (s - k))
  let E₁ := W ^ 2 * (8 * (L * r 0 / Y) ^ 2 * D ^ (2 * b) / G.outerRate)
  let E₂ := (b * r 0 * D ^ b) ^ 2 / η
  let E₃ := (N * D / Y / (G.outerRate - k)) ^ 2
  refine ⟨U₀, T, j, max D (N * D), η, C, E₀, E₁, E₂, E₃, hU₀, hU₀δ, hT, hj,
    hD.trans_le (le_max_left _ _), hη, hC,
    mul_nonneg (sq_nonneg _) (div_nonneg (by positivity) (sub_pos.2 hks).le),
    by dsimp only [E₁]; positivity, div_nonneg (sq_nonneg _) hη.le, sq_nonneg _, ?_⟩
  intro p hp ℓ B hB hf hfn hkp
  obtain ⟨g, hgc, hga, hgl, hdc, hstart, hpoint, hgeo⟩ := hsolve p hp (logarithmicIncoming b ℓ B) hf hfn hkp
  refine ⟨g, hgc, hga, hgl, hdc, hstart, fun t ht =>
    ⟨(hpoint t ht).1, (hpoint t ht).2.1.trans (le_max_left _ _), (hpoint t ht).2.2⟩, ?_⟩
  intro U V hU hV hUR hUU hfU x hx
  have hwc : Continuous (fun v : Icc 0 V => g (max T (v : ℝ))) :=
    hgc.comp_continuous (by fun_prop) (fun v => le_max_left T (v : ℝ))
  let w : C(Icc 0 V, ℝ) := ⟨fun v => g (max T (v : ℝ)), hwc⟩
  have hw0 (v : Icc 0 V) : 0 ≤ w v := (hpoint _ (show T ≤ max T (v : ℝ) from le_max_left _ _)).1.1.le
  have hw : Antitone w := by
    intro v z hvz
    exact hga.antitoneOn (le_max_left T (v : ℝ)) (le_max_left T (z : ℝ)) (max_le_max_left T hvz)
  have hscale (v : Icc 0 V) : w v * Real.exp (G.outerRate * v) ≤ D := by
    have hh := (hpoint _ (show T ≤ max T (v : ℝ) from le_max_left _ _)).2.1
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_max_right T (v : ℝ)) G.outerRate_pos.le))
      (hw0 v)).trans hh
  have hwD (v : Icc 0 V) : w v ≤ D * Real.exp (-G.outerRate * v) := by
    have hh := mul_le_mul_of_nonneg_right (hscale v) (Real.exp_pos (-G.outerRate * v)).le
    simpa only [mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one] using hh
  obtain ⟨hg, hlevel, hidentify⟩ := hgeo U V hU hV hUR hUU hfU x hx
  have hactual := hx.horizon_moving_spatial_energy hU hV hUR hc hi hrc hr0 hφ hrd
    G.outerRate_pos hb hb1 hcrit hks hY0 hN.le hL hσ hD hH hsmall
    (fun t _ => by simpa only [Real.norm_eq_abs] using hout t) w hw0 hw hwD hp ℓ B hB hfU
    (fun u v hu => (hg u v hu).1) (fun u v hu => (hg u v hu).2.1) (fun u v hu => (hg u v hu).2.2)
  let M := movingSpatialRadiationEnvelope w hw0 G.outerRate k σ x
  let M₀ := movingSpatialRadiationEnvelope w hw0 G.outerRate k 0 x
  have he : (∫ t in (0 : ℝ)..V, (M₀ (projIcc 0 V hV t)) ^ 2) ≤ E₀ + E₁ * ∫ t, B t ^ 2 :=
    hactual.2.1.trans_eq (by dsimp only [E₀, E₁, W]; ring)
  refine ⟨w, hw0, fun _ => rfl, he, hidentify, ?_, ?_⟩
  · intro v hTv hgv
    have hvU : g v ∈ Icc 0 U := ⟨(hpoint v hTv).1.1.le, hgv⟩
    have hh := (hg (projIcc 0 U hU (g v)) v (by
      rw [projIcc_of_mem hU hvU, max_eq_right hTv])).2.1
    calc
      _ ≤ g v * (N * Real.exp (G.outerRate * v)) :=
        mul_le_mul_of_nonneg_left hh hvU.1
      _ = N * (g v * Real.exp (G.outerRate * v)) := by ring
      _ ≤ N * D := mul_le_mul_of_nonneg_left (hpoint v hTv).2.1 hN.le
      _ ≤ _ := le_max_right _ _
  intro l q hl hlq hqV hglU
  let C := scalarTransportCorrection hV (radialNuField hV G.charge G.cosmological
    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose) x.2.1
  have hsub : Icc l q ⊆ Ici T := fun _ ht => hl.trans ht.1
  have hgu (t : ℝ) (ht : t ∈ Icc l q) : g t ∈ Icc 0 U :=
    ⟨(hpoint t (hsub ht)).1.1.le, (hga.antitoneOn hl (hsub ht) ht.1).trans hglU⟩
  have htv (t : ℝ) (ht : t ∈ Icc l q) : t ∈ Icc (0 : ℝ) V :=
    ⟨hT.le.trans (hsub ht), ht.2.trans hqV⟩
  have hwidth (t : ℝ) (ht : t ∈ Icc l q) : g t ≤ w ⟨t, htv t ht⟩ := by
    change g t ≤ g (max T t)
    rw [max_eq_right (hsub ht)]
  refine ⟨fun t ht => hlevel t ⟨hsub ht, ht.2.trans hqV⟩ (hgu t ht).2, ?_, ?_⟩
  · let F := fun t => Real.exp (k * t) *
      (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
        intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1)
    have hFc : ContinuousOn F (Icc l q) := by
      have hgc' := hgc.mono hsub
      dsimp only [F]
      fun_prop
    have hMc : Continuous (fun t => M₀ (projIcc 0 V hV t)) := by fun_prop
    have hbnd (t : ℝ) (ht : t ∈ Icc l q) : F t ^ 2 ≤ M₀ (projIcc 0 V hV t) ^ 2 := by
      have hh := (movingSpatialRadiationEnvelope_le_iff (a := G.outerRate) (k := k) (σ := 0)
        hU w hw0 x ⟨t, htv t ht⟩).1 le_rfl ⟨g t, hgu t ht⟩ (hwidth t ht)
      have ha : |F t| ≤ M₀ (projIcc 0 V hV t) := by
        simpa only [F, M₀, zero_mul, sub_zero, intervalExtension_apply,
          projIcc_of_mem hU (hgu t ht), projIcc_of_mem hV (htv t ht),
          abs_mul, abs_of_pos (Real.exp_pos _)] using hh
      have hM0 : 0 ≤ M₀ (projIcc 0 V hV t) :=
        norm_nonneg (movingSpatialRadiationRows w hw0 G.outerRate k 0 x _)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (F t)) hM0).2 ha
    have hh := intervalIntegral.integral_mono_on (μ := volume) hlq
      ((hFc.pow 2).intervalIntegrable_of_Icc hlq) ((hMc.pow 2).intervalIntegrable _ _) hbnd
    exact hh.trans ((intervalIntegral.integral_mono_interval (hT.le.trans hl) hlq hqV
      (Filter.Eventually.of_forall (fun t => sq_nonneg (M₀ (projIcc 0 V hV t))))
      ((hMc.pow 2).intervalIntegrable _ _)).trans he)
  · have hcorr : (∫ t in l..q, (g t * Real.exp (k * t) *
        intervalExtension hV (intervalExtension hU C (g t)) t) ^ 2) ≤
          E₃ * (E₀ + E₁ * ∫ t, B t ^ 2) := by
      let F := fun t => g t * Real.exp (k * t) * intervalExtension hV (intervalExtension hU C (g t)) t
      have hFc : ContinuousOn F (Icc l q) := by
        have hgc' := hgc.mono hsub
        dsimp only [F]
        fun_prop
      have hh := causalExpIntegral_dominated_energy hV (sub_pos.2 hka)
        (hT.le.trans hl) hlq hqV M hFc (C := (N * D / Y) * W) (fun t ht => ?_)
      · exact (hh.trans (mul_le_mul_of_nonneg_left hactual.1 (sq_nonneg _))).trans_eq
          (by dsimp only [E₀, E₁, E₃, W]; ring)
      · have hbnd := hactual.2.2 ⟨g t, hgu t ht⟩ ⟨t, htv t ht⟩ (hwidth t ht)
        simpa only [F, C, M, W, abs_mul, abs_of_nonneg (hgu t ht).1, abs_of_pos (Real.exp_pos _),
          intervalExtension_apply, projIcc_of_mem hU (hgu t ht), projIcc_of_mem hV (htv t ht)] using hbnd
    refine ⟨hcorr, ?_⟩
    have hdirect := logarithmicIncoming_trace_energy (ℓ := ℓ) hlq hb hD hη hcrit (hgc.mono hsub)
      (fun t ht => (hpoint t (hsub ht)).2.2.1) (fun t ht => (hpoint t (hsub ht)).1.1)
      (fun t ht => (hpoint t (hsub ht)).1.2.le) (fun t ht => (hpoint t (hsub ht)).2.1)
      (fun t ht => (hpoint t (hsub ht)).2.2.2.1) B hB
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
    have hin : (∫ t in l..q, (g t * Real.exp (k * t) *
        incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0) (projIcc 0 U hU (g t)) 0 *
          logarithmicIncoming b ℓ B (g t)) ^ 2) ≤ E₂ * ∫ t, B t ^ 2 := by
      convert hdirect using 1
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hlq] at ht
      simp only [projIcc_of_mem hU (hgu t ht), incomingWaveCurve_apply, incomingRadius,
        Matrix.cons_val_zero]
    have hh := hx.scalar_curve_energy rfl hinu hfc hif hlq (hgc.mono hsub)
      (fun t ht => ⟨(hpoint t (hsub ht)).1.1, (hgu t ht).2⟩) hin hcorr
    exact hh.trans_eq (by ring)

end CauchyHorizon.Background
