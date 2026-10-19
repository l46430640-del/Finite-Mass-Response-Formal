import CauchyHorizon.Characteristic.BandTraceEnergy

/-! The actual matching curve supplies a continuous source with uniform post-entry energy. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_band_source_energy (G : Background) {s H dH A b k : ℝ}
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
      ∀ Y : ℝ, G.inner < Y → Y ≤ R → ∃ U₀ T j D η C E₀ E₁ F₀ F₁ : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ 0 < j ∧ 0 < D ∧ 0 < η ∧ 0 < C ∧
        0 ≤ E₀ ∧ 0 ≤ E₁ ∧ 0 ≤ F₀ ∧ 0 ≤ F₁ ∧
        ∀ Olo : ℝ, 0 < Olo → ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (B : ℝ →ᵇ ℝ),
          Integrable (fun t => B t ^ 2) →
          MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 δ)) →
          (eLpNorm (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 δ))).toReal ≤ A →
          k ≤ G.outerRate * (1 - 1 / p.toReal) →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧
            Tendsto g atTop (𝓝 0) ∧ ContinuousOn (deriv g) (Ici T) ∧ U₀ < g T ∧
            (∀ t ∈ Ici T, 0 < g t ∧ g t * Real.exp (G.outerRate * t) ≤ D ∧
              DifferentiableAt ℝ g t ∧ η ≤ -deriv g t / g t ∧
              j ≤ g t * Real.exp (G.outerRate * t) ∧ -deriv g t / g t ≤ C) ∧
            ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 U)))
                (x : WaveState U V)
                (hx : IsWaveIntegral hU.le hV G.charge G.cosmological
                  (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x),
                ∃ (w : C(Icc 0 V, ℝ)) (hw0 : ∀ v, 0 ≤ w v) (S : C(Icc 0 V, ℝ)),
                  (∀ v, w v = g (max T (v : ℝ))) ∧ Antitone w ∧ (∀ v, 0 ≤ S v) ∧
                  ((∫ t in (0 : ℝ)..V,
                    (movingSpatialRadiationEnvelope w hw0 G.outerRate k 0 x (projIcc 0 V hV t)) ^ 2) ≤
                      E₀ + E₁ * ∫ t, B t ^ 2) ∧
                  (∀ v : Icc 0 V, T ≤ v → g v ≤ U →
                    x.1 (projIcc 0 U hU.le (g v)) v 0 = Y) ∧
                  (∀ (u : Icc 0 U) (v : Icc 0 V), 0 < (u : ℝ) →
                    x.1 u v 0 = Y → x.2.1 u v 0 < 0 → g v = u) ∧
                  (∀ v : Icc 0 V, T ≤ v → g v ≤ U →
                    g v * |radialNuField hV G.charge G.cosmological
                      (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                        (projIcc 0 U hU.le (g v)) v| ≤ D) ∧
                  (∀ l q : ℝ, T ≤ l → l ≤ q → q ≤ V → g l ≤ U →
                    (∫ t in l..q, (g t * Real.exp (k * t) *
                      (intervalExtension hV (intervalExtension hU.le x.1 (g t)) t 0 *
                        derivWithin (fun u => intervalExtension hV (intervalExtension hU.le x.1 u) t 1)
                          (Icc 0 U) (g t))) ^ 2) ≤ F₀ + F₁ * ∫ t, B t ^ 2) ∧
                  (∀ l q : ℝ, T ≤ l → l ≤ q → q ≤ V → g l ≤ U →
                    (∫ t in l..q, (S (projIcc 0 V hV t)) ^ 2) ≤
                      (4 / Olo) ^ 2 * (F₀ + F₁ * ∫ t, B t ^ 2)) ∧
                  let ν := radialNuField hV G.charge G.cosmological
                    (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                  ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, T ≤ v → 0 < t →
                    x.1 (projIcc 0 U hU.le t) v 0 = Y → x.2.1 (projIcc 0 U hU.le t) v 0 < 0 →
                    Olo ≤ t * Real.exp (x.1 (projIcc 0 U hU.le t) v 2) →
                      Real.exp (k * v) * |x.1 (projIcc 0 U hU.le t) v 0 * x.2.2 t v 1| ≤
                        (-ν (projIcc 0 U hU.le t) v) * S v := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hout
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hout hrb
  obtain ⟨δ, R, hδ, hδr, hR, hRr, hsolve⟩ := G.exists_band_trace_energy
    hs hH hdH hdHR hA hb hb1 hcrit hks hc hout hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, hRr, ?_⟩
  intro Y hY hYR
  obtain ⟨U₀, T, j, D, η, C, E₀, E₁, E₂, E₃, hU₀, hU₀δ, hT, hj, hD, hη, hC,
    hE₀, hE₁, hE₂, hE₃, hbnd⟩ := hsolve Y hY hYR
  let F₀ := 2 * E₃ * E₀
  let F₁ := 2 * (E₂ + E₃ * E₁)
  refine ⟨U₀, T, j, D, η, C, E₀, E₁, F₀, F₁, hU₀, hU₀δ, hT, hj, hD, hη, hC, hE₀, hE₁,
    by dsimp only [F₀]; positivity, by dsimp only [F₁]; positivity, ?_⟩
  intro Olo hOlo p hp ℓ B hB hf hfn hkp
  obtain ⟨g, hgc, hga, hgl, hdc, hstart, hpoint, hphysical⟩ := hbnd p hp ℓ B hB hf hfn hkp
  refine ⟨g, hgc, hga, hgl, hdc, hstart, fun t ht => ⟨(hpoint t ht).1.1, (hpoint t ht).2⟩, ?_⟩
  intro U V hU hV hUR hUU hfU x hx
  obtain ⟨w, hw0, hw, henergy, hidentify, hnuY, htraces⟩ := hphysical U V hU.le hV hUR hUU hfU x hx
  have hwa : Antitone w := fun v z hvz => by
    rw [hw, hw]
    exact hga.antitoneOn (le_max_left T (v : ℝ)) (le_max_left T (z : ℝ)) (max_le_max_left T hvz)
  let gC : C(Icc 0 V, Icc 0 U) :=
    ⟨fun v => ⟨min U (w v), le_min hU.le (hw0 v), min_le_left _ _⟩,
      (continuous_const.min w.continuous).subtype_mk _⟩
  have hgC (v : Icc 0 V) : 0 < (gC v : ℝ) := by
    change 0 < min U (w v)
    rw [hw]
    exact lt_min hU (hpoint _ (show T ≤ max T (v : ℝ) from le_max_left _ _)).1.1
  have hfc : ContinuousOn (logarithmicIncoming b ℓ B) (Ioi 0) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.mul (continuousOn_id.rpow_const (fun t ht => Or.inl ht.ne'))
    · exact B.continuous.comp_continuousOn
        (continuousOn_const.sub (continuousOn_id.log (fun t ht => ht.ne')))
  have hif : ∀ᵐ t ∂volume.restrict (Icc 0 U),
      incomingWaveVelocity hUR hp hfU t 1 = logarithmicIncoming b ℓ B t := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hfU] with t ht
    rw [ht]
    rfl
  obtain ⟨S, hS0, _hSval, hSE, hsource⟩ := hx.exists_matching_radiation_source (k := k) rfl
    (incomingWave_constraint_data hU.le hUR hp hfU (horizonPhi h r 0)).1 hfc hif
      (show 0 < Olo / 4 by positivity) gC hgC
  have hfactor : 1 / (Olo / 4) ^ 2 = (4 / Olo) ^ 2 := by ring
  rw [hfactor] at hSE
  refine ⟨w, hw0, S, hw, hwa, hS0, henergy, ?_, hidentify, hnuY,
    (fun l q hl hlq hqV hgl => (htraces l q hl hlq hqV hgl).2.2.2), ?_, ?_⟩
  · intro v hTv hgv
    have hh := (htraces v v hTv le_rfl v.property.2 hgv).1 v ⟨le_rfl, le_rfl⟩
    simpa only [intervalExtension_apply, projIcc_of_mem hV v.property] using hh
  · intro l q hl hlq hqV hglU
    have hsub : Icc l q ⊆ Ici T := fun _ ht => hl.trans ht.1
    have hgu (t : ℝ) (ht : t ∈ Icc l q) : g t ∈ Icc 0 U :=
      ⟨(hpoint t (hsub ht)).1.1.le, (hga.antitoneOn hl (hsub ht) ht.1).trans hglU⟩
    have htv (t : ℝ) (ht : t ∈ Icc l q) : t ∈ Icc (0 : ℝ) V :=
      ⟨hT.le.trans (hsub ht), ht.2.trans hqV⟩
    have hcp (t : ℝ) (ht : t ∈ Icc l q) : gC (projIcc 0 V hV t) = ⟨g t, hgu t ht⟩ := by
      apply Subtype.ext
      rw [projIcc_of_mem hV (htv t ht)]
      change min U (w ⟨t, htv t ht⟩) = g t
      rw [hw, max_eq_right (hsub ht), min_eq_right (hgu t ht).2]
    have hbound := (htraces l q hl hlq hqV hglU).2.2.2
    calc
      (∫ t in l..q, (S (projIcc 0 V hV t)) ^ 2) = (4 / Olo) ^ 2 *
          ∫ t in l..q, (g t * Real.exp (k * t) *
            (intervalExtension hV (intervalExtension hU.le x.1 (g t)) t 0 *
              derivWithin (fun u => intervalExtension hV (intervalExtension hU.le x.1 u) t 1)
                (Icc 0 U) (g t))) ^ 2 := by
        rw [hSE l q]
        congr 1
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hlq] at ht
        dsimp only
        rw [hcp t ht]
        simp only [intervalExtension_apply, projIcc_of_mem hV (htv t ht),
          projIcc_of_mem hU.le (hgu t ht)]
      _ ≤ (4 / Olo) ^ 2 * (2 * E₃ * E₀ + 2 * (E₂ + E₃ * E₁) * ∫ t, B t ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = (4 / Olo) ^ 2 * (F₀ + F₁ * ∫ t, B t ^ 2) := rfl
  · filter_upwards [hsource, ae_restrict_mem measurableSet_Icc] with t ht htu
    intro v hTv ht0 hrad hlam hnorm
    have hscale : Olo / 4 ≤ t *
        (-radialNuField hV G.charge G.cosmological
          (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose (projIcc 0 U hU.le t) v) := by
      have hgauge := hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU (projIcc 0 U hU.le t) v
      have he := (div_le_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hgauge.2.2.1)).1
        hgauge.2.2.2.2
      have hE : Real.exp (x.1 (projIcc 0 U hU.le t) v 2) ≤
          4 * (-radialNuField hV G.charge G.cosmological
            (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose (projIcc 0 U hU.le t) v) := by
        linarith only [he]
      have hh := mul_le_mul_of_nonneg_left hE htu.1
      linarith only [hnorm, hh]
    apply ht v ?_ hscale
    have he : g v = t := by
      simpa only [projIcc_of_mem hU.le htu] using
        hidentify (projIcc 0 U hU.le t) v (by simpa only [projIcc_of_mem hU.le htu] using ht0) hrad hlam
    change min U (w v) = t
    rw [hw, max_eq_right hTv, he, min_eq_right htu.2]

end CauchyHorizon.Background
