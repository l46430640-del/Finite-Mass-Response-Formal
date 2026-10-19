import CauchyHorizon.Characteristic.MatchedLimit

/-! Matched scalar tails on one prescribed all-time physical family. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 4000000 in
theorem exists_common_family_matched_small (B : Background) {s H dH A E : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hm : B.criticalExponent < 1) (hks : B.innerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let b := B.criticalExponent
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    let Ch := r 0 / (B.event * cν ^ b)
    let Xm := fun z => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - z)
    let Wm := fun z => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - z)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y cap η : ℝ, B.inner < Y → Y ≤ R → 0 < cap → 0 < η →
        ∃ Z : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
          Z ∈ Ioo Y B.event ∧ B.event - cap < Z ∧ (∀ U, 0 < τ U) ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ m : ℕ → ℝ) (P Q : ℕ → ℝ →ᵇ ℝ),
            B.innerRate ≤ B.outerRate * (1 - 1 / p.toReal) →
            (∀ n, Integrable (fun t => P n t ^ 2)) → (∀ n, (∫ t, P n t ^ 2) ≤ E) →
            (∀ n t, HasDerivAt (P n) (Q n t) t) → (∀ n, Integrable (fun t => Q n t ^ 2)) →
            Tendsto (fun n => ∫ t, Q n t ^ 2) atTop (𝓝 0) →
            Tendsto (fun n => m n - ℓ n) atTop atTop → (∀ n t, t ≤ m n → P n t = 0) →
            (∀ n, MemLp (logarithmicIncoming b (ℓ n) (P n)) p (volume.restrict (Icc 0 δ))) →
            (∀ n, (eLpNorm (logarithmicIncoming b (ℓ n) (P n)) p (volume.restrict (Icc 0 δ))).toReal ≤ A) →
            Tendsto (fun n => (eLpNorm (logarithmicIncoming b (ℓ n) (P n)) p
              (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            ∀ (U : ℝ) (hUp : 0 < U) (hUR : U < r 0)
              (hfU : ∀ n, MemLp (logarithmicIncoming b (ℓ n) (P n)) p (volume.restrict (Icc 0 U)))
              (X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T)
              (X₀ : (T : Ici (0 : ℝ)) → WaveState U T)
              (hX : ∀ n (T : Ici (0 : ℝ)), IsWaveIntegral hUp.le T.property B.charge B.cosmological
                (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                (incomingWaveVelocity hUR hp (hfU n)) (X n T))
              (_hX₀ : ∀ T : Ici (0 : ℝ), IsWaveIntegral hUp.le T.property B.charge B.cosmological
                (incomingWaveCurve hUp.le hUR hp (f := 0) MemLp.zero (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                (incomingWaveVelocity hUR hp (f := 0) MemLp.zero) (X₀ T)),
              ∀ ρ : ℝ, 0 < ρ → (∀ n T u v, ρ ≤ (X n T).1 u v 0) → (∀ T u v, ρ ≤ (X₀ T).1 u v 0) →
                ∀ l : ℝ, τ ⟨U, hUp⟩ ≤ l →
                  ∃ g Eθ Eζ : ℕ → ℝ → ℝ,
                    (∀ n, ContinuousOn (g n) (Ici l) ∧ ContinuousOn (Eθ n) (Ici l) ∧
                      ContinuousOn (Eζ n) (Ici l) ∧ MemLp (Eθ n) 2 (volume.restrict (Ici l)) ∧
                        MemLp (Eζ n) 2 (volume.restrict (Ici l))) ∧
                    (∀ n t, l ≤ t → ∀ (T : Ici (0 : ℝ)) (htT : t ∈ Icc 0 (T : ℝ)),
                      let u := projIcc 0 U hUp.le (g n t)
                      let v : Icc 0 (T : ℝ) := ⟨t, htT⟩
                      let ν := radialNuField T.property B.charge B.cosmological
                        (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose
                      let H₀ := Ch * P n (B.outerRate * t + ℓ n + Real.log cν - Real.log (B.z Z))
                      g n t ∈ Ioo 0 U ∧ (X n T).1 u v 0 = Y ∧
                        Eθ n t = Real.exp (B.innerRate * t) * (Y * (X n T).2.1 u v 1) - Xm Y * H₀ ∧
                        Eζ n t = Real.exp (B.innerRate * t) * g n t *
                          ((r 0 - g n t) * logarithmicIncoming b (ℓ n) (P n) (g n t) +
                            scalarTransportCorrection T.property ν (X n T).2.1 u v) /
                              B.criticalWeight Y - Wm Y * H₀) ∧
                    (∀ n t, l ≤ t → ∀ (T : Ici (0 : ℝ)) (htT : t ∈ Icc 0 (T : ℝ)) (u : Icc (0 : ℝ) U),
                      (X n T).1 u ⟨t, htT⟩ 0 = Y → (u : ℝ) = g n t) ∧
                    ∀ᶠ n in atTop, Real.sqrt (∫ t in Ici l, Eθ n t ^ 2 + Eζ n t ^ 2) < η := by
  classical
  intro b hi hr0 cν Ch Xm Wm
  obtain ⟨δ, R, hδ, hR, hlate⟩ := B.exists_late_matched_small
    hs hH hdH hdHR hA hE hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y cap η hY hYR hcap hη
  obtain ⟨Z, U₀, τ, hZ, hcapZ, hU₀, _hUδ, hτ, hsmall⟩ := hlate Y cap η hY hYR hcap hη
  let width := fun U : Ioi (0 : ℝ) => (⟨min (U : ℝ) U₀, lt_min U.property hU₀⟩ : Ioi (0 : ℝ))
  refine ⟨Z, (fun U => τ (width U)), hZ, hcapZ, (fun U => hτ (width U)), ?_⟩
  intro p hp ℓ m P Q hcrit hPi hPE hPQ hQi hQlim hfront hsupport hf hfn hflim
    U hUp hUR hfU X X₀ hX hX₀ ρ hρ hfloor hfloor₀ l hl
  let W := min U U₀
  have hWp : 0 < W := lt_min hUp hU₀
  have hWU : W ≤ U := min_le_left _ _
  have hWW : W ≤ U₀ := min_le_right _ _
  have hWR : W < r 0 := hWU.trans_lt hUR
  let hfW := fun n => (hfU n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hWU) le_rfl)
  let restrict := fun (T : Ici (0 : ℝ)) (z : WaveState U T) =>
    waveTranslate (a := 0) (U := W) (b := 0) (V := (T : ℝ))
      le_rfl (by simpa only [zero_add] using hWU) le_rfl (by simp) z
  let Xw := fun n T => restrict T (X n T)
  let Xw₀ := fun T => restrict T (X₀ T)
  have hXw (n : ℕ) (T : Ici (0 : ℝ)) : IsWaveIntegral hWp.le T.property B.charge B.cosmological
      (incomingWaveCurve hWp.le hWR hp (hfW n) (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
      (incomingWaveVelocity hWR hp (hfW n)) (Xw n T) :=
    (hX n T).horizon_prefix hUp.le T.property hUR hWp.le T.property hWU le_rfl hc hi hrc hr0 hp (hfU n)
  have hXw₀ (T : Ici (0 : ℝ)) : IsWaveIntegral hWp.le T.property B.charge B.cosmological
      (incomingWaveCurve hWp.le hWR hp (f := 0) MemLp.zero (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
      (incomingWaveVelocity hWR hp (f := 0) MemLp.zero) (Xw₀ T) :=
    (hX₀ T).horizon_prefix hUp.le T.property hUR hWp.le T.property hWU le_rfl hc hi hrc hr0 hp MemLp.zero
  have hfloorw (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc (0 : ℝ) W) (v : Icc (0 : ℝ) (T : ℝ)) :
      ρ ≤ (Xw n T).1 u v 0 := hfloor n T _ _
  have hfloorw₀ (T : Ici (0 : ℝ)) (u : Icc (0 : ℝ) W) (v : Icc (0 : ℝ) (T : ℝ)) :
      ρ ≤ (Xw₀ T).1 u v 0 := hfloor₀ T _ _
  obtain ⟨g, Eθ, Eζ, hreg, htrace, hbound⟩ := hsmall p hp ℓ m P Q hcrit hPi hPE hPQ hQi hQlim
    hfront hsupport hf hfn hflim W hWp hWR hWW hfW Xw Xw₀ hXw hXw₀ ρ hρ hfloorw hfloorw₀ l hl
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have hcanonical (n : ℕ) (t : ℝ) (ht : l ≤ t) (V : Ici (0 : ℝ)) (htV : t ∈ Icc 0 (V : ℝ))
      (u : Icc (0 : ℝ) U) (huY : (X n V).1 u ⟨t, htV⟩ 0 = Y) : (u : ℝ) = g n t := by
    let T : Ici (0 : ℝ) := ⟨max 0 t + 1, by change 0 ≤ max 0 t + 1; positivity⟩
    have hh := htrace n t ht
    have hgW : g n t ∈ Icc 0 W := ⟨hh.1.1.le, hh.1.2.le⟩
    have htT : t ∈ Icc 0 (T : ℝ) :=
      ⟨htV.1, (le_max_right 0 t).trans (le_add_of_nonneg_right zero_le_one)⟩
    have hhit : (Xw n T).1 ⟨g n t, hgW⟩ ⟨t, htT⟩ 0 = Y := by
      have hh' := hh.2.1
      change (Xw n T).1 (projIcc 0 W hWp.le (g n t)) (projIcc 0 (T : ℝ) T.property t) 0 = Y at hh'
      simpa only [projIcc_of_mem hWp.le hgW, projIcc_of_mem T.property htT] using hh'
    exact (hX n V).horizon_radius_coordinate_unique hUp.le V.property hUR hWp.le T.property hWR
      hc hi hrc hr0 hφ hrd hp (hfU n) (hfW n) (hXw n T) u ⟨g n t, hgW⟩ htV htT (huY.trans hhit.symm)
  refine ⟨g, Eθ, Eζ, hreg, ?_, hcanonical, hbound⟩
  intro n t ht T htT u v ν H₀
  let S : Ici (0 : ℝ) := ⟨max 0 t + 1, by change 0 ≤ max 0 t + 1; positivity⟩
  have hh := htrace n t ht
  have hgW : g n t ∈ Icc 0 W := ⟨hh.1.1.le, hh.1.2.le⟩
  have hgU : g n t ∈ Icc 0 U := ⟨hgW.1, hgW.2.trans hWU⟩
  have htS : t ∈ Icc 0 (S : ℝ) :=
    ⟨htT.1, (le_max_right 0 t).trans (le_add_of_nonneg_right zero_le_one)⟩
  have hu : u = ⟨g n t, hgU⟩ := projIcc_of_mem hUp.le hgU
  let vw := projIcc 0 (S : ℝ) S.property t
  have hvw : vw = ⟨t, htS⟩ := projIcc_of_mem S.property htS
  let uw := projIcc 0 W hWp.le (g n t)
  have huw : uw = ⟨g n t, hgW⟩ := projIcc_of_mem hWp.le hgW
  have ho := (hXw n S).horizon_overlap hWp.le S.property hWR hUp.le T.property hUR
    hc hi hrc hr0 hp (hfW n) (hfU n) (hX n T) hgW hgU htS htT
  have hstate : (Xw n S).1 uw vw = (X n T).1 u v := by simpa only [hu, hvw, huw] using ho.1
  have hvel : (Xw n S).2.1 uw vw = (X n T).2.1 u v := by simpa only [hu, hvw, huw] using ho.2
  let νw := radialNuField S.property B.charge B.cosmological
    (incomingWaveCurve hWp.le hWR hp (hfW n) (horizonPhi h r 0)) (Xw n S).1 (hXw n S).choose
  have hcor : scalarTransportCorrection S.property νw (Xw n S).2.1 uw vw =
      scalarTransportCorrection T.property ν (X n T).2.1 u v := by
    have hz := (hXw n S).horizon_overlap_zeta hWp.le S.property hWR hUp.le T.property hUR
      hc hi hrc hr0 hp (hfW n) (hfU n) (hX n T) hgW hgU htS htT
    simp only [incomingWaveCurve_apply, Matrix.cons_val_zero, incomingRadius] at hz
    simpa only [hu, hvw, huw] using (add_left_cancel hz)
  refine ⟨⟨hh.1.1, hh.1.2.trans_le hWU⟩, ?_, ?_, ?_⟩
  · have hh' := hh.2.1
    change (Xw n S).1 uw vw 0 = Y at hh'
    simpa only [hstate] using hh'
  · have hh' := hh.2.2.1
    change Eθ n t = Real.exp (B.innerRate * t) * (Y * (Xw n S).2.1 uw vw 1) - Xm Y * H₀ at hh'
    simpa only [hvel] using hh'
  · have hh' := hh.2.2.2
    change Eζ n t = Real.exp (B.innerRate * t) * g n t *
      ((r 0 - g n t) * logarithmicIncoming b (ℓ n) (P n) (g n t) +
        scalarTransportCorrection S.property νw (Xw n S).2.1 uw vw) / B.criticalWeight Y - Wm Y * H₀ at hh'
    simpa only [hcor] using hh'

end CauchyHorizon.Background
