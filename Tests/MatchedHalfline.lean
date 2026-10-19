import CauchyHorizon.Characteristic.CommonRadiation

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Tests

-- Finite representatives may differ arbitrarily outside their own windows.
example (l : ℝ) : ∃ f : ℝ → ℝ, ContinuousOn f (Ici l) ∧
    ∀ S : Ici l, EqOn f (fun t => if t ≤ S then Real.exp (-t) else (S : ℝ)) (Icc l S) := by
  apply exists_continuous_compatible_halfline
  · intro S
    apply (Real.continuous_exp.comp continuous_neg).continuousOn.congr
    intro t ht
    simp only [if_pos ht.2, Function.comp_def]
  · intro S T t htS htT
    simp only [if_pos htS.2, if_pos htT.2]

-- The endpoint and zero-energy cases need no strict positivity assumption.
example (l : ℝ) : MemLp (fun _ : ℝ => (0 : ℝ)) 2 (volume.restrict (Ici l)) ∧
    MemLp (fun _ : ℝ => (0 : ℝ)) 2 (volume.restrict (Ici l)) ∧
    Real.sqrt (∫ _t in Ici l, (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2) ≤ 0 := by
  apply pair_energy_halfline continuousOn_const continuousOn_const
  intro S _
  simp

-- A fixed-width common family supplies the prefixes; no compatibility premise is needed.
set_option maxHeartbeats 4000000 in
example (B : Background) (hcrit : B.criticalExponent = 3 / 4) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hks : B.innerRate < s) {h rH : ℝ → ℝ}
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous rH) (hrb : ∀ t, B.event - dH ≤ rH t) (hrinit : B.inner < rH 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt rH
      (horizonFunction (rH t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖rH t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h rH s) :
    let hm : B.criticalExponent < 1 := by rw [hcrit]; norm_num
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (rH t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    let Ch := rH 0 / (B.event * cν ^ B.criticalExponent)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R →
        ∃ Z U₀ : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
          Y < Z ∧ Z < B.event ∧ 0 < U₀ ∧ U₀ ≤ δ ∧
          ∀ (ℓ : ℝ) (P Q : ℝ →ᵇ ℝ), Integrable (fun t => P t ^ 2) →
            (∀ t, HasDerivAt P (Q t) t) → Integrable (fun t => Q t ^ 2) →
            MemLp (logarithmicIncoming B.criticalExponent ℓ P) 4 (volume.restrict (Icc 0 δ)) →
            (eLpNorm (logarithmicIncoming B.criticalExponent ℓ P) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (U : ℝ) (hUp : 0 < U) (hUR : U < rH 0), U ≤ U₀ →
              ∀ (hfU : MemLp (logarithmicIncoming B.criticalExponent ℓ P) 4 (volume.restrict (Icc 0 U)))
                (l : ℝ), τ ⟨U, hUp⟩ ≤ l →
                ∀ (x : (T : Ici (0 : ℝ)) → WaveState U T)
                  (hx : ∀ T : Ici (0 : ℝ), IsWaveIntegral hUp.le T.property B.charge B.cosmological
                    (incomingWaveCurve hUp.le hUR le_rfl hfU (horizonPhi h rH 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                    (incomingWaveVelocity hUR le_rfl hfU) (x T)),
                  ∃ g E : ℝ → ℝ, ContinuousOn g (Ici l) ∧ ContinuousOn E (Ici l) ∧
                    MemLp E 2 (volume.restrict (Ici l)) ∧ ∀ t ≥ l,
                      let T : Ici (0 : ℝ) := ⟨max 0 t + 1, by change 0 ≤ max 0 t + 1; positivity⟩
                      let u := projIcc 0 U hUp.le (g t)
                      let v := projIcc 0 (T : ℝ) T.property t
                      g t ∈ Ioo 0 U ∧ (x T).1 u v 0 = Y ∧
                      E t = Real.exp (B.innerRate * t) * (Y * (x T).2.1 u v 1) -
                        extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - Y) *
                          (Ch * P (B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Z))) := by
  intro hm hi hr0 cν Ch
  have hk : B.innerRate ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    have hh := (div_eq_iff B.outerRate_pos.ne').1 hcrit
    norm_num
    linarith only [hh]
  obtain ⟨δ, R, hδ, hR, hband⟩ := B.exists_matched_halfline_energy hs hH hdH hdHR hA hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨Z, U₀, C, L, τ, hZ, _hcapZ, hU₀, hUδ, _hC, _hL, hsolve⟩ :=
    hband Y 1 1 hY hYR zero_lt_one zero_lt_one
  let ε : Ioi (0 : ℝ) := ⟨1, by change (0 : ℝ) < 1; exact zero_lt_one⟩
  refine ⟨Z, U₀, (fun U => τ ε U), hZ.1, hZ.2, hU₀, hUδ, ?_⟩
  intro ℓ P Q hPi hPQ hQi hf hfn U hUp hUR hUU hfU l hl x hx
  obtain ⟨χ, hχ, g, E, F, hgc, hec, _hfc, htrace, hElp, _hFlp, _hbound⟩ :=
    hsolve 4 le_rfl ℓ P Q hk hPi hPQ hQi hf hfn U hUp.le hUR hUU hfU ε hUp l hl
      (fun S => x ⟨max 0 (S : ℝ) + 1, by change 0 ≤ max 0 (S : ℝ) + 1; positivity⟩)
      (fun S => hx ⟨max 0 (S : ℝ) + 1, by change 0 ≤ max 0 (S : ℝ) + 1; positivity⟩)
  refine ⟨g, E, hgc, hec, hElp, ?_⟩
  intro t ht T u v
  have hgt := htrace ⟨t, ht⟩ t ⟨ht, le_rfl⟩
  have hhit := (hχ ⟨t, ht⟩).2 (Z - Y, t) ⟨⟨sub_nonneg.2 hZ.1.le, le_rfl⟩, ht, le_rfl⟩
  have hr : (x T).1 u v 0 = Y := by
    simpa only [u, v, T, hgt.1, sub_sub_cancel] using hhit.2
  refine ⟨by simpa only [hgt.1] using hhit.1, hr, ?_⟩
  have he := hgt.2.1
  dsimp only at he
  rw [← hgt.1] at he
  change E t = Real.exp (B.innerRate * t) * ((x T).1 u v 0 * (x T).2.1 u v 1) -
    extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - (x T).1 u v 0) *
      (Ch * P (B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Z))) at he
  simpa only [hr] using he

-- Critical p=4: the original family's width has no accuracy-dependent upper bound.
set_option maxHeartbeats 5000000 in
example (B : Background) (hcrit : B.criticalExponent = 3 / 4) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hks : B.innerRate < s) {h r : ℝ → ℝ}
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hm : B.criticalExponent < 1 := by rw [hcrit]; norm_num
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    let Ch := r 0 / (B.event * cν ^ B.criticalExponent)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y η : ℝ, B.inner < Y → Y ≤ R → 0 < η →
        ∃ Z : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
          Z ∈ Ioo Y B.event ∧ (∀ U, 0 < τ U) ∧
          ∀ (ℓ m : ℕ → ℝ) (P Q : ℕ → ℝ →ᵇ ℝ),
            (∀ n, Integrable (fun t => P n t ^ 2)) → (∀ n, (∫ t, P n t ^ 2) ≤ 1) →
            (∀ n t, HasDerivAt (P n) (Q n t) t) → (∀ n, Integrable (fun t => Q n t ^ 2)) →
            Tendsto (fun n => ∫ t, Q n t ^ 2) atTop (𝓝 0) →
            Tendsto (fun n => m n - ℓ n) atTop atTop → (∀ n t, t ≤ m n → P n t = 0) →
            (∀ n, MemLp (logarithmicIncoming B.criticalExponent (ℓ n) (P n)) 4 (volume.restrict (Icc 0 δ))) →
            (∀ n, (eLpNorm (logarithmicIncoming B.criticalExponent (ℓ n) (P n)) 4
              (volume.restrict (Icc 0 δ))).toReal ≤ A) →
            Tendsto (fun n => (eLpNorm (logarithmicIncoming B.criticalExponent (ℓ n) (P n)) 4
              (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            ∀ (U : ℝ) (hUp : 0 < U) (hUR : U < r 0),
              ∀ (hfU : ∀ n, MemLp (logarithmicIncoming B.criticalExponent (ℓ n) (P n)) 4
                  (volume.restrict (Icc 0 U)))
                (X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T)
                (X₀ : (T : Ici (0 : ℝ)) → WaveState U T)
                (_hX : ∀ n (T : Ici (0 : ℝ)), IsWaveIntegral hUp.le T.property B.charge B.cosmological
                  (incomingWaveCurve hUp.le hUR le_rfl (hfU n) (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl (hfU n)) (X n T))
                (_hX₀ : ∀ T : Ici (0 : ℝ), IsWaveIntegral hUp.le T.property B.charge B.cosmological
                  (incomingWaveCurve hUp.le hUR le_rfl (f := 0) MemLp.zero (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl (f := 0) MemLp.zero) (X₀ T)),
                ∀ ρ : ℝ, 0 < ρ → (∀ n T u v, ρ ≤ (X n T).1 u v 0) →
                  (∀ T u v, ρ ≤ (X₀ T).1 u v 0) → ∀ l : ℝ, τ ⟨U, hUp⟩ ≤ l →
                    ∃ g Eθ Eζ : ℕ → ℝ → ℝ,
                      (∀ n, MemLp (Eθ n) 2 (volume.restrict (Ici l)) ∧
                        MemLp (Eζ n) 2 (volume.restrict (Ici l))) ∧
                      (∀ n t, l ≤ t → ∀ (T : Ici (0 : ℝ)) (htT : t ∈ Icc 0 (T : ℝ)),
                        let u := projIcc 0 U hUp.le (g n t)
                        let v : Icc 0 (T : ℝ) := ⟨t, htT⟩
                        g n t ∈ Ioo 0 U ∧ (X n T).1 u v 0 = Y ∧
                          Eθ n t = Real.exp (B.innerRate * t) * (Y * (X n T).2.1 u v 1) -
                            extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - Y) *
                              (Ch * P n (B.outerRate * t + ℓ n + Real.log cν - Real.log (B.z Z)))) ∧
                      (∀ n t, l ≤ t → ∀ (T : Ici (0 : ℝ)) (htT : t ∈ Icc 0 (T : ℝ)) (u : Icc (0 : ℝ) U),
                        (X n T).1 u ⟨t, htT⟩ 0 = Y → (u : ℝ) = g n t) ∧
                      ∀ᶠ n in atTop, Real.sqrt (∫ t in Ici l, Eθ n t ^ 2 + Eζ n t ^ 2) < η := by
  intro hm hi hr0 cν Ch
  have hk : B.innerRate ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    have hh := (div_eq_iff B.outerRate_pos.ne').1 hcrit
    norm_num
    linarith only [hh]
  obtain ⟨δ, R, hδ, hR, hlate⟩ := B.exists_common_family_matched_small
    hs hH hdH hdHR hA zero_le_one hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y η hY hYR hη
  obtain ⟨Z, τ, hZ, _hcap, hτ, hsmall⟩ := hlate Y 1 η hY hYR zero_lt_one hη
  refine ⟨Z, τ, hZ, hτ, ?_⟩
  intro ℓ m P Q hPi hPE hPQ hQi hQlim hfront hsupport hf hfn hflim U hUp hUR hfU X X₀ hX hX₀ ρ hρ hfloor hfloor₀ l hl
  obtain ⟨g, Eθ, Eζ, hreg, htrace, hcanonical, hbound⟩ := hsmall 4 le_rfl ℓ m P Q hk
    hPi hPE hPQ hQi hQlim hfront hsupport hf hfn hflim U hUp hUR hfU
    X X₀ hX hX₀ ρ hρ hfloor hfloor₀ l hl
  refine ⟨g, Eθ, Eζ, (fun n => ⟨(hreg n).2.2.2.1, (hreg n).2.2.2.2⟩), ?_, hcanonical, hbound⟩
  intro n t ht T htT
  exact ⟨(htrace n t ht T htT).1, (htrace n t ht T htT).2.1, (htrace n t ht T htT).2.2.1⟩

-- A nonzero L2 reference needs only its integrable tail, not an exponential rate.
example (l : ℝ) (F G : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Ici l)))
    (hG : MemLp G 2 (volume.restrict (Ici l))) :
    Tendsto (fun _n : ℕ => ∫ t in Ici l, (F t - F t) ^ 2 + (G t - G t) ^ 2) atTop (𝓝 0) := by
  apply pair_energy_tendsto_of_history_tail (fun _ => hF) (fun _ => hG) hF hG
  · intro S _
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, intervalIntegral.integral_zero] using
      (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · intro ε hε
    have hh : Tendsto (fun S : ℝ => ∫ t in Ici S, F t ^ 2 + G t ^ 2) atTop (𝓝 0) :=
      tendsto_integral_Ici_zero tendsto_id
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hh.eventually_lt_const hε)
    exact ⟨T, fun S hS => Eventually.of_forall (fun _ => hT S hS)⟩

-- Critical p=4: both actual components converge on the fixed half-line,
-- with the zero-incoming member subtracted and no outer matching phase retained.
set_option maxHeartbeats 5000000 in
example (B : Background) (hcrit : B.criticalExponent = 3 / 4) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hks : B.innerRate < s) {h r : ℝ → ℝ}
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hm : B.criticalExponent < 1 := by rw [hcrit]; norm_num
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    let Ch := r 0 / (B.event * cν ^ B.criticalExponent)
    let cθ := fun Y => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - Y) * Ch
    let cζ := fun Y => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - Y) * Ch
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R →
        ∃ τ : Ioi (0 : ℝ) → ℝ, (∀ U, 0 < τ U) ∧
          ∀ (ℓ m : ℕ → ℝ) (P Q : ℕ → ℝ →ᵇ ℝ), P 0 = 0 →
            (∀ n, Integrable (fun t => P n t ^ 2)) → (∀ n, (∫ t, P n t ^ 2) ≤ 1) →
            (∀ n t, HasDerivAt (P n) (Q n t) t) → (∀ n, Integrable (fun t => Q n t ^ 2)) →
            Tendsto (fun n => ∫ t, Q n t ^ 2) atTop (𝓝 0) →
            Tendsto (fun n => m n - ℓ n) atTop atTop → (∀ n t, t ≤ m n → P n t = 0) →
            (∀ n, MemLp (logarithmicIncoming B.criticalExponent (ℓ n) (P n)) 4 (volume.restrict (Icc 0 δ))) →
            (∀ n, (eLpNorm (logarithmicIncoming B.criticalExponent (ℓ n) (P n)) 4
              (volume.restrict (Icc 0 δ))).toReal ≤ A) →
            Tendsto (fun n => (eLpNorm (logarithmicIncoming B.criticalExponent (ℓ n) (P n)) 4
              (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            ∀ (U : ℝ) (hUp : 0 < U) (hUR : U < r 0), U ≤ 1 → U ≤ δ →
              ∀ (hfU : ∀ n, MemLp (logarithmicIncoming B.criticalExponent (ℓ n) (P n)) 4
                  (volume.restrict (Icc 0 U)))
                (X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T)
                (hX : ∀ n (T : Ici (0 : ℝ)), IsWaveIntegral hUp.le T.property B.charge B.cosmological
                  (incomingWaveCurve hUp.le hUR le_rfl (hfU n) (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl (hfU n)) (X n T)),
                ∀ ρ : ℝ, 0 < ρ → (∀ n T u v, ρ ≤ (X n T).1 u v 0) →
                  ∀ l : ℝ, τ ⟨U, hUp⟩ ≤ l →
                    ∃ g θ ζ : ℕ → ℝ → ℝ,
                      (∀ n, MemLp (θ n) 2 (volume.restrict (Ici l)) ∧
                        MemLp (ζ n) 2 (volume.restrict (Ici l))) ∧
                      (∀ n t, l ≤ t → ∀ (T : Ici (0 : ℝ)) (htT : t ∈ Icc 0 (T : ℝ)),
                        let u := projIcc 0 U hUp.le (g n t)
                        let v : Icc 0 (T : ℝ) := ⟨t, htT⟩
                        let ν := radialNuField T.property B.charge B.cosmological
                          (incomingWaveCurve hUp.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose
                        g n t ∈ Ioo 0 U ∧ (X n T).1 u v 0 = Y ∧
                          θ n t = Real.exp (B.innerRate * t) * (Y * (X n T).2.1 u v 1) ∧
                          ζ n t = Real.exp (B.innerRate * t) * g n t *
                            ((r 0 - g n t) * logarithmicIncoming B.criticalExponent (ℓ n) (P n) (g n t) +
                              scalarTransportCorrection T.property ν (X n T).2.1 u v) / B.criticalWeight Y) ∧
                      (∀ n,
                        let A := fun t => B.criticalWeight Y /
                          (Real.exp (-1) * (-B.F Y) / B.outerRate) * |ζ n t|
                        ContinuousOn A (Ici l) ∧ MemLp A 2 (volume.restrict (Ici l)) ∧
                          (∀ T : Ici (0 : ℝ),
                            let ν := radialNuField T.property B.charge B.cosmological
                              (incomingWaveCurve hUp.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose
                            ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 (T : ℝ), l ≤ v →
                              (X n T).1 (projIcc 0 U hUp.le u) v 0 = Y →
                                Real.exp (B.innerRate * v) *
                                  |(X n T).1 (projIcc 0 U hUp.le u) v 0 * (X n T).2.2 u v 1| ≤
                                    (-ν (projIcc 0 U hUp.le u) v) * A v) ∧
                          ∀ (V : Ici (0 : ℝ)) (l' : Icc 0 (V : ℝ)), l ≤ l' →
                            ∀ (T₀ β L S : ℝ) (g₀ : ℝ → ℝ),
                            0 ≤ β → 0 ≤ L → ContinuousOn g₀ (Ici T₀) →
                            AuxiliaryRadiationCharts B hUp.le (X n V)
                              (radialNuField V.property B.charge B.cosmological
                                (incomingWaveCurve hUp.le hUR le_rfl (hfU n) (horizonPhi h r 0))
                                (X n V).1 (hX n V).choose) g₀ T₀ β Y L S →
                            ∀ b₀ : Icc 0 (V : ℝ), max (l' : ℝ) T₀ ≤ (b₀ : ℝ) / (1 + β) → S ≤ b₀ →
                              AuxiliaryRadiationEstimate B hUp.le V.property (X n V) (g n) g₀ β Y L
                                l' b₀ A) ∧
                      Tendsto (fun n => ∫ t in Ici l,
                        (θ n t - θ 0 t - cθ Y * P n (B.outerRate * t + ℓ n + Real.log cν)) ^ 2 +
                          (ζ n t - ζ 0 t - cζ Y * P n (B.outerRate * t + ℓ n + Real.log cν)) ^ 2) atTop (𝓝 0) := by
  intro hm hi hr0 cν Ch cθ cζ
  have hk : B.innerRate ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    have hh := (div_eq_iff B.outerRate_pos.ne').1 hcrit
    norm_num
    linarith only [hh]
  obtain ⟨δ, R, hδ, hR, hsolve⟩ := B.exists_common_radius_radiation
    hs hH hdH hdHR hA zero_le_one hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨τ, hτ, hfull⟩ := hsolve Y hY hYR
  refine ⟨τ, hτ, ?_⟩
  intro ℓ m P Q hP₀ hPi hPE hPQ hQi hQlim hfront hsupport hf hfn hflim
    U hUp hUR hU1 hUδ hfU X hX ρ hρ hfloor l hl
  obtain ⟨g, θ, ζ, hreg, htrace, hsource, hlimit⟩ := hfull 4 le_rfl ℓ m P Q hk hP₀
    hPi hPE hPQ hQi hQlim hfront hsupport hf hfn hflim U hUp hUR hU1 hUδ hfU X hX ρ hρ hfloor l hl
  exact ⟨g, θ, ζ, (fun n => ⟨(hreg n).2.2.2.1, (hreg n).2.2.2.2⟩), htrace, hsource, (hlimit (Real.log cν)).2⟩

end CauchyHorizon.Tests
