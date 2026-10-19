import CauchyHorizon.Characteristic.BottomLimit

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Tests

-- A smaller width restricts the same family, preserving fields and the common floor.
set_option maxHeartbeats 2000000 in
example {M e Λ A U ρ : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hUA : U ≤ A) (hAR : A < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 A)))
    (X : (T : Ici (0 : ℝ)) → WaveState A T)
    (hX : ∀ T : Ici (0 : ℝ), IsWaveIntegral hA T.property e Λ
      (incomingWaveCurve hA hAR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ T hc hi hrc hr0) (incomingWaveVelocity hAR hp hf) (X T))
    (hfloor : ∀ T u v, ρ ≤ (X T).1 u v 0) :
    let hfU := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hUA) le_rfl)
    ∃ Y : (T : Ici (0 : ℝ)) → WaveState U T,
      (∀ T : Ici (0 : ℝ), IsWaveIntegral hU T.property e Λ
        (incomingWaveCurve hU (hUA.trans_lt hAR) hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ T hc hi hrc hr0) (incomingWaveVelocity (hUA.trans_lt hAR) hp hfU) (Y T)) ∧
      ∀ T u v, (Y T).1 u v = (X T).1 ⟨u, u.property.1, u.property.2.trans hUA⟩ v ∧
        (Y T).2.1 u v = (X T).2.1 ⟨u, u.property.1, u.property.2.trans hUA⟩ v ∧ ρ ≤ (Y T).1 u v 0 := by
  intro hfU
  let Y := fun T : Ici (0 : ℝ) => waveTranslate (a := 0) (U := U) (b := 0) (V := (T : ℝ))
    le_rfl (by simpa only [zero_add] using hUA) le_rfl (by simp) (X T)
  refine ⟨Y, fun T => (hX T).horizon_prefix hA T.property hAR hU T.property hUA le_rfl hc hi hrc hr0 hp hf, ?_⟩
  intro T u v
  have hu : intervalTranslate (a := 0) (U := U) le_rfl (by simpa only [zero_add] using hUA) u =
      (⟨u, u.property.1, u.property.2.trans hUA⟩ : Icc 0 A) := Subtype.ext (zero_add _)
  have hv : intervalTranslate (a := 0) (U := (T : ℝ)) le_rfl (by simp) v = v := Subtype.ext (zero_add _)
  have he : (Y T).1 u v = (X T).1 ⟨u, u.property.1, u.property.2.trans hUA⟩ v := by
    change (X T).1 (intervalTranslate _ _ u) (intervalTranslate _ _ v) = _
    rw [hu, hv]
  refine ⟨he, ?_, ?_⟩
  · change (X T).2.1 (intervalTranslate _ _ u) (intervalTranslate _ _ v) = _
    rw [hu, hv]
  · rw [he]
    exact hfloor T _ v

-- The critical common family supplies every rectangle; the cutoff precedes the sequence and height.
set_option maxHeartbeats 3000000 in
example (B : Background) (hcrit : B.criticalExponent = 3 / 4) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hks : B.innerRate < s) {h r : ℝ → ℝ}
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → ∀ hYZ : Y < Z, Y ≤ R → Z < B.event →
        ∃ U₀ : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ,
          0 < U₀ ∧ U₀ ≤ δ ∧ (∀ ε U, 0 < τ ε U) ∧
          ∀ f : ℕ → ℝ → ℝ, (∀ n, MemLp (f n) 4 (volume.restrict (Icc 0 δ))) →
            (∀ n, (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A) →
            Tendsto (fun n => (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u ∈ Icc η δ, f n u = 0) →
            ∀ (U : ℝ) (hUp : 0 < U) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : ∀ n, MemLp (f n) 4 (volume.restrict (Icc 0 U)))
                (X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T)
                (X₀ : (T : Ici (0 : ℝ)) → WaveState U T)
                (hX : ∀ n (T : Ici (0 : ℝ)), IsWaveIntegral hUp.le T.property B.charge B.cosmological
                  (incomingWaveCurve hUp.le hUR le_rfl (hfU n) (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl (hfU n)) (X n T))
                (_hX₀ : ∀ T : Ici (0 : ℝ), IsWaveIntegral hUp.le T.property B.charge B.cosmological
                  (incomingWaveCurve hUp.le hUR le_rfl (f := 0) (p := 4) MemLp.zero (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl (f := 0) (p := 4) MemLp.zero) (X₀ T)),
                (∀ n T u v, 3 * B.inner / 4 ≤ (X n T).1 u v 0) →
                (∀ T u v, 3 * B.inner / 4 ≤ (X₀ T).1 u v 0) →
                ∀ (ε : Ioi (0 : ℝ)) (t : Ici (0 : ℝ)), τ ε ⟨U, hUp⟩ ≤ t →
                  let T : Ici (0 : ℝ) := ⟨(t : ℝ) + 1, by
                    change 0 ≤ (t : ℝ) + 1
                    exact add_nonneg t.property zero_le_one⟩
                  let v : Icc 0 (T : ℝ) := ⟨t, t.property, (lt_add_one (t : ℝ)).le⟩
                  ∀ χ : ℕ → C(Icc (0 : ℝ) (Z - Y), Icc (0 : ℝ) U),
                    (∀ n w, (X n T).1 (χ n w) v 0 = Z - w) →
                    ∀ (W : C(Icc (0 : ℝ) (Z - Y), ℝ)) (a : ℕ → ℝ), Tendsto a atTop (𝓝 0) →
                      let ν := fun n => radialNuField T.property B.charge B.cosmological
                        (incomingWaveCurve hUp.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose
                      let ζ := fun n w => (r 0 - (χ n w : ℝ)) * f n (χ n w) +
                        scalarTransportCorrection T.property (ν n) (X n T).2.1 (χ n w) v
                      let q := fun n w => Real.exp (B.innerRate * t) * (χ n w : ℝ) * ζ n w /
                        B.criticalWeight (Z - w) - W w * a n
                      ∀ᶠ n in atTop, |∫ w in (0 : ℝ)..(Z - Y),
                        let z := projIcc 0 (Z - Y) (sub_nonneg.2 hYZ.le) w
                        (-1 / (X n T).2.1 (χ n z) v 0) * q n z ^ 2| < (ε : ℝ) := by
  intro hi hr0
  have hm : B.criticalExponent < 1 := by rw [hcrit]; norm_num
  obtain ⟨δ, R, hδ, hR, hband⟩ := B.exists_bottom_flux_small
    hs hH hdH hdHR hA hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, τ, hU₀, hUδ, hτ, hsolve⟩ := hband Y Z hY hYZ hYR hZ
  refine ⟨U₀, τ, hU₀, hUδ, hτ, ?_⟩
  intro f hf hfn hlim hsupport U hUp hUR hUU hfU X X₀ hX hX₀ hfloor hfloor₀ ε t ht T v χ hχ W a ha ν ζ q
  exact hsolve 4 le_rfl f hf hfn hlim hsupport U T hUp.le T.property hUR hUU
    hfU (fun n => X n T) (X₀ T) (fun n => hX n T) (hX₀ T)
    (3 * B.inner / 4) (by have := B.inner_pos; positivity)
    (fun n => hfloor n T) (hfloor₀ T) ε hUp v (lt_add_one (t : ℝ)) ht χ hχ W a ha

end CauchyHorizon.Tests
