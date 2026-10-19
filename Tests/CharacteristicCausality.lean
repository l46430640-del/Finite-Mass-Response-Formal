import CauchyHorizon.Reduced.LocalWeakExtension

open Set Filter
open scoped Topology

namespace CauchyHorizon.Tests

-- Regular-time normalization agrees with the actual lapse even on the initial sides.
example {U : ℝ} (hU : 0 ≤ U) (X : (S : Ici (0 : ℝ)) → WaveState U S) {ψ : ℝ → ℝ}
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hψ : IsRegularTimeCoordinate (anchoringLapse hU X) (-1) ψ)
    (S : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htS : t ≤ S)
    (u : Icc 0 U) (ω : UnitSphere) :
    let z := originalSpacetimeField hU X ψ ((regularTime (anchoringLapse hU X) t, u), ω)
    Real.exp (z 2) * anchoringLapse hU X t = Real.exp ((X S).1 u ⟨t, ht, htS⟩ 2) := by
  dsimp only
  have hz := originalSpacetimeField_apply hU X hX hψ S t ht htS u ω
  have ha : anchoringLapse hU X t = Real.exp ((X S).1 ⟨U, hU, le_rfl⟩ ⟨t, ht, htS⟩ 2) := by
    unfold anchoringLapse
    rw [max_eq_right ht, renormalizedWaveRow_apply hU X hX S ht htS]
    simp
  rw [hz, Pi.sub_apply, if_pos rfl, ha, ← Real.exp_add, sub_add_cancel]

-- The dependence statement before the horizon quantifies over a nonempty curve class.
example (ω : UnitSphere) :
    ∃ γ : ℝ → SphericalSpacetime,
      IsPastInextendibleCausalCurve (characteristicCrossingRegion (-3) 4 (-1) 1 1 3)
        (fun _ => 1) (fun _ => 1) γ ∧ γ 0 = ((-1 / 2, 2), ω) := by
  apply exists_past_curve_before_characteristic_horizon
    (by norm_num : (-3 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (3 : ℝ) < 4) (fun _ => 1) (fun _ => 1)
  · norm_num [sphericalOpenRectangle]
  · norm_num

-- Both original characteristic faces, including the corner, belong to the same initial set.
example {vi U : ℝ} (hvi : vi < 0) (hU : 0 < U) (ω : UnitSphere) :
    ((vi, 0), ω) ∈ characteristicInitialSides vi U ∧
      ((vi / 2, 0), ω) ∈ characteristicInitialSides vi U ∧
      ((vi, U / 2), ω) ∈ characteristicInitialSides vi U := by
  refine ⟨Or.inl ⟨rfl, le_rfl, hU⟩, Or.inr ?_, Or.inl ?_⟩
  · exact ⟨by dsimp; linarith, by dsimp; linarith, rfl⟩
  · exact ⟨rfl, by dsimp; linarith, by dsimp; linarith⟩

-- The strengthened final predicate keeps the same X, y, and actual embedding E.
example {U ε e Λ T₀ u₀ : ℝ} {hε : 0 ≤ ε} {hεU : ε ≤ U}
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    (h : HasLocalSphericalWeakExtension hε hεU e Λ X χ T₀ u₀) :
    let V := regularTime (anchoringLapse (hε.trans hεU) X)
    ∃ ua L T b : ℝ, ∃ hW : 0 ≤ b - V T, ∃ hL : 0 ≤ L,
    ∃ y : WaveState (b - V T) L,
    ∃ E : OpenPartialHomeomorph SphericalSpacetime SphericalSpacetime,
      HasSphericalWeakSolution hW hL e Λ y ∧
      IsRegularSpacetimeEmbedding (anchoringLapse (hε.trans hεU) X) χ T ua (ua + L) E ∧
      HasCharacteristicCauchyHorizon (hε.trans hεU) X hW hL y (V T) ua ∧
      ∃ F : SphericalSpacetime → WaveVector,
        (∀ p ∈ sphericalOpenRectangle (V T) b ua (ua + L),
          F p = crossingSpacetimeField hW hL y (V T) ua p) ∧
        let M := characteristicCrossingRegion (V (-1)) U (V T) b ua (ua + L)
        let N := sphericalOpenRectangle (V T) b ua (ua + L)
        let H := fun p => Real.exp (F p 2)
        let R := fun p => F p 0 ^ 2
        N ∩ futureDomainOfDependence M H R (characteristicInitialSides (V 0) U) = E.target ∧
          N ∩ futureCauchyHorizon M H R (characteristicInitialSides (V 0) U) =
            ({0} ×ˢ Ioo ua (ua + L)) ×ˢ univ := by
  obtain ⟨_hχ, ua, L, T, b, _hea, _ham, _hmr, _hrU, _hT₀, _hT, _hn, _hb,
    hL, hW, y, hy, _himage, E, hE, _hdomain, _hfrontier, _hcausal, hchar, _hcharts, _hpast⟩ := h
  refine ⟨ua, L, T, b, hW, hL, y, E, hy, hE, hchar, ?_⟩
  obtain ⟨F, _hc, _hr, _horiginal, hcross, hD, hH⟩ := hchar
  rw [add_sub_cancel] at hcross hD hH
  exact ⟨F, hcross, hD.trans hE.2.1.symm, hH⟩

end CauchyHorizon.Tests
