import CauchyHorizon.Characteristic.MatchedFamily
import CauchyHorizon.Characteristic.HistoryConvergence
import CauchyHorizon.Analysis.HistoryTail
import CauchyHorizon.Characteristic.RadiusNormalization
import CauchyHorizon.Characteristic.AuxiliaryRadiationEnergy

/-! Full half-line comparison on a fixed radius of one actual common family. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 6000000 in
theorem exists_common_radius_radiation (B : Background) {s H dH A E : ℝ}
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
    let cθ := fun Y => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - Y) * Ch
    let cζ := fun Y => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - Y) * Ch
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R →
        ∃ τ : Ioi (0 : ℝ) → ℝ, (∀ U, 0 < τ U) ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ m : ℕ → ℝ) (P Q : ℕ → ℝ →ᵇ ℝ),
            B.innerRate ≤ B.outerRate * (1 - 1 / p.toReal) → P 0 = 0 →
            (∀ n, Integrable (fun t => P n t ^ 2)) → (∀ n, (∫ t, P n t ^ 2) ≤ E) →
            (∀ n t, HasDerivAt (P n) (Q n t) t) → (∀ n, Integrable (fun t => Q n t ^ 2)) →
            Tendsto (fun n => ∫ t, Q n t ^ 2) atTop (𝓝 0) →
            Tendsto (fun n => m n - ℓ n) atTop atTop → (∀ n t, t ≤ m n → P n t = 0) →
            (∀ n, MemLp (logarithmicIncoming b (ℓ n) (P n)) p (volume.restrict (Icc 0 δ))) →
            (∀ n, (eLpNorm (logarithmicIncoming b (ℓ n) (P n)) p (volume.restrict (Icc 0 δ))).toReal ≤ A) →
            Tendsto (fun n => (eLpNorm (logarithmicIncoming b (ℓ n) (P n)) p
              (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            ∀ (U : ℝ) (hUp : 0 < U) (hUR : U < r 0), U ≤ 1 → U ≤ δ →
              ∀ (hfU : ∀ n, MemLp (logarithmicIncoming b (ℓ n) (P n)) p (volume.restrict (Icc 0 U)))
                (X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T)
                (hX : ∀ n (T : Ici (0 : ℝ)), IsWaveIntegral hUp.le T.property B.charge B.cosmological
                  (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp (hfU n)) (X n T)),
                ∀ ρ : ℝ, 0 < ρ → (∀ n T u v, ρ ≤ (X n T).1 u v 0) →
                  ∀ l : ℝ, τ ⟨U, hUp⟩ ≤ l →
                    ∃ g θ ζ : ℕ → ℝ → ℝ,
                      (∀ n, ContinuousOn (g n) (Ici l) ∧ ContinuousOn (θ n) (Ici l) ∧
                        ContinuousOn (ζ n) (Ici l) ∧ MemLp (θ n) 2 (volume.restrict (Ici l)) ∧
                          MemLp (ζ n) 2 (volume.restrict (Ici l))) ∧
                      (∀ n t, l ≤ t → ∀ (T : Ici (0 : ℝ)) (htT : t ∈ Icc 0 (T : ℝ)),
                        let u := projIcc 0 U hUp.le (g n t)
                        let v : Icc 0 (T : ℝ) := ⟨t, htT⟩
                        let ν := radialNuField T.property B.charge B.cosmological
                          (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose
                        g n t ∈ Ioo 0 U ∧ (X n T).1 u v 0 = Y ∧
                          θ n t = Real.exp (B.innerRate * t) * (Y * (X n T).2.1 u v 1) ∧
                          ζ n t = Real.exp (B.innerRate * t) * g n t *
                            ((r 0 - g n t) * logarithmicIncoming b (ℓ n) (P n) (g n t) +
                              scalarTransportCorrection T.property ν (X n T).2.1 u v) / B.criticalWeight Y) ∧
                      (∀ n,
                        let A := fun t => B.criticalWeight Y /
                          (Real.exp (-1) * (-B.F Y) / B.outerRate) * |ζ n t|
                        ContinuousOn A (Ici l) ∧ MemLp A 2 (volume.restrict (Ici l)) ∧
                          (∀ T : Ici (0 : ℝ),
                            let ν := radialNuField T.property B.charge B.cosmological
                              (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose
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
                                (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0))
                                (X n V).1 (hX n V).choose) g₀ T₀ β Y L S →
                            ∀ b₀ : Icc 0 (V : ℝ), max (l' : ℝ) T₀ ≤ (b₀ : ℝ) / (1 + β) → S ≤ b₀ →
                              AuxiliaryRadiationEstimate B hUp.le V.property (X n V) (g n) g₀ β Y L
                                l' b₀ A) ∧
                      ∀ d : ℝ,
                        (∀ n, MemLp (fun t => θ n t - θ 0 t - cθ Y * P n (B.outerRate * t + ℓ n + d))
                            2 (volume.restrict (Ici l)) ∧
                          MemLp (fun t => ζ n t - ζ 0 t - cζ Y * P n (B.outerRate * t + ℓ n + d))
                            2 (volume.restrict (Ici l))) ∧
                        Tendsto (fun n => ∫ t in Ici l,
                          (θ n t - θ 0 t - cθ Y * P n (B.outerRate * t + ℓ n + d)) ^ 2 +
                            (ζ n t - ζ 0 t - cζ Y * P n (B.outerRate * t + ℓ n + d)) ^ 2) atTop (𝓝 0) := by
  classical
  intro b hi hr0 cν Ch cθ cζ
  obtain ⟨δ₀, R₀, hδ₀, hR₀, hlate⟩ := B.exists_common_family_matched_small
    hs hH hdH hdHR hA hE hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δν, Rν, _hδν, hRν, hnorm⟩ := B.exists_physical_radius_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  let δ := max δ₀ δν
  let R := min R₀ Rν
  have hR : R ∈ Ioo B.inner B.event :=
    ⟨lt_min hR₀.1 hRν.1, (min_le_left _ _).trans_lt hR₀.2⟩
  refine ⟨δ, R, hδ₀.trans_le (le_max_left _ _), hR, ?_⟩
  intro Y hY hYR
  obtain ⟨σ, _hσ, hphysicalNorm⟩ := hnorm Y hY (hYR.trans (min_le_right _ _))
  obtain ⟨Z₁, τ₁, _hZ₁, _hcap₁, hτ₁, hbase⟩ :=
    hlate Y 1 1 hY (hYR.trans (min_le_left _ _)) zero_lt_one zero_lt_one
  let τ := fun U => max (τ₁ U) (σ ⟨1, by norm_num⟩ U)
  refine ⟨τ, fun U => (hτ₁ U).trans_le (le_max_left _ _), ?_⟩
  intro p hp ℓ m P Q hcrit hP₀ hPi hPE hPQ hQi hQlim hfront hsupport hf hfn hflim
    U hUp hUR hU1 hUδ hfU X hX ρ hρ hfloor l hl
  have hlbase : τ₁ ⟨U, hUp⟩ ≤ l := (le_max_left _ _).trans hl
  have hlnorm : σ ⟨1, by norm_num⟩ ⟨U, hUp⟩ ≤ l := (le_max_right _ _).trans hl
  have hl0 : 0 < l := (hτ₁ ⟨U, hUp⟩).trans_le hlbase
  let hf₀ := fun n => (hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_left δ₀ δν)) le_rfl)
  have hfn₀ (n : ℕ) := (scalar_prefix_norm_le (le_max_left δ₀ δν) (hf n)).trans (hfn n)
  have hflim₀ := squeeze_zero (fun n => ENNReal.toReal_nonneg)
    (fun n => scalar_prefix_norm_le (le_max_left δ₀ δν) (hf n)) hflim
  have hfzero : logarithmicIncoming b (ℓ 0) (P 0) = 0 := by
    ext u
    simp only [logarithmicIncoming, hP₀, BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero]
  have hX₀ (T : Ici (0 : ℝ)) : IsWaveIntegral hUp.le T.property B.charge B.cosmological
      (incomingWaveCurve hUp.le hUR hp (f := 0) MemLp.zero (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
      (incomingWaveVelocity hUR hp (f := 0) MemLp.zero) (X 0 T) := by
    simpa only [hfzero] using hX 0 T
  obtain ⟨g, Eθ, Eζ, hreg, hbaseTrace, hunique, _hbaseSmall⟩ := hbase p hp ℓ m P Q hcrit
    hPi hPE hPQ hQi hQlim hfront hsupport hf₀ hfn₀ hflim₀ U hUp hUR hfU X (X 0) hX hX₀
      ρ hρ hfloor (hfloor 0) l hlbase
  let phase := fun n d t => B.outerRate * t + ℓ n + d
  have hphaseD (n : ℕ) (d t : ℝ) : HasDerivAt (phase n d) B.outerRate t := by
    simpa only [phase, id_eq, mul_one] using (((hasDerivAt_id t).const_mul B.outerRate).add_const (ℓ n)).add_const d
  have hphaseC (n : ℕ) (d : ℝ) : Continuous (phase n d) := by dsimp only [phase]; fun_prop
  have hprofile (n : ℕ) (d S : ℝ) : MemLp (fun t => P n (phase n d t)) 2 (volume.restrict (Ici S)) :=
    (timeChange_l2_halfline B.outerRate_pos (hphaseC n d).continuousOn
      (fun t _ => hphaseD n d t) (fun _ _ => le_rfl) (P n).continuous (hPi n)).1
  have hphaseEq (n : ℕ) (Z t : ℝ) :
      B.outerRate * t + ℓ n + Real.log cν - Real.log (B.z Z) = phase n (Real.log cν - Real.log (B.z Z)) t := by
    dsimp only [phase]; ring
  let d₁ := Real.log cν - Real.log (B.z Z₁)
  let θ := fun n t => Eθ n t + cθ Y * P n (phase n d₁ t)
  let ζ := fun n t => Eζ n t + cζ Y * P n (phase n d₁ t)
  have hregular (n : ℕ) : ContinuousOn (g n) (Ici l) ∧ ContinuousOn (θ n) (Ici l) ∧
      ContinuousOn (ζ n) (Ici l) ∧ MemLp (θ n) 2 (volume.restrict (Ici l)) ∧
        MemLp (ζ n) 2 (volume.restrict (Ici l)) := by
    have hpc := ((P n).continuous.comp (hphaseC n d₁)).continuousOn (s := Ici l)
    exact ⟨(hreg n).1, (hreg n).2.1.add (hpc.const_mul _),
      (hreg n).2.2.1.add (hpc.const_mul _),
      (hreg n).2.2.2.1.add ((hprofile n d₁ l).const_mul _),
      (hreg n).2.2.2.2.add ((hprofile n d₁ l).const_mul _)⟩
  have htrace (n : ℕ) (t : ℝ) (ht : l ≤ t) (T : Ici (0 : ℝ)) (htT : t ∈ Icc 0 (T : ℝ)) :=
    hbaseTrace n t ht T htT
  have hθ (n : ℕ) (t : ℝ) (ht : l ≤ t) (T : Ici (0 : ℝ)) (htT : t ∈ Icc 0 (T : ℝ)) :
      θ n t = Real.exp (B.innerRate * t) * (Y * (X n T).2.1 (projIcc 0 U hUp.le (g n t)) ⟨t, htT⟩ 1) := by
    dsimp only [θ]
    rw [(htrace n t ht T htT).2.2.1, hphaseEq]
    dsimp only [cθ, d₁]
    ring
  have hζ (n : ℕ) (t : ℝ) (ht : l ≤ t) (T : Ici (0 : ℝ)) (htT : t ∈ Icc 0 (T : ℝ)) :
      ζ n t = Real.exp (B.innerRate * t) * g n t *
        ((r 0 - g n t) * logarithmicIncoming b (ℓ n) (P n) (g n t) +
          scalarTransportCorrection T.property
            (radialNuField T.property B.charge B.cosmological
              (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose)
            (X n T).2.1 (projIcc 0 U hUp.le (g n t)) ⟨t, htT⟩) / B.criticalWeight Y := by
    dsimp only [ζ]
    rw [(htrace n t ht T htT).2.2.2, hphaseEq]
    dsimp only [cζ, d₁]
    ring
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have hfnU (n : ℕ) := (scalar_prefix_norm_le hUδ (hf n)).trans (hfn n)
  have hflimU := squeeze_zero (fun n => ENNReal.toReal_nonneg)
    (fun n => scalar_prefix_norm_le hUδ (hf n)) hflim
  have hescape := logarithmicIncoming_eventually_zero b hfront hsupport
  have hhistory (S : ℝ) (hS : l ≤ S) : Tendsto (fun n => ∫ t in l..S,
      (θ n t - θ 0 t) ^ 2 + (ζ n t - ζ 0 t) ^ 2) atTop (𝓝 0) := by
    let T : Ici (0 : ℝ) := ⟨S, hl0.le.trans hS⟩
    let χ : ℕ → C(Icc l S, Icc (0 : ℝ) U) := fun n =>
      ⟨fun t => projIcc 0 U hUp.le (g n t),
        continuous_projIcc.comp ((hreg n).1.mono Icc_subset_Ici_self).domRestrict⟩
    have hhit (n : ℕ) (t : Icc l S) :
        (X n T).1 (χ n t) ⟨t, hl0.le.trans t.property.1, t.property.2⟩ 0 = Y :=
      (htrace n t t.property.1 T ⟨hl0.le.trans t.property.1, t.property.2⟩).2.1
    have hpos (t : Icc l S) : 0 < (χ 0 t : ℝ) := by
      have hh := (htrace 0 t t.property.1 T ⟨hl0.le.trans t.property.1, t.property.2⟩).1
      change 0 < (projIcc 0 U hUp.le (g 0 t) : ℝ)
      rw [projIcc_of_mem hUp.le ⟨hh.1.le, hh.2.le⟩]
      exact hh.1
    have hh := (IsWaveIntegral.horizon_scalar_history_tendsto B hUp.le hU1 T.property hUR
      hl0.le hS le_rfl hc hi hrc hr0 hφ hrd hρ hA hp hfU hfnU hflimU
      (fun η hη => (hescape.1 η hη).mono (fun _ hh u hu => hh u hu.1))
      (fun n => hX n T) (hX₀ T) (fun n => hfloor n T) (hfloor 0 T)
      χ (χ 0) hhit (hhit 0) hpos).2.2.2.2
    apply hh.congr
    intro n
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc l S := by simpa only [uIcc_of_le hS] using ht
    simp only [projIcc_of_mem hS ht']
    rw [hθ n t ht'.1 T ⟨hl0.le.trans ht'.1, ht'.2⟩,
      hθ 0 t ht'.1 T ⟨hl0.le.trans ht'.1, ht'.2⟩,
      hζ n t ht'.1 T ⟨hl0.le.trans ht'.1, ht'.2⟩,
      hζ 0 t ht'.1 T ⟨hl0.le.trans ht'.1, ht'.2⟩]
    have hg0 := (htrace 0 t ht'.1 T ⟨hl0.le.trans ht'.1, ht'.2⟩).1
    have hgn := (htrace n t ht'.1 T ⟨hl0.le.trans ht'.1, ht'.2⟩).1
    simp only [χ, ContinuousMap.coe_mk, hfzero, Pi.zero_apply, mul_zero, zero_add,
      projIcc_of_mem hUp.le ⟨hg0.1.le, hg0.2.le⟩, projIcc_of_mem hUp.le ⟨hgn.1.le, hgn.2.le⟩]
  refine ⟨g, θ, ζ, hregular, ?_, ?_, ?_⟩
  · intro n t ht T htT
    exact ⟨(htrace n t ht T htT).1, (htrace n t ht T htT).2.1,
      hθ n t ht T htT, hζ n t ht T htT⟩
  · intro n
    dsimp only
    suffices hsource : ∀ T : Ici (0 : ℝ),
        let ν := radialNuField T.property B.charge B.cosmological
          (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose
        ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 (T : ℝ), l ≤ v →
          (X n T).1 (projIcc 0 U hUp.le u) v 0 = Y →
            Real.exp (B.innerRate * v) *
              |(X n T).1 (projIcc 0 U hUp.le u) v 0 * (X n T).2.2 u v 1| ≤
                (-ν (projIcc 0 U hUp.le u) v) *
                  (B.criticalWeight Y / (Real.exp (-1) * (-B.F Y) / B.outerRate) * |ζ n v|) by
      refine ⟨(hregular n).2.2.1.abs.const_mul _, (hregular n).2.2.2.2.norm.const_mul _, hsource, ?_⟩
      intro V l' hll' T₀ β L S g₀ hβ hL hg₀ hcharts b₀ hstart hS
      have hYband : Y ∈ Ioo B.inner B.event := ⟨hY, hYR.trans_lt hR.2⟩
      have hcoef : 0 ≤ B.criticalWeight Y / (Real.exp (-1) * (-B.F Y) / B.outerRate) :=
        (div_pos (B.criticalWeight_pos hYband)
          (div_pos (mul_pos (Real.exp_pos _) (neg_pos.2 (B.F_neg hYband))) B.outerRate_pos)).le
      exact (hX n V).auxiliary_radiation_energy B hUp.le V.property hUR hc hi hrc hr0 hφ hrd hp (hfU n)
        hβ hY hL l' b₀ hstart hS (g n) g₀ _ ((hregular n).1.mono (Ici_subset_Ici.2 hll')) hg₀
        (((hregular n).2.2.1.abs.const_mul _).mono (Ici_subset_Ici.2 hll'))
        (fun t _ => mul_nonneg hcoef (abs_nonneg (ζ n t)))
        (fun b hb => (htrace n b (hll'.trans hb) V b.property).2.1) hcharts (by
          filter_upwards [hsource V] with u hu
          intro v hv
          exact hu v (hll'.trans hv))
    intro T
    let ν := radialNuField T.property B.charge B.cosmological
      (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose
    have hif : ∀ᵐ u ∂volume.restrict (Icc 0 U),
        incomingWaveVelocity hUR hp (hfU n) u 1 = logarithmicIncoming b (ℓ n) (P n) u := by
      filter_upwards [incomingWaveVelocity_ae hUR hp (hfU n)] with u hu
      rw [hu]
      rfl
    filter_upwards [(hX n T).zeta_transport (hX n T).choose
      (incomingWave_constraint_data hUp.le hUR hp (hfU n) (horizonPhi h r 0)).1,
      hif, ae_restrict_mem measurableSet_Icc] with u hz hifU hu
    intro v hv hrad
    let w := projIcc 0 U hUp.le u
    have hwu : (w : ℝ) = u := by simp only [w, projIcc_of_mem hUp.le hu]
    have hgu : u = g n v := by
      simpa only [hwu] using hunique n v hv T v.property w hrad
    have hζv : ζ n v = Real.exp (B.innerRate * v) * u *
        ((X n T).1 w v 0 * (X n T).2.2 u v 1) / B.criticalWeight Y := by
      have hh := hζ n v hv T v.property
      rw [← hgu] at hh
      have he := hz v
      rw [hifU] at he
      simp only [incomingWaveCurve_apply, Matrix.cons_val_zero, incomingRadius] at he
      change (X n T).1 w v 0 * (X n T).2.2 u v 1 =
        (r 0 - (w : ℝ)) * logarithmicIncoming b (ℓ n) (P n) u +
          scalarTransportCorrection T.property ν (X n T).2.1 w v at he
      rw [hwu] at he
      change ζ n v = Real.exp (B.innerRate * v) * u *
        ((r 0 - u) * logarithmicIncoming b (ℓ n) (P n) u +
          scalarTransportCorrection T.property ν (X n T).2.1 w v) / B.criticalWeight Y at hh
      rw [← he] at hh
      exact hh
    have hnormal := hphysicalNorm p hp (logarithmicIncoming b (ℓ n) (P n))
      ((hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_right δ₀ δν)) le_rfl))
      ((scalar_prefix_norm_le (le_max_right δ₀ δν) (hf n)).trans (hfn n))
      ⟨1, by norm_num⟩ ⟨U, hUp⟩ U T hUp.le T.property hUR le_rfl (hfU n) (X n T) (hX n T)
      w v (hlnorm.trans hv) hrad
    have hu0 : 0 < u := by simpa only [w, projIcc_of_mem hUp.le hu] using hnormal.1
    have hn : ν w v < 0 :=
      ((hX n T).interior_gauge hUp.le T.property hUR hc hi hrc hr0 hφ hrd hp (hfU n) w v).2.2.1
    have hF : 0 < -B.F Y := neg_pos.2 (B.F_neg ⟨hY, hYR.trans_lt hR.2⟩)
    have hq : 0 < B.criticalWeight Y := B.criticalWeight_pos ⟨hY, hYR.trans_lt hR.2⟩
    let n₀ := Real.exp (-1) * (-B.F Y) / B.outerRate
    have hn₀ : 0 < n₀ := div_pos (mul_pos (Real.exp_pos _) hF) B.outerRate_pos
    let Q := B.outerRate * (u * (-ν w v)) / (-B.F Y)
    have hQ : 0 < Q := div_pos (mul_pos B.outerRate_pos (mul_pos hu0 (neg_pos.2 hn))) hF
    have hlog : |Real.log Q| < 1 := by
      have heq : B.outerRate * (u * ν w v / B.F Y) = Q := by dsimp only [Q]; ring
      have hh := hnormal.2
      change |Real.log (B.outerRate * ((w : ℝ) * ν w v / B.F Y))| < 1 at hh
      rwa [hwu, heq] at hh
    have hQl : Real.exp (-1) ≤ Q := by
      rw [← Real.exp_log hQ]
      exact Real.exp_le_exp.2 (abs_le.1 hlog.le).1
    have hscale : n₀ ≤ u * (-ν w v) := by
      apply (div_le_iff₀ B.outerRate_pos).2
      simpa only [mul_comm B.outerRate] using (le_div_iff₀ hF).1 hQl
    let S := Real.exp (B.innerRate * v) * |(X n T).1 w v 0 * (X n T).2.2 u v 1|
    have hS : 0 ≤ S := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
    have hζabs : B.criticalWeight Y * |ζ n v| = u * S := by
      rw [hζv, abs_div, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hu0, abs_of_pos hq]
      dsimp only [S]
      field_simp [hq.ne']
    change S ≤ (-ν w v) * (B.criticalWeight Y / n₀ * |ζ n v|)
    rw [show (-ν w v) * (B.criticalWeight Y / n₀ * |ζ n v|) =
      (-ν w v) * (B.criticalWeight Y * |ζ n v|) / n₀ by ring]
    apply (le_div_iff₀ hn₀).2
    rw [hζabs]
    nlinarith only [mul_le_mul_of_nonneg_right hscale hS]
  intro d
  let F := fun n t => θ n t - cθ Y * P n (phase n d t)
  let G := fun n t => ζ n t - cζ Y * P n (phase n d t)
  have hF (n : ℕ) : MemLp (F n) 2 (volume.restrict (Ici l)) :=
    (hregular n).2.2.2.1.sub ((hprofile n d l).const_mul _)
  have hG (n : ℕ) : MemLp (G n) 2 (volume.restrict (Ici l)) :=
    (hregular n).2.2.2.2.sub ((hprofile n d l).const_mul _)
  have hhist (S : ℝ) (hS : l ≤ S) : Tendsto (fun n => ∫ t in l..S,
      (F n t - θ 0 t) ^ 2 + (G n t - ζ 0 t) ^ 2) atTop (𝓝 0) := by
    apply (hhistory S hS).congr'
    filter_upwards [hescape.2 (B.outerRate * S + d)] with n hn
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ≤ S := by rw [uIcc_of_le hS] at ht; exact ht.2
    have hz : P n (phase n d t) = 0 := by
      have hh := hn (B.outerRate * t + d) (add_le_add (mul_le_mul_of_nonneg_left ht' B.outerRate_pos.le) le_rfl)
      simpa only [phase, add_comm (ℓ n), add_assoc] using hh
    simp only [F, G, hz, mul_zero, sub_zero]
  have htail : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ S : ℝ, T ≤ S →
      ∀ᶠ n in atTop, (∫ t in Ici S, F n t ^ 2 + G n t ^ 2) < ε := by
    intro ε hε
    let η := Real.sqrt (ε / 4)
    have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
    have hηsq : η ^ 2 = ε / 4 := Real.sq_sqrt (by positivity)
    obtain ⟨Z, τ, _hZ, _hcap, _hτ, hsmall⟩ :=
      hlate Y 1 η hY (hYR.trans (min_le_left _ _)) zero_lt_one hη
    refine ⟨max l (τ ⟨U, hUp⟩), ?_⟩
    intro S hS
    have hlS := (le_max_left l (τ ⟨U, hUp⟩)).trans hS
    have hτS := (le_max_right l (τ ⟨U, hUp⟩)).trans hS
    obtain ⟨g', Eθ', Eζ', hreg', htrace', _hunique', hbound⟩ := hsmall p hp ℓ m P Q hcrit
      hPi hPE hPQ hQi hQlim hfront hsupport hf₀ hfn₀ hflim₀ U hUp hUR hfU X (X 0) hX hX₀
        ρ hρ hfloor (hfloor 0) S hτS
    let d' := Real.log cν - Real.log (B.z Z)
    let D := fun n t => P n (phase n d' t) - P n (phase n d t)
    have hD (n : ℕ) := phaseChange_l2_halfline (l := S) B.outerRate_pos (abs_nonneg (d' - d))
      (hphaseC n d).continuousOn (hphaseC n d').continuousOn
      (fun t _ => hphaseD n d t) (fun t _ => hphaseD n d' t)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl)
      (fun t _ => by dsimp only [phase]; rw [show B.outerRate * t + ℓ n + d' -
        (B.outerRate * t + ℓ n + d) = d' - d by ring])
      (P n).continuous (Q n).continuous (hPQ n) (hQi n)
    let C := 2 * (cθ Y ^ 2 + cζ Y ^ 2) * (|d' - d| ^ 2 / B.outerRate)
    have hClim : Tendsto (fun n => C * ∫ t, Q n t ^ 2) atTop (𝓝 0) := by
      simpa only [mul_zero] using hQlim.const_mul C
    filter_upwards [hbound, hClim.eventually_lt_const (show 0 < ε / 2 by positivity)] with n hn hCn
    have hmatch (t : ℝ) (ht : S ≤ t) :
        F n t = Eθ' n t + cθ Y * D n t ∧ G n t = Eζ' n t + cζ Y * D n t := by
      let T : Ici (0 : ℝ) := ⟨max 0 t + 1, by change 0 ≤ max 0 t + 1; positivity⟩
      have htT : t ∈ Icc 0 (T : ℝ) := ⟨hl0.le.trans (hlS.trans ht),
        (le_max_right 0 t).trans (le_add_of_nonneg_right zero_le_one)⟩
      have hh := htrace' n t ht T htT
      have hg : g' n t = g n t := by
        have hmem : g' n t ∈ Icc 0 U := ⟨hh.1.1.le, hh.1.2.le⟩
        have hh' := hunique n t (hlS.trans ht) T htT (projIcc 0 U hUp.le (g' n t)) hh.2.1
        simpa only [projIcc_of_mem hUp.le hmem] using hh'
      constructor
      · dsimp only [F, D]
        rw [hθ n t (hlS.trans ht) T htT, hh.2.2.1, hg, hphaseEq]
        dsimp only [cθ, d']
        ring
      · dsimp only [G, D]
        rw [hζ n t (hlS.trans ht) T htT, hh.2.2.2, hg, hphaseEq]
        dsimp only [cζ, d']
        ring
    have hEi : IntegrableOn (fun t => Eθ' n t ^ 2 + Eζ' n t ^ 2) (Ici S) :=
      ((memLp_two_iff_integrable_sq (hreg' n).2.2.2.1.aestronglyMeasurable).1 (hreg' n).2.2.2.1).add
      ((memLp_two_iff_integrable_sq (hreg' n).2.2.2.2.aestronglyMeasurable).1 (hreg' n).2.2.2.2)
    have hDi : IntegrableOn (fun t => D n t ^ 2) (Ici S) :=
      (memLp_two_iff_integrable_sq (hD n).1.aestronglyMeasurable).1 (hD n).1
    have hFi : IntegrableOn (fun t => F n t ^ 2 + G n t ^ 2) (Ici l) :=
      ((memLp_two_iff_integrable_sq (hF n).aestronglyMeasurable).1 (hF n)).add
      ((memLp_two_iff_integrable_sq (hG n).aestronglyMeasurable).1 (hG n))
    have hbnd : (∫ t in Ici S, F n t ^ 2 + G n t ^ 2) ≤
        2 * (∫ t in Ici S, Eθ' n t ^ 2 + Eζ' n t ^ 2) + C * ∫ t, Q n t ^ 2 := by
      have hh := integral_mono_ae (hFi.mono_set (Ici_subset_Ici.2 hlS))
        ((hEi.const_mul 2).add (hDi.const_mul (2 * (cθ Y ^ 2 + cζ Y ^ 2))))
        ((ae_restrict_mem measurableSet_Ici).mono (fun t ht => by
          change F n t ^ 2 + G n t ^ 2 ≤
            2 * (Eθ' n t ^ 2 + Eζ' n t ^ 2) + 2 * (cθ Y ^ 2 + cζ Y ^ 2) * D n t ^ 2
          rw [(hmatch t ht).1, (hmatch t ht).2]
          nlinarith only [sq_nonneg (Eθ' n t - cθ Y * D n t), sq_nonneg (Eζ' n t - cζ Y * D n t)]))
      change (∫ t in Ici S, F n t ^ 2 + G n t ^ 2) ≤
        ∫ t in Ici S, 2 * (Eθ' n t ^ 2 + Eζ' n t ^ 2) + 2 * (cθ Y ^ 2 + cζ Y ^ 2) * D n t ^ 2 at hh
      rw [integral_add (hEi.const_mul 2) (hDi.const_mul _), integral_const_mul, integral_const_mul] at hh
      exact hh.trans (add_le_add le_rfl ((mul_le_mul_of_nonneg_left (hD n).2 (by positivity)).trans_eq (by dsimp only [C]; ring)))
    have hEnonneg : 0 ≤ ∫ t in Ici S, Eθ' n t ^ 2 + Eζ' n t ^ 2 :=
      integral_nonneg (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hEsq := Real.sq_sqrt hEnonneg
    have hEsmall : (∫ t in Ici S, Eθ' n t ^ 2 + Eζ' n t ^ 2) < ε / 4 := by
      nlinarith only [hn, Real.sqrt_nonneg (∫ t in Ici S, Eθ' n t ^ 2 + Eζ' n t ^ 2), hEsq, hηsq, hη]
    linarith only [hbnd, hEsmall, hCn]
  have hlim := pair_energy_tendsto_of_history_tail hF hG
    (hregular 0).2.2.2.1 (hregular 0).2.2.2.2 hhist htail
  have heqθ (n : ℕ) : (fun t => θ n t - θ 0 t - cθ Y * P n (phase n d t)) =
      (fun t => F n t - θ 0 t) := by ext t; dsimp only [F]; ring
  have heqζ (n : ℕ) : (fun t => ζ n t - ζ 0 t - cζ Y * P n (phase n d t)) =
      (fun t => G n t - ζ 0 t) := by ext t; dsimp only [G]; ring
  refine ⟨fun n => ⟨?_, ?_⟩, ?_⟩
  · change MemLp (fun t => θ n t - θ 0 t - cθ Y * P n (phase n d t)) 2 _
    rw [heqθ]
    exact (hF n).sub (hregular 0).2.2.2.1
  · change MemLp (fun t => ζ n t - ζ 0 t - cζ Y * P n (phase n d t)) 2 _
    rw [heqζ]
    exact (hG n).sub (hregular 0).2.2.2.2
  · convert hlim using 1
    ext n
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by
      change (θ n t - θ 0 t - cθ Y * P n (phase n d t)) ^ 2 +
          (ζ n t - ζ 0 t - cζ Y * P n (phase n d t)) ^ 2 = _
      rw [congrFun (heqθ n) t, congrFun (heqζ n) t])

end CauchyHorizon.Background
