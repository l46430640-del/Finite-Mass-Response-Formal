import CauchyHorizon.Characteristic.MatchedBand
import CauchyHorizon.Characteristic.BandOverlap
import CauchyHorizon.Analysis.CompatibleHalfline

/-! The actual matched scalar error on a half-line, with one fixed bottom inflow. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 4000000 in
theorem exists_matched_halfline_energy (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hm : B.criticalExponent < 1) (hks : B.innerRate < s)
    {h rH : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous rH) (hrb : ∀ t, B.event - dH ≤ rH t) (hrinit : B.inner < rH 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt rH
      (horizonFunction (rH t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖rH t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h rH s) :
    let b := B.criticalExponent
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (rH t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    let Ch := rH 0 / (B.event * cν ^ b)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y cap e : ℝ, B.inner < Y → Y ≤ R → 0 < cap → 0 < e →
        ∃ Z U₀ C L : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ,
          Z ∈ Ioo Y B.event ∧ B.event - cap < Z ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < C ∧ 0 < L ∧
          ∀ (p₀ : ℝ≥0∞) (hp₀ : 4 ≤ p₀) (ℓ : ℝ) (P Q : ℝ →ᵇ ℝ),
            B.innerRate ≤ B.outerRate * (1 - 1 / p₀.toReal) → Integrable (fun t => P t ^ 2) →
            (∀ t, HasDerivAt P (Q t) t) → Integrable (fun t => Q t ^ 2) →
            MemLp (logarithmicIncoming b ℓ P) p₀ (volume.restrict (Icc 0 δ)) →
            (eLpNorm (logarithmicIncoming b ℓ P) p₀ (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (U : ℝ) (hU : 0 ≤ U) (hUR : U < rH 0), U ≤ U₀ →
              ∀ (hfU : MemLp (logarithmicIncoming b ℓ P) p₀ (volume.restrict (Icc 0 U)))
                (ε : Ioi (0 : ℝ)) (hUp : 0 < U) (l : ℝ), τ ε ⟨U, hUp⟩ ≤ l →
                ∀ (x : (S : Ici l) → WaveState U (max 0 (S : ℝ) + 1))
                  (hx : ∀ S : Ici l, IsWaveIntegral hU (by positivity) B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h rH 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological (max 0 (S : ℝ) + 1) hc hi hrc hr0)
                    (incomingWaveVelocity hUR hp₀ hfU) (x S)),
                  let T := fun S : Ici l => max 0 (S : ℝ) + 1
                  let hT := fun S : Ici l => (le_max_left 0 (S : ℝ)).trans (le_add_of_nonneg_right zero_le_one)
                  let zIn := incomingWaveCurve hU hUR hp₀ hfU (horizonPhi h rH 0)
                  ∃ χ : Ici l → ℝ × ℝ → ℝ,
                    (∀ S, ContinuousOn (χ S) (Icc (0 : ℝ) (Z - Y) ×ˢ Icc l S) ∧
                      ∀ z ∈ Icc (0 : ℝ) (Z - Y) ×ˢ Icc l S, χ S z ∈ Ioo 0 U ∧
                        (x S).1 (projIcc 0 U hU (χ S z)) (projIcc 0 (T S) (hT S) z.2) 0 = Z - z.1) ∧
                    let ν := fun S => radialNuField (hT S) B.charge B.cosmological zIn (x S).1 (hx S).choose
                    let u := fun S z => projIcc 0 U hU (χ S z)
                    let v := fun S (z : ℝ × ℝ) => projIcc 0 (T S) (hT S) z.2
                    let ρ := fun S z => (x S).1 (u S z) (v S z) 0
                    let Lm := fun S z => (x S).2.1 (u S z) (v S z) 0
                    let ζ := fun S z => zIn (u S z) 0 * logarithmicIncoming b ℓ P (χ S z) +
                      scalarTransportCorrection (hT S) (ν S) (x S).2.1 (u S z) (v S z)
                    let X := fun r => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - r)
                    let W := fun r => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - r)
                    let H₀ := fun t => Ch * P (B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Z))
                    let p := fun S (z : ℝ × ℝ) => Real.exp (B.innerRate * z.2) * (ρ S z * (x S).2.1 (u S z) (v S z) 1) - X (ρ S z) * H₀ z.2
                    let q := fun S (z : ℝ × ℝ) => Real.exp (B.innerRate * z.2) * χ S z * ζ S z / B.criticalWeight (ρ S z) - W (ρ S z) * H₀ z.2
                    ∃ g Pout Qout : ℝ → ℝ,
                      ContinuousOn g (Ici l) ∧ ContinuousOn Pout (Ici l) ∧ ContinuousOn Qout (Ici l) ∧
                      (∀ S : Ici l, ∀ t ∈ Icc l (S : ℝ), g t = χ S (Z - Y, t) ∧
                        Pout t = p S (Z - Y, t) ∧ Qout t = q S (Z - Y, t)) ∧
                      MemLp Pout 2 (volume.restrict (Ici l)) ∧ MemLp Qout 2 (volume.restrict (Ici l)) ∧
                      Real.sqrt (∫ t in Ici l, Pout t ^ 2 + Qout t ^ 2) ≤
                        (Real.sqrt (e * (1 + ∫ t, P t ^ 2) + L * ∫ t, Q t ^ 2) +
                          Real.sqrt (∫ d in (0 : ℝ)..(Z - Y),
                            (-1 / Lm ⟨l, by exact le_refl l⟩ (d, l)) * q ⟨l, by exact le_refl l⟩ (d, l) ^ 2) +
                          (Z - Y) * Real.sqrt (2 * (ε : ℝ) ^ 2 * (Ch ^ 2 / B.outerRate * ∫ t, P t ^ 2) +
                            2 * C ^ 2 * (Ch ^ 2 * B.outerRate * ∫ t, Q t ^ 2))) *
                              Real.exp (((∫ r in B.inner..B.event, B.energyGrowth r) + (ε : ℝ) * (Z - Y) + 1) / 2) := by
  classical
  intro b hi hr0 cν Ch
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, hR, hband⟩ := B.exists_matched_band_energy hs hH hdH hdHR hA hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y cap e hY hYR hcap he
  obtain ⟨Z, U₀, C, L, τ, hZ, hcapZ, hU₀, hUδ, hC, hL, hsolve⟩ := hband Y cap e hY hYR hcap he
  refine ⟨Z, U₀, C, L, (fun ε U => max 0 (τ ε U)), hZ, hcapZ, hU₀, hUδ, hC, hL, ?_⟩
  intro p₀ hp₀ ℓ P Q hcrit hPi hPQ hQi hf hfn U hU hUR hUU hfU ε hUp l hl x hx T hT zIn
  have hl0 : 0 ≤ l := (le_max_left _ _).trans hl
  have hτ : τ ε ⟨U, hUp⟩ ≤ l := (le_max_right _ _).trans hl
  have hST (S : Ici l) : (S : ℝ) < T S := (le_max_right _ _).trans_lt (lt_add_one _)
  have hwindows (S : Ici l) := hsolve p₀ hp₀ ℓ P Q hcrit hPi hPQ hQi hf hfn
    U (T S) hU (hT S) hUR hUU hfU (x S) (hx S) ε hUp l S hτ S.property (hST S)
  choose χ hχc hχhit henergy using hwindows
  refine ⟨χ, (fun S => ⟨hχc S, hχhit S⟩), ?_⟩
  intro ν u v ρ Lm ζ X W H₀ p q
  let d := Z - Y
  have hd : d ∈ Icc (0 : ℝ) (Z - Y) := ⟨sub_nonneg.2 hZ.1.le, le_rfl⟩
  have htime (S : Ici l) {t : ℝ} (ht : t ∈ Icc l S) : t ∈ Icc 0 (T S) :=
    ⟨hl0.trans ht.1, ht.2.trans (hST S).le⟩
  have hρ (S : Ici l) {t : ℝ} (ht : t ∈ Icc l S) : ρ S (d, t) = Y := by
    have hh := (hχhit S (d, t) ⟨hd, ht⟩).2
    change ρ S (d, t) = Z - (Z - Y) at hh
    simpa only [sub_sub_cancel] using hh
  let F := fun S t => (χ S (d, t), (p S (d, t), q S (d, t)))
  have hfc : ContinuousOn (logarithmicIncoming b ℓ P) (Ioi 0) :=
    (logarithmicIncoming_contDiff (contDiff_one_iff_deriv.2
      ⟨fun t => (hPQ t).differentiableAt, by
        have heq : deriv P = Q := funext (fun t => (hPQ t).deriv)
        rw [heq]
        exact Q.continuous⟩) b ℓ).continuousOn
  have hH₀ : Continuous H₀ := by dsimp only [H₀]; fun_prop
  have hFc (S : Ici l) : ContinuousOn (F S) (Icc l S) := by
    have hχt : ContinuousOn (fun t => χ S (d, t)) (Icc l S) :=
      (hχc S).comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hd, ht⟩)
    have hut : ContinuousOn (fun t => u S (d, t)) (Icc l S) :=
      (continuous_projIcc (h := hU)).comp_continuousOn hχt
    have hvt : ContinuousOn (fun t => v S (d, t)) (Icc l S) := continuous_projIcc.continuousOn
    have hθt : ContinuousOn (fun t => (x S).2.1 (u S (d, t)) (v S (d, t)) 1) (Icc l S) :=
      (continuous_apply 1).comp_continuousOn ((x S).2.1.uncurry.continuous.comp_continuousOn (hut.prodMk hvt))
    have hzt : ContinuousOn (fun t => ζ S (d, t)) (Icc l S) := by
      have hz := (continuous_apply 0).comp_continuousOn (zIn.continuous.comp_continuousOn hut)
      have hfχ := hfc.comp hχt (fun t ht => (hχhit S (d, t) ⟨hd, ht⟩).1.1)
      exact (hz.mul hfχ).add ((scalarTransportCorrection (hT S) (ν S) (x S).2.1).uncurry.continuous.comp_continuousOn (hut.prodMk hvt))
    have hexp : ContinuousOn (fun t : ℝ => Real.exp (B.innerRate * t)) (Icc l S) := by fun_prop
    have hpt : ContinuousOn (fun t => p S (d, t)) (Icc l S) := by
      apply ((hexp.mul ((continuousOn_const (c := Y)).mul hθt)).sub
        ((continuousOn_const (c := X Y)).mul hH₀.continuousOn)).congr
      intro t ht
      dsimp only [p]
      rw [hρ S ht]
      rfl
    have hqt : ContinuousOn (fun t => q S (d, t)) (Icc l S) := by
      apply ((((hexp.mul hχt).mul hzt).div_const (B.criticalWeight Y)).sub
        ((continuousOn_const (c := W Y)).mul hH₀.continuousOn)).congr
      intro t ht
      dsimp only [q]
      rw [hρ S ht]
      rfl
    exact hχt.prodMk (hpt.prodMk hqt)
  have hcompat (S J : Ici l) (t : ℝ) (htS : t ∈ Icc l S) (htJ : t ∈ Icc l J) : F S t = F J t := by
    have hsχ := (hχhit S (d, t) ⟨hd, htS⟩).1
    have hjχ := (hχhit J (d, t) ⟨hd, htJ⟩).1
    have hsT := htime S htS
    have hjT := htime J htJ
    have hvs : v S (d, t) = ⟨t, hsT⟩ := projIcc_of_mem (hT S) hsT
    have hvj : v J (d, t) = ⟨t, hjT⟩ := projIcc_of_mem (hT J) hjT
    have heq : (x S).1 (u S (d, t)) ⟨t, hsT⟩ 0 = (x J).1 (u J (d, t)) ⟨t, hjT⟩ 0 := by
      simpa only [ρ, hvs, hvj] using
        (hρ S htS).trans (hρ J htJ).symm
    have ho := (hx S).horizon_radius_scalar_overlap hU (hT S) hUR hU (hT J) hUR hc hi hrc hr0 hφ hrd
      hp₀ hfU hfU (hx J) (u S (d, t)) (u J (d, t)) hsT hjT heq
    have hh : χ S (d, t) = χ J (d, t) ∧
        (x S).1 (u S (d, t)) (v S (d, t)) = (x J).1 (u J (d, t)) (v J (d, t)) ∧
        (x S).2.1 (u S (d, t)) (v S (d, t)) = (x J).2.1 (u J (d, t)) (v J (d, t)) ∧
        ζ S (d, t) = ζ J (d, t) := by
      simpa only [ζ, ν, zIn, u, hvs, hvj, projIcc_of_mem hU ⟨hsχ.1.le, hsχ.2.le⟩,
        projIcc_of_mem hU ⟨hjχ.1.le, hjχ.2.le⟩] using ho
    dsimp only [F, p, q, ρ]
    rw [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2]
  obtain ⟨Fout, hFout, hFoutEq⟩ := exists_continuous_compatible_halfline F hFc hcompat
  let g := fun t => (Fout t).1
  let Pout := fun t => (Fout t).2.1
  let Qout := fun t => (Fout t).2.2
  have hg : ContinuousOn g (Ici l) := hFout.fst
  have hp : ContinuousOn Pout (Ici l) := hFout.snd.fst
  have hq : ContinuousOn Qout (Ici l) := hFout.snd.snd
  have htrace (S : Ici l) {t : ℝ} (ht : t ∈ Icc l S) :
      g t = χ S (d, t) ∧ Pout t = p S (d, t) ∧ Qout t = q S (d, t) := by
    have hh := hFoutEq S ht
    exact ⟨congrArg Prod.fst hh, congrArg (fun z => z.2.1) hh, congrArg (fun z => z.2.2) hh⟩
  have hbottom (S : Ici l) :
      (∫ w in (0 : ℝ)..d, (-1 / Lm S (w, l)) * q S (w, l) ^ 2) =
        ∫ w in (0 : ℝ)..d, (-1 / Lm ⟨l, by exact le_refl l⟩ (w, l)) * q ⟨l, by exact le_refl l⟩ (w, l) ^ 2 := by
    let J : Ici l := ⟨l, by exact le_refl l⟩
    have hh := (hx S).horizon_band_energy_overlap hU (hT S) hUR hU (hT J) hUR
      hc hi hrc hr0 hφ hrd hp₀ hfU hfU (hx J) B.innerRate X W B.criticalWeight H₀
      hd.1 (le_refl l) (χ S) (χ J)
    apply hh (fun z hz => ?_) |>.2.2.2.2
    have htl : z.2 = l := le_antisymm hz.2.2 hz.2.1
    have hzS : z ∈ Icc (0 : ℝ) d ×ˢ Icc l S := ⟨hz.1, hz.2.1, htl.trans_le S.property⟩
    have hsχ := hχhit S z hzS
    have hjχ := hχhit J z hz
    exact ⟨⟨hsχ.1.1.le, hsχ.1.2.le⟩, ⟨hjχ.1.1.le, hjχ.1.2.le⟩,
      htime S hzS.2, htime J hz.2, hsχ.2.trans hjχ.2.symm⟩
  refine ⟨g, Pout, Qout, hg, hp, hq, (fun S t ht => htrace S ht), ?_⟩
  apply pair_energy_halfline hp hq
  intro S hS
  have he := henergy ⟨S, hS⟩
  change Real.sqrt (∫ t in l..S, p ⟨S, hS⟩ (d, t) ^ 2 + q ⟨S, hS⟩ (d, t) ^ 2) ≤ _ at he
  rw [hbottom ⟨S, hS⟩] at he
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htt : t ∈ Icc l S := by simpa only [uIcc_of_le hS] using ht
  change Pout t ^ 2 + Qout t ^ 2 = p ⟨S, hS⟩ (d, t) ^ 2 + q ⟨S, hS⟩ (d, t) ^ 2
  rw [(htrace ⟨S, hS⟩ htt).2.1, (htrace ⟨S, hS⟩ htt).2.2]

end CauchyHorizon.Background
