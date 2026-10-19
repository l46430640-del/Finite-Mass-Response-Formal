import CauchyHorizon.Characteristic.MatchedHalfline
import CauchyHorizon.Characteristic.BottomLimit
import CauchyHorizon.Analysis.EscapingProfile

/-! Arbitrarily small late half-line errors for the actual matched scalar sequence. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 5000000 in
theorem exists_late_matched_small (B : Background) {s H dH A E : ℝ}
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
        ∃ Z U₀ : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
          Z ∈ Ioo Y B.event ∧ B.event - cap < Z ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ (∀ U, 0 < τ U) ∧
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
            ∀ (U : ℝ) (hUp : 0 < U) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : ∀ n, MemLp (logarithmicIncoming b (ℓ n) (P n)) p (volume.restrict (Icc 0 U)))
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
                      (∀ n t, l ≤ t →
                        let T : Ici (0 : ℝ) := ⟨max 0 t + 1, by change 0 ≤ max 0 t + 1; positivity⟩
                        let u := projIcc 0 U hUp.le (g n t)
                        let v := projIcc 0 (T : ℝ) T.property t
                        let ν := radialNuField T.property B.charge B.cosmological
                          (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose
                        let H₀ := Ch * P n (B.outerRate * t + ℓ n + Real.log cν - Real.log (B.z Z))
                        g n t ∈ Ioo 0 U ∧ (X n T).1 u v 0 = Y ∧
                          Eθ n t = Real.exp (B.innerRate * t) * (Y * (X n T).2.1 u v 1) - Xm Y * H₀ ∧
                          Eζ n t = Real.exp (B.innerRate * t) * g n t *
                            ((r 0 - g n t) * logarithmicIncoming b (ℓ n) (P n) (g n t) +
                              scalarTransportCorrection T.property ν (X n T).2.1 u v) /
                                B.criticalWeight Y - Wm Y * H₀) ∧
                      ∀ᶠ n in atTop, Real.sqrt (∫ t in Ici l, Eθ n t ^ 2 + Eζ n t ^ 2) < η := by
  classical
  intro b hi hr0 cν Ch Xm Wm
  obtain ⟨δm, Rm, hδm, hRm, hmatched⟩ := B.exists_matched_halfline_energy
    hs hH hdH hdHR hA hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δb, Rb, _hδb, hRb, hbottom⟩ := B.exists_bottom_flux_small
    hs hH hdH hdHR hA hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨max δm δb, min Rm Rb, hδm.trans_le (le_max_left _ _),
    ⟨lt_min hRm.1 hRb.1, (min_le_left _ _).trans_lt hRm.2⟩, ?_⟩
  intro Y cap η hY hYR hcap hη
  let D := B.event - B.inner
  let G := ∫ z in B.inner..B.event, B.energyGrowth z
  let K := Ch ^ 2 / B.outerRate * E
  have hD : 0 < D := B.radialLength_pos
  have hK : 0 ≤ K := mul_nonneg (div_nonneg (sq_nonneg _) B.outerRate_pos.le) hE
  let J := fun e : ℝ => (Real.sqrt (e * (1 + E)) + Real.sqrt e + D * Real.sqrt (2 * e ^ 2 * K)) *
    Real.exp ((G + e * D + 1) / 2)
  have hJc : Continuous J := by dsimp only [J]; fun_prop
  have hJ0 : J 0 = 0 := by simp [J]
  have hJlt : J 0 < η := by rw [hJ0]; exact hη
  obtain ⟨d, hd, hdsmall⟩ := Metric.mem_nhds_iff.1
    ((hJc.continuousAt (x := 0)).tendsto.eventually_lt_const hJlt)
  let e := d / 2
  have he : 0 < e := half_pos hd
  have hJe : J e < η := hdsmall (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos he]
    exact half_lt_self hd)
  let ε : Ioi (0 : ℝ) := ⟨e, he⟩
  obtain ⟨Z, Um, C, L, τm, hZ, hcapZ, hUm, hUmδ, _hC, _hL, hmatch⟩ :=
    hmatched Y cap e hY (hYR.trans (min_le_left _ _)) hcap he
  obtain ⟨Ub, τb, hUb, _hUbδ, hτb, hsmall⟩ :=
    hbottom Y Z hY hZ.1 (hYR.trans (min_le_right _ _)) hZ.2
  let τ := fun U => max (τm ε U) (τb ε U)
  refine ⟨Z, min Um Ub, τ, hZ, hcapZ, lt_min hUm hUb,
    ((min_le_left _ _).trans hUmδ).trans (le_max_left _ _),
    (fun U => (hτb ε U).trans_le (le_max_right _ _)), ?_⟩
  intro p hp ℓ m P Q hcrit hPi hPE hPQ hQi hQlim hfront hsupport hf hfn hflim U hUp hUR hUU hfU X X₀ hX hX₀ ρ hρ hfloor hfloor₀ l hl
  have hlm : τm ε ⟨U, hUp⟩ ≤ l := (le_max_left _ _).trans hl
  have hlb : τb ε ⟨U, hUp⟩ ≤ l := (le_max_right _ _).trans hl
  have hl0 : 0 < l := (hτb ε ⟨U, hUp⟩).trans_le hlb
  let hfM := fun n => (hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_left δm δb)) le_rfl)
  let hfB := fun n => (hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_right δm δb)) le_rfl)
  have hnormM (n : ℕ) := scalar_prefix_norm_le (le_max_left δm δb) (hf n)
  have hnormB (n : ℕ) := scalar_prefix_norm_le (le_max_right δm δb) (hf n)
  have hlimB : Tendsto (fun n => (eLpNorm (logarithmicIncoming b (ℓ n) (P n)) p
      (volume.restrict (Icc 0 δb))).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) hnormB hflim
  let T := fun S : Ici l => (⟨max 0 (S : ℝ) + 1, by change 0 ≤ max 0 (S : ℝ) + 1; positivity⟩ : Ici (0 : ℝ))
  let x := fun n S => X n (T S)
  let hx := fun n S => hX n (T S)
  have hmatches (n : ℕ) := hmatch p hp (ℓ n) (P n) (Q n) hcrit (hPi n) (hPQ n) (hQi n)
    (hfM n) ((hnormM n).trans (hfn n)) U hUp.le hUR (hUU.trans (min_le_left _ _))
    (hfU n) ε hUp l hlm (x n) (hx n)
  choose χ hχ g Eθ Eζ hgc hθc hζc htrace hθlp hζlp henergy using hmatches
  let S₀ : Ici l := ⟨l, by change l ≤ l; exact le_rfl⟩
  let v₀ : Icc 0 (T S₀ : ℝ) := ⟨l, hl0.le, (le_max_right 0 l).trans (le_add_of_nonneg_right zero_le_one)⟩
  have hvproj : projIcc 0 (T S₀ : ℝ) (T S₀).property l = v₀ :=
    projIcc_of_mem (T S₀).property v₀.property
  let Wband : C(Icc (0 : ℝ) (Z - Y), ℝ) :=
    ⟨fun w => Wm (Z - w), (continuous_extendCurve B.radialLength_pos.le _).comp
      (continuous_const.sub (continuous_const.sub continuous_subtype_val))⟩
  have hbottomHit (n : ℕ) (w : Icc (0 : ℝ) (Z - Y)) :=
    (hχ n S₀).2 (w, l) ⟨w.property, le_rfl, le_rfl⟩
  let χb := fun n => (⟨fun w : Icc (0 : ℝ) (Z - Y) => projIcc 0 U hUp.le (χ n S₀ (w, l)),
    continuous_projIcc.comp ((hχ n S₀).1.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun w => ⟨w.property, le_rfl, le_rfl⟩))⟩ :
      C(Icc (0 : ℝ) (Z - Y), Icc (0 : ℝ) U))
  have hχbv (n : ℕ) (w : Icc (0 : ℝ) (Z - Y)) : (χb n w : ℝ) = χ n S₀ (w, l) :=
    congrArg Subtype.val (projIcc_of_mem hUp.le ⟨(hbottomHit n w).1.1.le, (hbottomHit n w).1.2.le⟩)
  have hχbr (n : ℕ) (w : Icc (0 : ℝ) (Z - Y)) : (x n S₀).1 (χb n w) v₀ 0 = Z - w := by
    have hh := (hbottomHit n w).2
    change (x n S₀).1 (χb n w) (projIcc 0 (T S₀ : ℝ) (T S₀).property l) 0 = Z - w at hh
    rwa [hvproj] at hh
  let a := fun n => Ch * P n (B.outerRate * l + ℓ n + Real.log cν - Real.log (B.z Z))
  obtain ⟨hszero, hPzero⟩ := logarithmicIncoming_eventually_zero b hfront hsupport
  have ha : Tendsto a atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hPzero (B.outerRate * l + Real.log cν - Real.log (B.z Z))] with n hn
    have hh := hn _ le_rfl
    rw [show ℓ n + (B.outerRate * l + Real.log cν - Real.log (B.z Z)) =
      B.outerRate * l + ℓ n + Real.log cν - Real.log (B.z Z) by ring] at hh
    simp only [a, hh, mul_zero]
  have hbot := hsmall p hp (fun n => logarithmicIncoming b (ℓ n) (P n)) hfB
    (fun n => (hnormB n).trans (hfn n)) hlimB
    (fun z hz => (hszero z hz).mono (fun _ hn u hu => hn u hu.1))
    U (T S₀) hUp.le (T S₀).property hUR (hUU.trans (min_le_right _ _)) hfU
    (fun n => x n S₀) (X₀ (T S₀)) (fun n => hx n S₀) (hX₀ (T S₀))
    ρ hρ (fun n => hfloor n (T S₀)) (hfloor₀ (T S₀)) ε hUp v₀
    ((le_max_right 0 l).trans_lt (lt_add_one _)) hlb χb hχbr Wband a ha
  let ν := fun n S => radialNuField (T S).property B.charge B.cosmological
    (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0)) (x n S).1 (hx n S).choose
  let bottom := fun n => ∫ w in (0 : ℝ)..(Z - Y),
    let u := projIcc 0 U hUp.le (χ n S₀ (w, l))
    let z := (x n S₀).1 u v₀ 0
    (-1 / (x n S₀).2.1 u v₀ 0) *
      (Real.exp (B.innerRate * l) * χ n S₀ (w, l) *
        (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0) u 0 *
            logarithmicIncoming b (ℓ n) (P n) (χ n S₀ (w, l)) +
          scalarTransportCorrection (T S₀).property (ν n S₀) (x n S₀).2.1 u v₀) /
            B.criticalWeight z - Wm z * a n) ^ 2
  have hbotSmall : ∀ᶠ n in atTop, |bottom n| < e := by
    apply hbot.mono
    intro n hn
    convert hn using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le (sub_nonneg.2 hZ.1.le)] at hw
    have hh := hbottomHit n ⟨w, hw⟩
    have hrad := hχbr n ⟨w, hw⟩
    have hval := hχbv n ⟨w, hw⟩
    simp only [projIcc_of_mem (sub_nonneg.2 hZ.1.le) hw]
    change _ = (-1 / (x n S₀).2.1 (χb n ⟨w, hw⟩) v₀ 0) *
      (Real.exp (B.innerRate * l) * (χb n ⟨w, hw⟩ : ℝ) *
        ((r 0 - (χb n ⟨w, hw⟩ : ℝ)) * logarithmicIncoming b (ℓ n) (P n) (χb n ⟨w, hw⟩) +
          scalarTransportCorrection (T S₀).property (ν n S₀) (x n S₀).2.1 (χb n ⟨w, hw⟩) v₀) /
            B.criticalWeight (Z - w) - Wm (Z - w) * a n) ^ 2
    rw [hval]
    dsimp only [χb, ContinuousMap.coe_mk] at hrad ⊢
    rw [hrad, incomingWaveCurve_apply]
    simp only [Matrix.cons_val_zero, incomingRadius,
      projIcc_of_mem hUp.le ⟨hh.1.1.le, hh.1.2.le⟩]
  let dQ := fun n => ∫ t, Q n t ^ 2
  let bound := fun d : ℝ =>
    (Real.sqrt (e * (1 + E) + L * d) + Real.sqrt e +
      D * Real.sqrt (2 * e ^ 2 * K + 2 * C ^ 2 * (Ch ^ 2 * B.outerRate * d))) *
        Real.exp ((G + e * D + 1) / 2)
  have hboundc : Continuous bound := by dsimp only [bound]; fun_prop
  have hb0 : bound 0 = J e := by simp only [bound, J, mul_zero, add_zero]
  have hboundlim : Tendsto (fun n => bound (dQ n)) atTop (𝓝 (J e)) := by
    simpa only [hb0, Function.comp_def] using hboundc.continuousAt.tendsto.comp hQlim
  have hwidth : Z - Y ≤ D := by dsimp only [D]; linarith only [hY, hZ.2]
  have henergyBound (n : ℕ) (hn : |bottom n| < e) :
      Real.sqrt (∫ t in Ici l, Eθ n t ^ 2 + Eζ n t ^ 2) ≤ bound (dQ n) := by
    have hh := henergy n
    dsimp only at hh
    rw [hvproj] at hh
    change Real.sqrt (∫ t in Ici l, Eθ n t ^ 2 + Eζ n t ^ 2) ≤
      (Real.sqrt (e * (1 + ∫ t, P n t ^ 2) + L * dQ n) + Real.sqrt (bottom n) +
        (Z - Y) * Real.sqrt (2 * e ^ 2 * (Ch ^ 2 / B.outerRate * ∫ t, P n t ^ 2) +
          2 * C ^ 2 * (Ch ^ 2 * B.outerRate * dQ n))) *
            Real.exp ((G + e * (Z - Y) + 1) / 2) at hh
    apply hh.trans
    have hhead : Real.sqrt (e * (1 + ∫ t, P n t ^ 2) + L * dQ n) ≤
        Real.sqrt (e * (1 + E) + L * dQ n) :=
      Real.sqrt_le_sqrt (add_le_add (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (hPE n)) he.le) le_rfl)
    have hbot' := Real.sqrt_le_sqrt ((le_abs_self (bottom n)).trans hn.le)
    have hsource :
        Real.sqrt (2 * e ^ 2 * (Ch ^ 2 / B.outerRate * ∫ t, P n t ^ 2) +
          2 * C ^ 2 * (Ch ^ 2 * B.outerRate * dQ n)) ≤
        Real.sqrt (2 * e ^ 2 * K + 2 * C ^ 2 * (Ch ^ 2 * B.outerRate * dQ n)) :=
      Real.sqrt_le_sqrt (add_le_add
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hPE n)
          (div_nonneg (sq_nonneg Ch) B.outerRate_pos.le)) (by positivity : 0 ≤ 2 * e ^ 2)) le_rfl)
    have hsource' := mul_le_mul hwidth hsource (Real.sqrt_nonneg _) hD.le
    have hsum := add_le_add (add_le_add hhead hbot') hsource'
    have hexp : Real.exp ((G + e * (Z - Y) + 1) / 2) ≤ Real.exp ((G + e * D + 1) / 2) :=
      Real.exp_le_exp.2 (div_le_div_of_nonneg_right
        (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hwidth he.le)) le_rfl)
        (by norm_num))
    exact mul_le_mul hsum hexp (Real.exp_pos _).le (by positivity)
  refine ⟨g, Eθ, Eζ, fun n => ⟨hgc n, hθc n, hζc n, hθlp n, hζlp n⟩, ?_, ?_⟩
  · intro n t ht Tt u v νt H₀
    have hg := htrace n ⟨t, ht⟩ t ⟨ht, le_rfl⟩
    have hh := (hχ n ⟨t, ht⟩).2 (Z - Y, t) ⟨⟨sub_nonneg.2 hZ.1.le, le_rfl⟩, ht, le_rfl⟩
    have hrad : (X n Tt).1 u v 0 = Y := by
      simpa only [u, v, Tt, hg.1, sub_sub_cancel] using hh.2
    refine ⟨by simpa only [hg.1] using hh.1, hrad, ?_, ?_⟩
    · have hh' := hg.2.1
      dsimp only at hh'
      rw [← hg.1] at hh'
      change Eθ n t = Real.exp (B.innerRate * t) * ((X n Tt).1 u v 0 * (X n Tt).2.1 u v 1) -
        Xm ((X n Tt).1 u v 0) * H₀ at hh'
      simpa only [hrad] using hh'
    · have hh' := hg.2.2
      dsimp only at hh'
      rw [← hg.1] at hh'
      change Eζ n t = Real.exp (B.innerRate * t) * g n t *
        (incomingWaveCurve hUp.le hUR hp (hfU n) (horizonPhi h r 0) u 0 *
          logarithmicIncoming b (ℓ n) (P n) (g n t) +
          scalarTransportCorrection Tt.property νt (X n Tt).2.1 u v) /
            B.criticalWeight ((X n Tt).1 u v 0) - Wm ((X n Tt).1 u v 0) * H₀ at hh'
      rw [hrad, incomingWaveCurve_apply] at hh'
      simpa only [Matrix.cons_val_zero, incomingRadius, u,
        projIcc_of_mem hUp.le ⟨(by simpa only [← hg.1] using hh.1.1.le),
        (by simpa only [← hg.1] using hh.1.2.le)⟩] using hh'
  · filter_upwards [hbotSmall, hboundlim.eventually_lt_const hJe] with n hn hn'
    exact (henergyBound n hn).trans_lt hn'

end CauchyHorizon.Background
