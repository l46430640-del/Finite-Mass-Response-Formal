import CauchyHorizon.Characteristic.OuterFluxNormalization
import CauchyHorizon.Characteristic.PhysicalOverlap
import CauchyHorizon.Analysis.KernelPrimitive

/-! The outer coefficient and the horizon contribution on actual moving prefixes. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Background

theorem exists_moving_outer_flux (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ cap ε : ℝ, 0 < cap → 0 < ε →
      ∃ δ T : ℝ, 0 < δ ∧ δ < cap ∧ δ ≤ 1 ∧ 0 ≤ T ∧
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
          (x : WaveState U V)
          (_hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x),
          (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
          let Q := fun (u : Icc 0 U) (v : Icc 0 V) =>
            r v * horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological *
              ∫ t in (0 : ℝ)..u, (r 0 - t) / (x.1 (projIcc 0 U hU t) v 0) ^ 2 * f t
          (∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) → (u : ℝ) * Real.exp (B.outerRate * v) ≤ δ →
            B.event / 2 ≤ x.1 u v 0 ∧
            |x.2.1 u v 0 / x.1 u v 0 -
              r v * horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological / (x.1 u v 0) ^ 2 +
              (B.outerRate / B.event) * u * (cν * Real.exp (B.outerRate * v))| ≤
                ε * u * (cν * Real.exp (B.outerRate * v))) ∧
          ∀ k : ℝ, k ≤ B.outerRate * (1 - 1 / p.toReal) →
            (∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) → (u : ℝ) * Real.exp (B.outerRate * v) ≤ δ →
              Real.exp (k * v) * |Q u v| ≤ C * Real.exp (-(2 * s) * v)) ∧
            ∀ (l S : ℝ) (g : ℝ → ℝ), T ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
              (∀ t ∈ Icc l S, g t ∈ Icc 0 U ∧ g t * Real.exp (B.outerRate * t) ≤ δ) →
              IntegrableOn (fun t => (Real.exp (k * t) * Q (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2)
                (Icc l S) ∧
              (∫ t in l..S, (Real.exp (k * t) * Q (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2) ≤
                C ^ 2 / (4 * s) * Real.exp (-(4 * s) * l) := by
  intro hi hr0 cν
  let ρ := B.event / 2
  have hρ : 0 < ρ := half_pos B.event_pos
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  have hR : 0 ≤ B.event + dH := add_nonneg B.event_pos.le hdH
  obtain ⟨W, hW, hWb⟩ := B.horizon_radius_lambda_bounds hs hH hdH hdHR hb hrdec
  let C := (B.event + dH) * W * (r 0 / ρ ^ 2) * A
  have hC : 0 ≤ C := by dsimp only [C]; positivity [B.event_pos]
  refine ⟨C, hC, ?_⟩
  intro cap ε hcap hε
  obtain ⟨δ, T, hδ, hδcap, hT, hthin⟩ := B.exists_outer_flux_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut (min cap 1) ε (lt_min hcap zero_lt_one) hε
  have hδ1 : δ ≤ 1 := hδcap.le.trans (min_le_right _ _)
  refine ⟨δ, T, hδ, hδcap.trans_le (min_le_left _ _), hδ1, hT, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn Q
  have hgeo (u : Icc 0 U) (v : Icc 0 V) (hv : T ≤ (v : ℝ))
      (hu : (u : ℝ) * Real.exp (B.outerRate * v) ≤ δ) :
      ρ ≤ x.1 u v 0 ∧
      |x.2.1 u v 0 / x.1 u v 0 -
        r v * horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological / (x.1 u v 0) ^ 2 +
        (B.outerRate / B.event) * u * (cν * Real.exp (B.outerRate * v))| ≤
          ε * u * (cν * Real.exp (B.outerRate * v)) := by
    let hfS := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
    have huR : (u : ℝ) < r 0 := u.property.2.trans_lt hUR
    let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (v : ℝ))
      le_rfl (by linarith only [u.property.2]) le_rfl (by linarith only [v.property.2]) x
    have hy : IsWaveIntegral u.property.1 v.property.1 B.charge B.cosmological
        (incomingWaveCurve u.property.1 huR hp hfS (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological (v : ℝ) hc hi hrc hr0)
        (incomingWaveVelocity huR hp hfS) y :=
      hx.horizon_prefix hU hV hUR u.property.1 v.property.1 u.property.2 v.property.2 hc hi hrc hr0 hp hf
    have hg := hthin u v u.property.1 v.property.1 huR p hp f hfS y hy
      ((scalar_prefix_norm_le u.property.2 hf).trans hfn) hu
      ⟨u, u.property.1, le_rfl⟩ ⟨v, v.property.1, le_rfl⟩ hv
    have he := hy.horizon_overlap u.property.1 v.property.1 huR hU hV hUR hc hi hrc hr0 hp hfS hf hx
      (show (u : ℝ) ∈ Icc 0 (u : ℝ) from ⟨u.property.1, le_rfl⟩) u.property
      (show (v : ℝ) ∈ Icc 0 (v : ℝ) from ⟨v.property.1, le_rfl⟩) v.property
    have hg0 := (hg.1 ⟨u, u.property.1, le_rfl⟩).1
    have hg1 := hg.2
    rw [he.1] at hg0
    rw [he.1, he.2] at hg1
    exact ⟨hg0, hg1⟩
  refine ⟨hgeo, ?_⟩
  intro k hkp
  have hpoint (u : Icc 0 U) (v : Icc 0 V) (hv : T ≤ (v : ℝ))
      (hu : (u : ℝ) * Real.exp (B.outerRate * v) ≤ δ) :
      Real.exp (k * v) * |Q u v| ≤ C * Real.exp (-(2 * s) * v) := by
    have hp1 : (1 : ℝ≥0∞) ≤ p := (by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp
    have hfi0 : IntegrableOn (fun t => |f t|) (Icc 0 U) := (hf.integrable hp1).norm
    have hfi : IntervalIntegrable (fun t => |f t|) volume 0 u :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le u.property.1).2
        (hfi0.mono_set (Icc_subset_Icc le_rfl u.property.2))
    have hcoeff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) u) :
        |(r 0 - t) / (x.1 (projIcc 0 U hU t) v 0) ^ 2| ≤ r 0 / ρ ^ 2 := by
      have htU : t ∈ Icc 0 U := ⟨ht.1, ht.2.trans u.property.2⟩
      have hg := (hgeo ⟨t, htU⟩ v hv
        ((mul_le_mul_of_nonneg_right ht.2 (Real.exp_pos _).le).trans hu)).1
      rw [projIcc_of_mem hU htU, abs_div, abs_of_pos (sub_pos.2 (htU.2.trans_lt hUR)),
        abs_of_nonneg (sq_nonneg _)]
      exact (div_le_div_of_nonneg_right (sub_le_self _ ht.1) (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left hrp.le (sq_pos_of_pos hρ) ((sq_le_sq₀ hρ.le (hρ.le.trans hg)).2 hg))
    have hI := intervalIntegral.norm_integral_le_of_norm_le u.property.1
      (f := fun t => (r 0 - t) / (x.1 (projIcc 0 U hU t) v 0) ^ 2 * f t)
      (g := fun t => (r 0 / ρ ^ 2) * |f t|)
      (Filter.Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hcoeff t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)))
      (hfi.const_mul _)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hI
    have hweighted := incoming_weighted_integral_le_lp u.property.1 v.property.1 hp1
      (hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)) hkp hu
    have hpw : δ ^ (1 - 1 / p.toReal) ≤ 1 :=
      Real.rpow_le_one hδ.le hδ1 (by linarith only [(incoming_exponent_bounds hp).1])
    have hw : Real.exp (k * v) * (∫ t in (0 : ℝ)..u, |f t|) ≤ A :=
      hweighted.trans ((mul_le_mul_of_nonneg_left hpw (eLpNorm f p (volume.restrict (Icc 0 u))).toReal_nonneg).trans
        (by simpa only [mul_one] using (scalar_prefix_norm_le u.property.2 hf).trans hfn))
    have hrad : |r v| ≤ B.event + dH := by
      rw [abs_of_pos ((sub_pos.2 hdHR).trans_le (hrb v))]
      exact (hWb v v.property.1).1.2
    have hlam := (hWb v v.property.1).2
    have hHbound := mul_le_mul hrad hlam (abs_nonneg _) (by positivity : 0 ≤ B.event + dH)
    have hIb := mul_le_mul_of_nonneg_left hI (Real.exp_pos (k * v)).le
    have hIb' : Real.exp (k * v) *
        |∫ t in (0 : ℝ)..u, (r 0 - t) / (x.1 (projIcc 0 U hU t) v 0) ^ 2 * f t| ≤ (r 0 / ρ ^ 2) * A := by
      calc
        _ ≤ (r 0 / ρ ^ 2) * (Real.exp (k * v) * (∫ t in (0 : ℝ)..u, |f t|)) := by
          simpa only [mul_left_comm] using hIb
        _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
    dsimp only [Q]
    rw [abs_mul, abs_mul]
    calc
      _ = (|r v| * |horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological|) *
          (Real.exp (k * v) * |∫ t in (0 : ℝ)..u,
            (r 0 - t) / (x.1 (projIcc 0 U hU t) v 0) ^ 2 * f t|) := by ring
      _ ≤ ((B.event + dH) * (W * Real.exp (-(2 * s) * v))) * ((r 0 / ρ ^ 2) * A) :=
        mul_le_mul hHbound hIb' (by positivity) (by positivity)
      _ = _ := by dsimp only [C]; ring
  refine ⟨hpoint, ?_⟩
  intro l S g hl hlS hSV hgc hg
  let K : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
    (⟨fun q : Icc 0 U × Icc 0 V => (r 0 - (q.1 : ℝ)) / (x.1.uncurry q 0) ^ 2, by
      fun_prop (disch := intro q; exact pow_ne_zero 2 (hx.choose q.1 q.2))⟩ :
      C(Icc 0 U × Icc 0 V, ℝ)).curry
  have hJc : Continuous (fun q : Icc 0 U × Icc 0 V =>
      ∫ t in (0 : ℝ)..q.1, (r 0 - t) / (x.1 (projIcc 0 U hU t) q.2 0) ^ 2 * f t) := by
    apply (continuous_kernel_primitive hU K (hf.mono_exponent ((by norm_num : (2 : ℝ≥0∞) ≤ 4).trans hp))).congr
    intro q
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le q.1.property.1] at ht
    change (r 0 - (projIcc 0 U hU t : ℝ)) / (x.1 (projIcc 0 U hU t) q.2 0) ^ 2 * f t =
      (r 0 - t) / (x.1 (projIcc 0 U hU t) q.2 0) ^ 2 * f t
    rw [projIcc_of_mem hU (show t ∈ Icc 0 U from ⟨ht.1, ht.2.trans q.1.property.2⟩)]
  have hLc : Continuous (fun v : Icc 0 V =>
      horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological) :=
    (continuous_apply (0 : Fin 3)).comp (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0).continuous
  have hQc : Continuous (fun q : Icc 0 U × Icc 0 V => Q q.1 q.2) := by
    exact ((hrc.comp (continuous_subtype_val.comp continuous_snd)).mul (hLc.comp continuous_snd)).mul hJc
  let E := fun t => Real.exp (k * t) * Q (projIcc 0 U hU (g t)) (projIcc 0 V hV t)
  have hEc : ContinuousOn E (Icc l S) := by
    have harg : ContinuousOn (fun t => (projIcc 0 U hU (g t), projIcc 0 V hV t)) (Icc l S) :=
      ((continuous_projIcc (a := (0 : ℝ)) (b := U) (h := hU)).comp_continuousOn hgc).prodMk
        (continuous_projIcc (a := (0 : ℝ)) (b := V) (h := hV)).continuousOn
    exact (by fun_prop : ContinuousOn (fun t => Real.exp (k * t)) (Icc l S)).mul
      (hQc.comp_continuousOn harg)
  have hEi : IntegrableOn (fun t => E t ^ 2) (Icc l S) := (hEc.pow 2).integrableOn_Icc
  have he (t : ℝ) : (C * Real.exp (-(2 * s) * t)) ^ 2 = C ^ 2 * Real.exp (-(4 * s) * t) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hmajor (t : ℝ) (ht : t ∈ Icc l S) : E t ^ 2 ≤ C ^ 2 * Real.exp (-(4 * s) * t) := by
    have htV : t ∈ Icc 0 V := ⟨hT.trans (hl.trans ht.1), ht.2.trans hSV⟩
    have hh := hpoint ⟨g t, (hg t ht).1⟩ ⟨t, htV⟩ (hl.trans ht.1) (hg t ht).2
    have hab : |E t| ≤ C * Real.exp (-(2 * s) * t) := by
      simpa only [E, abs_mul, abs_of_pos (Real.exp_pos _), projIcc_of_mem hU (hg t ht).1,
        projIcc_of_mem hV htV] using hh
    rw [← he t]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (E t)) (by positivity)).2 hab
  have hright : Continuous (fun t : ℝ => C ^ 2 * Real.exp (-(4 * s) * t)) := by fun_prop
  have hle := intervalIntegral.integral_mono_on (μ := volume) hlS ((hEc.pow 2).intervalIntegrable_of_Icc hlS)
    (hright.intervalIntegrable l S) hmajor
  have htail := setIntegral_mono_set
    ((integrableOn_exp_mul_Ioi (by linarith only [hs] : -(4 * s) < 0) l).const_mul (C ^ 2))
    (Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg C) (Real.exp_pos _).le))
    (Filter.Eventually.of_forall (fun t (ht : t ∈ Ioc l S) => ht.1))
  simp only [intervalIntegral.integral_of_le hlS] at hle
  have hfinal := hle.trans htail
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith only [hs] : -(4 * s) < 0),
    neg_div_neg_eq] at hfinal
  refine ⟨hEi, ?_⟩
  rw [intervalIntegral.integral_of_le hlS]
  exact hfinal.trans_eq (by ring)

end CauchyHorizon.Background
