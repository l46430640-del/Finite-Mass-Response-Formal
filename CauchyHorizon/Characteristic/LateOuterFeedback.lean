import CauchyHorizon.Characteristic.OuterFeedback
import CauchyHorizon.Characteristic.HorizonBounds

/-! Late outer feedback gains a second power of the width without discarding its causal history. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

theorem exists_late_outer_feedback (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ₀ L C D : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < L ∧ 0 < C ∧ 0 < D ∧
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ → ∃ T : ℝ, 0 ≤ T ∧
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
          (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x),
          (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let F := scalarRadiationFeedback hU hV x.1 x.2.1 ν hx.choose
          (∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
            (u : ℝ) ≤ δ * Real.exp (-B.outerRate * v) → |x.2.1 u v 0| ≤ L * δ) ∧
          ∀ k : ℝ, k < B.outerRate →
            let M := outerRadiationEnvelope hδ.le B.outerRate k x
            (∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ δ * Real.exp (-B.outerRate * v) →
              Real.exp (k * v) * |scalarTransportCorrection hV ν x.2.1 u v| ≤
                D * Real.exp (B.outerRate * v) * causalExpIntegral hV (B.outerRate - k) M v) ∧
            (∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
              (u : ℝ) ≤ δ * Real.exp (-B.outerRate * v) →
                Real.exp (k * v) * |F u v| ≤
                  C * δ ^ 2 * causalExpIntegral hV (B.outerRate - k) M v) ∧
            ∀ (l S : ℝ) (g : ℝ → ℝ), T ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
              (∀ t ∈ Icc l S, g t ∈ Icc 0 U ∧ g t ≤ δ * Real.exp (-B.outerRate * t)) →
              IntegrableOn (fun t => (Real.exp (k * t) * F (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2)
                (Icc l S) ∧
              (∫ t in l..S, (Real.exp (k * t) * F (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2) ≤
                (C * δ ^ 2 / (B.outerRate - k)) ^ 2 *
                  ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  intro hi hr0
  let a := B.outerRate
  let ρ := (B.event - dH) / 2
  let R := B.event + dH
  have ha : 0 < a := B.outerRate_pos
  have hρ : 0 < ρ := half_pos (sub_pos.2 hdHR)
  have hR : 0 ≤ R := add_nonneg B.event_pos.le hdH
  have hρR : ρ ≤ R := by dsimp only [ρ, R]; linarith only [B.event_pos, hdH]
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨W, hW, hrlam⟩ := B.horizon_radius_lambda_bounds hs hH hdH hdHR hb hrdec
  have haxis (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : r t ∈ Icc (2 * ρ) R :=
    ⟨by dsimp only [ρ]; linarith only [(hrlam t ht).1.1], (hrlam t ht).1.2⟩
  have hlout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      |horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological| ≤ W :=
    (hrlam t ht).2.trans (mul_le_of_le_one_right hW (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) ht)))
  have hout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : Real.exp (0 * t) * |h t| ≤ H := by
    simp only [zero_mul, Real.exp_zero, one_mul]
    exact (hb t).trans (mul_le_of_le_one_right hH (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hs.le) ht)))
  obtain ⟨nH, NH, hnH, _, hNH, hνaxis⟩ := hOut.nu_bounds hs hc hi hrc hr0
  obtain ⟨δ₀, L₀, hδ₀, hδ₀1, _hδ₀r, _hL₀, hb₀⟩ := exists_horizon_outer_bounds
    hc hi hrc hr0 hφ hrd ha le_rfl ha hρ hnH (zero_lt_one.trans_le hNH) hH hW hA haxis hνaxis hout hlout
  let N := (5 / 3) * NH
  have hN : 0 < N := by dsimp only [N]; positivity
  obtain ⟨P, hP, hpot⟩ := radialPotential_bounded B.charge B.cosmological (R := R) hρ
  let C₀ := R * W / ρ
  let C₁ := 4 * R * P * N / ρ
  let L := 1 + C₁
  let C := L * N / ρ ^ 2
  let D := N / ρ
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hL : 0 < L := by dsimp only [L]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hD : 0 < D := div_pos hN hρ
  refine ⟨δ₀, L, C, D, hδ₀, hδ₀1, hL, hC, hD, ?_⟩
  intro δ hδ hδδ
  have hlim : Tendsto (fun t : ℝ => C₀ * Real.exp (-(2 * s) * t)) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-(2 * s) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith only [hs] : -(2 * s) < 0))
    simpa only [mul_zero] using he.const_mul C₀
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually_lt_const hδ)
  refine ⟨max 0 T, le_max_left _ _, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn ν F
  have hcb : 0 ≤ a * (1 - 1 / p.toReal) :=
    mul_nonneg ha.le (by linarith only [(incoming_exponent_bounds hp).1])
  have hscale (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ δ * Real.exp (-a * v)) :
      (u : ℝ) * Real.exp (a * v) ≤ δ := by
    have hh := mul_le_mul_of_nonneg_right hu (Real.exp_pos (a * v)).le
    simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] using hh
  have hgeo (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ δ * Real.exp (-a * v)) :
      ρ ≤ x.1 u v 0 ∧ |ν u v| ≤ N * Real.exp (a * v) ∧
        |x.2.1 u v 0| ≤ C₀ * Real.exp (-(2 * s) * v) + C₁ * u * Real.exp (a * v) := by
    let hfS := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
    have huR : (u : ℝ) < r 0 := u.property.2.trans_lt hUR
    let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (v : ℝ))
      le_rfl (by linarith only [u.property.2]) le_rfl (by linarith only [v.property.2]) x
    have hy : IsWaveIntegral u.property.1 v.property.1 B.charge B.cosmological
        (incomingWaveCurve u.property.1 huR hp hfS (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological (v : ℝ) hc hi hrc hr0)
        (incomingWaveVelocity huR hp hfS) y :=
      hx.horizon_prefix hU hV hUR u.property.1 v.property.1 u.property.2 v.property.2 hc hi hrc hr0 hp hf
    have hg := hb₀ u v u.property.1 v.property.1 huR p hp f hfS y hy
      ((scalar_prefix_norm_le u.property.2 hf).trans hfn) hcb ((hscale u v hu).trans hδδ)
    have hlo (q : Icc (0 : ℝ) u) (t : Icc (0 : ℝ) v) : ρ ≤ y.1 q t 0 := by
      linarith only [(hg q t).1, hρ]
    have hn (q : Icc (0 : ℝ) u) (t : Icc (0 : ℝ) v) :
        |radialNuField v.property.1 B.charge B.cosmological
          (incomingWaveCurve u.property.1 huR hp hfS (horizonPhi h r 0)) y.1 hy.choose q t| ≤ N * Real.exp (a * t) := by
      rw [abs_of_neg (hy.interior_gauge u.property.1 v.property.1 huR hc hi hrc hr0 hφ hrd hp hfS q t).2.2.1]
      exact (hg q t).2.2.2.2
    let q : Icc (0 : ℝ) u := ⟨u, u.property.1, le_rfl⟩
    let t : Icc (0 : ℝ) v := ⟨v, v.property.1, le_rfl⟩
    have hl := (hy.horizon_outer_radial u.property.1 v.property.1 huR hc hi hrc hr0 hφ hrd hp hfS
      ha.le (by positivity : 0 ≤ 2 * s) hρ hρR hN.le hP hW hpot hlo
      (fun w => haxis w w.property.1) hn (fun w => (hrlam w w.property.1).2) (hscale u v hu) q t).2.2.2.2.1
    have he := hy.horizon_overlap u.property.1 v.property.1 huR hU hV hUR hc hi hrc hr0 hp hfS hf hx
      q.property u.property t.property v.property
    have hne := hy.horizon_overlap_nu u.property.1 v.property.1 huR hU hV hUR hc hi hrc hr0 hp hfS hf hx
      q.property u.property t.property v.property
    have hr := hlo q t
    have hn' := hn q t
    change y.1 q t = x.1 u v ∧ y.2.1 q t = x.2.1 u v at he
    change _ = ν u v at hne
    rw [he.1] at hr
    rw [he.2] at hl
    rw [hne] at hn'
    exact ⟨hr, hn', hl⟩
  have hlam (u : Icc 0 U) (v : Icc 0 V) (hv : max 0 T ≤ (v : ℝ))
      (hu : (u : ℝ) ≤ δ * Real.exp (-a * v)) : |x.2.1 u v 0| ≤ L * δ := by
    have hh := (hgeo u v hu).2.2
    have ht := (hT v ((le_max_right _ _).trans hv)).le
    have hw := mul_le_mul_of_nonneg_left (hscale u v hu) hC₁
    dsimp only [L]
    nlinarith only [hh, ht, hw]
  refine ⟨hlam, ?_⟩
  intro k hk M
  have hB : Antitone (fun v : Icc 0 V => δ * Real.exp (-a * v)) := by
    intro v w hvw
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonpos_left hvw (neg_nonpos.2 ha.le))) hδ.le
  have hin (u : Icc 0 U) : |incomingWaveCurve hU hUR hp hf (horizonPhi h r 0) u 0| ≤ r 0 := by
    rw [incomingWaveCurve_apply]
    change |r 0 - (u : ℝ)| ≤ r 0
    rw [abs_of_pos (sub_pos.2 (u.property.2.trans_lt hUR))]
    exact sub_le_self _ u.property.1
  have hglobal (q : Icc 0 U) (t : Icc 0 V) (_hq : (q : ℝ) ≤ δ * Real.exp (-a * t)) :
      |x.2.1 q t 0| ≤ ‖x.2.1‖ :=
    (norm_le_pi_norm (x.2.1 q t) 0).trans
      (((x.2.1 q).norm_coe_le_norm t).trans (x.2.1.norm_coe_le_norm q))
  have hcor := (hx.outer_radiation_majorant_on hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 hρ hN.le (norm_nonneg x.2.1)
    (fun w => δ * Real.exp (-a * w)) hB (fun q w hq => (hgeo q w hq).1) hin
    (fun q w hq => (hgeo q w hq).2.1) hglobal
    (ContinuousMap.const _ (ContinuousMap.const _ 1)) (fun _ => monotone_const) M
    (outerRadiationEnvelope_nonneg hδ.le a k x)
    (fun q w hq => by simpa using (outerRadiationEnvelope_le_iff hU hδ.le x w).1 le_rfl q hq)).1
  simp only [ContinuousMap.const_apply, mul_one] at hcor
  refine ⟨hcor, ?_⟩
  have hfb (u : Icc 0 U) (v : Icc 0 V) (hv : max 0 T ≤ (v : ℝ))
      (hu : (u : ℝ) ≤ δ * Real.exp (-a * v)) :
      Real.exp (k * v) * |F u v| ≤ C * δ ^ 2 * causalExpIntegral hV (a - k) M v := by
    have hh := hx.outer_feedback_kernel_at hx.choose rfl
      (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 hρ hN.le (mul_pos hL hδ).le
      (fun w => δ * Real.exp (-a * w)) hB (fun q w hq => (hgeo q w hq).1) hin
      (fun q w hq => (hgeo q w hq).2.1) hscale M (outerRadiationEnvelope_nonneg hδ.le a k x)
      (fun q w hq => (outerRadiationEnvelope_le_iff hU hδ.le x w).1 le_rfl q hq) u v hu
      (fun q hq => hlam q v hv ((show (q : ℝ) ≤ u from hq).trans hu))
    exact hh.trans_eq (by dsimp only [C]; ring)
  refine ⟨hfb, ?_⟩
  intro l S g hl hlS hSV hgc hg
  have harg : ContinuousOn (fun t => (projIcc 0 U hU (g t), projIcc 0 V hV t)) (Icc l S) :=
    ((continuous_projIcc (a := (0 : ℝ)) (b := U) (h := hU)).comp_continuousOn hgc).prodMk
      (continuous_projIcc (a := (0 : ℝ)) (b := V) (h := hV)).continuousOn
  have hFc : ContinuousOn (fun t => F (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) (Icc l S) := by
    simpa only [Function.comp_def, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair] using
      F.uncurry.continuous.comp_continuousOn harg
  have hEc : ContinuousOn (fun t => Real.exp (k * t) * F (projIcc 0 U hU (g t))
      (projIcc 0 V hV t)) (Icc l S) := by fun_prop
  refine ⟨(hEc.pow 2).integrableOn_Icc, ?_⟩
  apply causalExpIntegral_dominated_energy hV (sub_pos.2 hk) ((le_max_left _ _).trans hl) hlS hSV M hEc
  intro t ht
  have htV : t ∈ Icc 0 V := ⟨(le_max_left _ _).trans (hl.trans ht.1), ht.2.trans hSV⟩
  rw [abs_mul, abs_of_pos (Real.exp_pos _), projIcc_of_mem hU (hg t ht).1, projIcc_of_mem hV htV]
  exact hfb ⟨g t, (hg t ht).1⟩ ⟨t, htV⟩ (hl.trans ht.1) (hg t ht).2

end CauchyHorizon.Background
