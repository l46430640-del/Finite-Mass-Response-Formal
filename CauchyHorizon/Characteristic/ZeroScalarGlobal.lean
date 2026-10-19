import CauchyHorizon.Characteristic.ZeroScalarSign
import CauchyHorizon.Characteristic.ScalarOverlap
import CauchyHorizon.Characteristic.OutgoingConstraint

/-! Trapping confines the adverse scalar correction to the positive outer prefix. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_zero_scalar_positive (B : Background) {s l c H Hlo dH : ℝ} {h r : ℝ → ℝ}
    (hs : 0 < s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s)
    (hl : l < 2 * s + c) (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hlo : ∀ t ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * t) ≤ h t)
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ W : ℝ, 0 < W ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p)
        (hf : MemLp (fun _ : ℝ => (0 : ℝ)) p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        U ≤ W →
          (∀ u v, 0 < x.1 u v 0 * x.2.1 u v 1) ∧
          (∀ u (v : Icc 0 V), 0 < (v : ℝ) → 0 < scalarTransportCorrection hV
            (radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose) x.2.1 u v) ∧
          ∀ u, Monotone (scalarTransportCorrection hV
            (radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose) x.2.1 u) := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  obtain ⟨δs, Ws, hδs, hWs, hsign⟩ := B.exists_zero_outer_scalar_positive
    hs hc0 hca hcs hl hH hHlo hdH hdHR hc hb hlo hrc hrb hrd hrdec hOut
  obtain ⟨δf, n, N, L, q, K, T₀, hδf, _hδr, _hn, _hN, _hL, hq, _hK, hT₀, hflux⟩ :=
    B.exists_outer_flux_prefix hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut
      (c := 0) le_rfl ha hs.le (A := 0) le_rfl
  let δ := min δs δf
  have hδ : 0 < δ := lt_min hδs hδf
  have htail : Tendsto (fun t : ℝ => K * Real.exp (-(2 * s) * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq, mul_zero] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (by linarith only [hs] : -(2 * s) < 0))).const_mul K
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (htail.eventually_lt_const (mul_pos hq hδ))
  let T := max T₀ T₁
  have hT : 0 ≤ T := hT₀.trans (le_max_left _ _)
  let W := min Ws (δ * Real.exp (-a * T) / 2)
  have hW : 0 < W := lt_min hWs (by positivity)
  refine ⟨W, hW, ?_⟩
  intro U V hU hV hUR p hp hf x hx hUW
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hr (u : Icc 0 U) (v : Icc 0 V) : 0 < x.1 u v 0 :=
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.1
  have hν (u : Icc 0 U) (v : Icc 0 V) : ν u v < 0 :=
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1
  have hsmall (u : Icc 0 U) : (u : ℝ) * Real.exp (a * T) < δ := by
    have hh := mul_le_mul_of_nonneg_right
      (u.property.2.trans (hUW.trans (min_le_right _ _))) (Real.exp_pos (a * T)).le
    have he : (δ * Real.exp (-a * T) / 2) * Real.exp (a * T) = δ / 2 := by
      rw [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add]
      simp only [neg_mul, neg_add_cancel, Real.exp_zero, mul_one]
    rw [he] at hh
    exact hh.trans_lt (half_lt_self hδ)
  have htrapped (u : Icc 0 U) (v : Icc 0 V)
      (hu : δ ≤ (u : ℝ) * Real.exp (a * v)) : x.2.1 u v 0 < 0 := by
    have hTv : T ≤ (v : ℝ) := by
      by_contra hv
      have hh := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (lt_of_not_ge hv).le ha.le)) u.property.1
      exact (hsmall u).not_ge (hu.trans hh)
    have hcont : Continuous (fun t : ℝ => (u : ℝ) * Real.exp (a * t)) := by fun_prop
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hTv hcont.continuousOn
      (show δ ∈ Icc ((u : ℝ) * Real.exp (a * T)) ((u : ℝ) * Real.exp (a * v)) from
        ⟨(hsmall u).le, hu⟩)
    change (u : ℝ) * Real.exp (a * t) = δ at he
    have htV : t ∈ Icc 0 V := ⟨hT.trans ht.1, ht.2.trans v.property.2⟩
    let hf' := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
    have huR : (u : ℝ) < r 0 := u.property.2.trans_lt hUR
    have hbudget : (eLpNorm (fun _ : ℝ => (0 : ℝ)) p (volume.restrict (Icc 0 u))).toReal ≤ 0 := by simp
    have hpR : 0 ≤ a * (1 - 1 / p.toReal) :=
      mul_nonneg ha.le ((by norm_num : (0 : ℝ) ≤ 3 / 4).trans (incoming_exponent_bounds hp).1)
    obtain ⟨y, ⟨hy, hg⟩, _⟩ := hflux u t u.property.1 htV.1 huR p hp _ hf' hbudget hpR
      (he.le.trans (min_le_right _ _))
    let uu : Icc 0 (u : ℝ) := ⟨u, u.property.1, le_rfl⟩
    let tt : Icc 0 t := ⟨t, htV.1, le_rfl⟩
    have hg' := (hg uu tt).2.2.2.2.2.2.2 ((le_max_left _ _).trans ht.1)
    have hover := hy.horizon_overlap u.property.1 htV.1 huR hU hV hUR
      hc hi hrc hr0 hp hf' hf hx uu.property u.property tt.property htV
    rw [hover.1, hover.2] at hg'
    have he' : q * (u : ℝ) * Real.exp (a * t) = q * δ := by rw [mul_assoc, he]
    change x.1 u ⟨t, htV⟩ 0 * x.2.1 u ⟨t, htV⟩ 0 ≤
      K * Real.exp (-(2 * s) * t) - q * (u : ℝ) * Real.exp (a * t) at hg'
    rw [he'] at hg'
    have hlneg : x.2.1 u ⟨t, htV⟩ 0 < 0 := by
      have hh := hT₁ t ((le_max_right _ _).trans ht.1)
      exact neg_of_mul_neg_right (hg'.trans_lt (sub_neg.2 hh)) (hr u ⟨t, htV⟩).le
    exact (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf
      u ⟨t, htV⟩ v ht.2 hlneg).1
  have hbad (u : Icc 0 U) (v : Icc 0 V) :
      scalarPositiveLambdaCorrection hU hV x.1 x.2.1 ν u v < h v := by
    let D := min (u : ℝ) (δ / Real.exp (a * v))
    have hD : 0 ≤ D := le_min u.property.1 (div_nonneg hδ.le (Real.exp_pos _).le)
    have hDu : D ≤ (u : ℝ) := min_le_left _ _
    have hDU : D ≤ U := hDu.trans u.property.2
    have hDR : D < r 0 := hDU.trans_lt hUR
    have hwidth : D * Real.exp (a * v) ≤ δ := (le_div_iff₀ (Real.exp_pos _)).1 (min_le_right _ _)
    let hfD := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hDU) le_rfl)
    let y := waveTranslate (a := 0) (U := D) (b := 0) (V := (v : ℝ))
      le_rfl (by linarith only [hDU]) le_rfl (by linarith only [v.property.2]) x
    have hy : IsWaveIntegral hD v.property.1 B.charge B.cosmological
        (incomingWaveCurve hD hDR hp hfD (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological (v : ℝ) hc hi hrc hr0)
        (incomingWaveVelocity hDR hp hfD) y :=
      hx.horizon_prefix hU hV hUR hD v.property.1 hDU v.property.2 hc hi hrc hr0 hp hf
    let N' := radialNuField v.property.1 B.charge B.cosmological
      (incomingWaveCurve hD hDR hp hfD (horizonPhi h r 0)) y.1 hy.choose
    let dd : Icc 0 D := ⟨D, hD, le_rfl⟩
    let vv : Icc 0 (v : ℝ) := ⟨v, v.property.1, le_rfl⟩
    have hb' := (hsign D v hD v.property.1 hDR p hp hfD y hy
      (hDU.trans (hUW.trans (min_le_left _ _))) (hwidth.trans (min_le_left _ _))).1 dd vv
    let G := fun t : ℝ => max (x.2.1 (projIcc 0 U hU t) v 0) 0 *
      |scalarTransportCorrection hV ν x.2.1 (projIcc 0 U hU t) v| / x.1 (projIcc 0 U hU t) v 0
    have he : scalarPositiveLambdaCorrection hD v.property.1 y.1 y.2.1 N' dd vv =
        ∫ t in (0 : ℝ)..D, G t := by
      unfold scalarPositiveLambdaCorrection
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hD] at ht
      have htU : t ∈ Icc 0 U := ⟨ht.1, ht.2.trans hDU⟩
      have hover := hy.horizon_overlap hD v.property.1 hDR hU hV hUR
        hc hi hrc hr0 hp hfD hf hx ht htU vv.property v.property
      have hs' := hy.horizon_overlap_zeta hD v.property.1 hDR hU hV hUR
        hc hi hrc hr0 hp hfD hf hx ht htU vv.property v.property
      simp only [mul_zero, zero_add] at hs'
      dsimp only [G]
      rw [projIcc_of_mem hD ht, projIcc_of_mem hU htU, hover.1, hover.2]
      change max (x.2.1 ⟨t, htU⟩ v 0) 0 *
        |scalarTransportCorrection v.property.1 N' y.2.1 ⟨t, ht⟩ vv| / x.1 ⟨t, htU⟩ v 0 = _
      rw [hs']
    have hrc' : Continuous (fun t => x.1 (projIcc 0 U hU t) v 0) :=
      ((continuous_apply 0).comp ((continuous_eval_const v).comp x.1.continuous)).comp continuous_projIcc
    have hlc : Continuous (fun t => x.2.1 (projIcc 0 U hU t) v 0) :=
      ((continuous_apply 0).comp ((continuous_eval_const v).comp x.2.1.continuous)).comp continuous_projIcc
    have hsc : Continuous (fun t => scalarTransportCorrection hV ν x.2.1 (projIcc 0 U hU t) v) :=
      ((continuous_eval_const v).comp (scalarTransportCorrection hV ν x.2.1).continuous).comp continuous_projIcc
    have hGc : Continuous G := ((hlc.max continuous_const).mul hsc.abs).div hrc' (fun _ => (hr _ _).ne')
    have htailzero : (∫ t in D..(u : ℝ), G t) = 0 := by
      by_cases heq : D = (u : ℝ)
      · rw [heq, intervalIntegral.integral_same]
      have hDeq : D = δ / Real.exp (a * v) := min_eq_right (le_of_not_ge (by
        intro hh
        exact heq (min_eq_left hh)))
      calc
        _ = ∫ t in D..(u : ℝ), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hDu] at ht
          have htU : t ∈ Icc 0 U := ⟨hD.trans ht.1, ht.2.trans u.property.2⟩
          have htδ : δ ≤ t * Real.exp (a * v) := (div_le_iff₀ (Real.exp_pos _)).1 (hDeq ▸ ht.1)
          dsimp only [G]
          rw [projIcc_of_mem hU htU, max_eq_right (htrapped ⟨t, htU⟩ v htδ).le, zero_mul, zero_div]
        _ = 0 := intervalIntegral.integral_zero
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hGc.intervalIntegrable (0 : ℝ) D) (hGc.intervalIntegrable D (u : ℝ))
    rw [htailzero, add_zero] at hadd
    change (∫ t in (0 : ℝ)..(u : ℝ), G t) < h v
    rw [← hadd, ← he]
    exact hb'
  have hzero : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 1 = 0 := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]
    rfl
  have hpositive := hx.zero_scalar_positive hr rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 hzero hν (by
      intro u v
      rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
      change scalarPositiveLambdaCorrection hU hV x.1 x.2.1 ν u v < r v * (h v / r v)
      rw [mul_div_cancel₀ _ (hr0 v)]
      exact hbad u v)
  refine ⟨hpositive.1, hpositive.2, ?_⟩
  intro u b d hbd
  change (∫ t in (0 : ℝ)..(b : ℝ), intervalExtension hV (scalarTransportSource ν x.2.1 u) t) ≤
    ∫ t in (0 : ℝ)..(d : ℝ), intervalExtension hV (scalarTransportSource ν x.2.1 u) t
  apply intervalIntegral.integral_mono_interval le_rfl b.property.1 hbd _
    ((intervalExtension hV (scalarTransportSource ν x.2.1 u)).continuous.intervalIntegrable _ _)
  apply Filter.Eventually.of_forall
  intro t
  change 0 ≤ -ν u (projIcc 0 V hV t) * x.2.1 u (projIcc 0 V hV t) 1
  exact mul_nonneg (neg_pos.2 (hν _ _)).le
    (pos_of_mul_pos_right (hpositive.1 _ _) (hr _ _).le).le

end CauchyHorizon.Background
