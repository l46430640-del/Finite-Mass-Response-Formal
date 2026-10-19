import CauchyHorizon.Characteristic.OuterSectionNormalization
import CauchyHorizon.Characteristic.BackgroundNormalization
import CauchyHorizon.Characteristic.MatchingFeedback
import CauchyHorizon.Characteristic.OutgoingConstraint

/-! Propagation from a fixed outer section on actual pre-arrival prefixes. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_prearrival_normalization (B : Background) {s H dH A Y j D : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hY : B.inner < Y) (hYe : Y < B.event) (hj : 0 < j) (hD : 0 < D)
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
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
          j ≤ (u : ℝ) * Real.exp (B.outerRate * v) →
          (u : ℝ) * Real.exp (B.outerRate * v) ≤ D →
          (∀ q ≤ u, ∀ t ≤ v, Y ≤ x.1 q t 0) →
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          x.1 u v 0 ∈ Ioo B.inner B.event ∧
            |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F (x.1 u v 0)))| +
              |Real.log (B.z (x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (B.outerRate * v))))| < ε := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  let a := B.outerRate
  let cν := Real.exp (∫ t in Ioi 0,
    2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - a)
  have ha : 0 < a := B.outerRate_pos
  have hcν : 0 < cν := Real.exp_pos _
  have hY0 : 0 < Y := B.inner_pos.trans hY
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let c := min s a / 2
  have hc0 : 0 < c := half_pos (lt_min hs ha)
  have hca : c < a := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  have hcs : c ≤ s := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (half_le_self hs.le)
  have hcHalf : c ≤ a / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let γ := min a (2 * c)
  have hγ : 0 < γ := lt_min ha (by positivity)
  obtain ⟨U₀, Cm, hU₀, _, hCm, hfeedback⟩ := B.exists_bounded_width_feedback_decay
    hs hH hdH hdHR hA hY0 (by linarith only [hYe, hdH]) hD.le hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  dsimp only
  intro ε hε
  have hlogJ : ContinuousAt (fun z : ℝ => Real.log (a * z)) (1 / a) := by
    fun_prop (disch := simp [ha.ne'])
  have hlogP : ContinuousAt Real.log (1 : ℝ) := Real.continuousAt_log one_ne_zero
  obtain ⟨ηJ, hηJ, hJnear⟩ := Metric.mem_nhds_iff.1
    (hlogJ.tendsto.abs.eventually_lt_const (show |Real.log (a * (1 / a))| < ε / 4 by simp [ha.ne']; positivity))
  obtain ⟨ηP, hηP, hPnear⟩ := Metric.mem_nhds_iff.1
    (hlogP.tendsto.abs.eventually_lt_const (show |Real.log (1 : ℝ)| < ε / 4 by simp; positivity))
  let cap := min j ((B.event - Y) / (4 * cν))
  have hcap : 0 < cap := lt_min hj (div_pos (sub_pos.2 hYe) (by positivity))
  obtain ⟨δ, T₁, hδ, hδcap, hT₁, _, hsection⟩ := B.exists_outer_section_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut cap (min ηJ ηP) hcap (lt_min hηJ hηP)
  have hδj : δ < j := hδcap.trans_le (min_le_left _ _)
  have hδY : 2 * cν * δ < B.event - Y := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4 * cν)).1 (hδcap.trans_le (min_le_right _ _))
    nlinarith only [hh, mul_pos hcν hδ]
  let Z := B.event - cν * δ / 4
  have hZ : Z < B.event := sub_lt_self _ (by positivity)
  have hYZ : Y < Z := by dsimp only [Z]; nlinarith only [hδY, mul_pos hcν hδ]
  have hFc : ContinuousOn B.F (Icc Y Z) := fun z hz =>
    (B.F_hasDerivAt (hY0.trans_le hz.1).ne').continuousAt.continuousWithinAt
  obtain ⟨rMax, hrMax, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hYZ.le) hFc
  let q := -B.F rMax
  have hq : 0 < q := neg_pos.2 (B.F_neg ⟨hY.trans_le hrMax.1, hrMax.2.trans_lt hZ⟩)
  have hFbound (z : ℝ) (hz : z ∈ Icc Y Z) : B.F z ≤ -q := by
    rw [show -q = B.F rMax by dsimp only [q]; exact neg_neg _]
    exact hmax hz
  obtain ⟨C, hC, htransport⟩ := B.exists_band_normalization_control hY hZ
  let L := max 0 (Real.log (D / δ) / a)
  have hL : 0 ≤ L := le_max_left _ _
  have hexp (b : ℝ) (hb : 0 < b) : Tendsto (fun t : ℝ => Real.exp (-b * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hb))
  have hwidth := (hexp a ha).const_mul D
  have hmass := (hexp γ hγ).const_mul Cm
  have hprop := (hexp γ hγ).const_mul (C * Cm * L)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1
    ((hwidth.eventually_lt_const (by simpa only [mul_zero] using hU₀)).and
      ((hmass.eventually_lt_const (show Cm * 0 < q * Y / 4 by rw [mul_zero]; positivity)).and
        (hprop.eventually_lt_const (show (C * Cm * L) * 0 < ε / 2 by simp; positivity))))
  let T₀ := max T₁ (max 0 T₂)
  have hT₀ : 0 ≤ T₀ := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨T₀ + L, add_nonneg hT₀ hL, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn u v hv hjv hDv hfloor
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
  let κ := fun t : Icc 0 V => -Real.exp (x.1 u t 2) / (4 * ν u t)
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hn (t : Icc 0 V) : ν u t < 0 := (hg u t).2.2.1
  have hu : 0 < (u : ℝ) := (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 (hj.trans_le hjv)
  let σ := (u : ℝ) * Real.exp (a * v)
  have hσ : 0 < σ := mul_pos hu (Real.exp_pos _)
  let d := Real.log (σ / δ) / a
  have hd : 0 < d := div_pos (Real.log_pos ((one_lt_div hδ).2 (hδj.trans_le hjv))) ha
  have hdL : d ≤ L := (div_le_div_of_nonneg_right
    (Real.log_le_log (div_pos hσ hδ) (div_le_div_of_nonneg_right hDv hδ.le)) ha.le).trans (le_max_right _ _)
  let w := (v : ℝ) - d
  have hwT : T₀ ≤ w := by dsimp only [w]; linarith only [hv, hdL]
  have hw0 : 0 ≤ w := hT₀.trans hwT
  have hwv : w ≤ (v : ℝ) := sub_le_self _ hd.le
  let ww : Icc 0 V := ⟨w, hw0, hwv.trans v.property.2⟩
  have hwsection : (u : ℝ) * Real.exp (a * w) = δ := by
    have had : a * d = Real.log (σ / δ) := by dsimp only [d]; field_simp
    dsimp only [w]
    rw [mul_sub, Real.exp_sub, had, Real.exp_log (div_pos hσ hδ)]
    rw [← mul_div_assoc]
    change σ / (σ / δ) = δ
    field_simp
  have hvT₂ : T₂ ≤ (v : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (hwT.trans hwv))
  have hu₀ : (u : ℝ) ≤ U₀ := by
    have hh := mul_le_mul_of_nonneg_right hDv (Real.exp_pos (-a * v)).le
    change (u : ℝ) * Real.exp (a * v) * Real.exp (-a * v) ≤ _ at hh
    have he : (u : ℝ) ≤ D * Real.exp (-a * v) := by
      simpa only [mul_assoc, ← Real.exp_add, show a * (v : ℝ) + -a * v = 0 by ring,
        Real.exp_zero, mul_one] using hh
    exact he.trans (hT₂ v hvT₂).1.le
  have hcb : c ≤ a * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le
    linarith only [hcHalf, hh, ha]
  have hpoint (t : Icc 0 V) (ht : t ≤ v) : |κ t - 1| + |m u t - B.mass| ≤ Cm * Real.exp (-γ * t) := by
    let hf' := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
    have hy := hx.horizon_prefix hU hV hUR u.property.1 t.property.1 u.property.2 t.property.2 hc hi hrc hr0 hp hf
    let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (t : ℝ))
      le_rfl (by simpa only [zero_add] using u.property.2) le_rfl (by simpa only [zero_add] using t.property.2) x
    let uu : Icc 0 (u : ℝ) := ⟨u, u.property.1, le_rfl⟩
    let tt : Icc 0 (t : ℝ) := ⟨t, t.property.1, le_rfl⟩
    have hyfloor (b z) : Y ≤ y.1 b z 0 :=
      hfloor _ (by change 0 + (b : ℝ) ≤ u; simpa only [zero_add] using b.property.2)
        _ (by change 0 + (z : ℝ) ≤ v; simpa only [zero_add] using z.property.2.trans ht)
    have htw : (u : ℝ) * Real.exp (a * t) ≤ D :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht ha.le)) hu.le).trans hDv
    have hh := hfeedback u t u.property.1 t.property.1 (u.property.2.trans_lt hUR) p hp f hf' y hy
      ((scalar_prefix_norm_le u.property.2 hf).trans hfn) hcb hu₀ hyfloor htw uu
    have he := hy.horizon_overlap u.property.1 t.property.1 (u.property.2.trans_lt hUR) hU hV hUR
      hc hi hrc hr0 hp hf' hf hx uu.property u.property tt.property t.property
    have hne := hy.horizon_overlap_nu u.property.1 t.property.1 (u.property.2.trans_lt hUR) hU hV hUR
      hc hi hrc hr0 hp hf' hf hx uu.property u.property tt.property t.property
    simp only [massField_apply] at hh
    rw [he.1, he.2, hne] at hh
    exact hh
  have hsec := hsection U V hU hV hUR p hp f hf x hx hfn u ww
    ((le_max_left _ _).trans hwT) (by rw [hwsection]; exact half_le_self hδ.le) hwsection.le
  have hstart : x.1 u ww 0 ∈ Icc Y Z :=
    ⟨hfloor u le_rfl ww hwv, by dsimp only [Z]; linarith only [hsec.1.1]⟩
  have hwT₂ : T₂ ≤ w := (le_max_right _ _).trans ((le_max_right _ _).trans hwT)
  have hmsmall : |m u ww - B.mass| < q * Y / 4 :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans_lt ((hpoint ww hwv).trans_lt (hT₂ w hwT₂).2.1)
  have hFactual : horizonFunction (x.1 u ww 0) (m u ww) B.charge B.cosmological < 0 := by
    rw [horizonFunction_mass_difference]
    change B.F (x.1 u ww 0) - 2 * (m u ww - B.mass) / x.1 u ww 0 < 0
    apply sub_neg.2
    apply (lt_div_iff₀ (hY0.trans_le hstart.1)).2
    have hh := mul_le_mul_of_nonneg_right (hFbound _ hstart) (hY0.trans_le hstart.1).le
    have hh' := mul_le_mul_of_nonpos_left hstart.1 (neg_nonpos.2 hq.le)
    nlinarith only [hh, hh', (abs_lt.1 hmsmall).1, mul_pos hq hY0]
  have hlam : x.2.1 u ww 0 < 0 := by
    have he := (renormalizedMass_first_order (hx.choose u ww) (hn ww).ne
      (x.2.1 u ww 0) (x.1 u ww 2) B.charge B.cosmological).1
    change x.2.1 u ww 0 = κ ww * horizonFunction (x.1 u ww 0) (m u ww) B.charge B.cosmological at he
    rw [he]
    exact mul_neg_of_pos_of_neg (hg u ww).2.2.2.1 hFactual
  have hband (t : Icc 0 V) (ht : t ∈ Icc ww v) : x.1 u t 0 ∈ Icc Y Z :=
    ⟨hfloor u le_rfl t ht.2, ((hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf
      u ww t ht.1 hlam).2).trans hstart.2⟩
  have hvband : x.1 u v 0 ∈ Ioo B.inner B.event :=
    ⟨hY.trans_le (hband v ⟨hwv, le_rfl⟩).1, (hband v ⟨hwv, le_rfl⟩).2.trans_lt hZ⟩
  let E := fun t : ℝ => |intervalExtension hV (m u) t - B.mass| +
    |-Real.exp (intervalExtension hV (x.1 u) t 2) / (4 * intervalExtension hV (ν u) t) - 1|
  have hnn (t : ℝ) : intervalExtension hV (ν u) t ≠ 0 := (hn (projIcc 0 V hV t)).ne
  have hEc : Continuous E := by dsimp only [E]; fun_prop (disch := intro t; exact mul_ne_zero (by norm_num) (hnn t))
  have hEb (t : ℝ) (ht : t ∈ Icc w (v : ℝ)) : E t ≤ Cm * Real.exp (-γ * w) := by
    have htV : t ∈ Icc 0 V := ⟨hw0.trans ht.1, ht.2.trans v.property.2⟩
    have he := (hpoint ⟨t, htV⟩ ht.2).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.2 hγ.le))) hCm)
    dsimp only [E]
    rw [intervalExtension_apply, intervalExtension_apply, intervalExtension_apply,
      projIcc_of_mem hV htV]
    rw [add_comm]
    exact he
  have hI : (∫ t in w..(v : ℝ), E t) ≤ Cm * Real.exp (-γ * w) * ((v : ℝ) - w) := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) (f := E)
      (g := fun _ => Cm * Real.exp (-γ * w)) hwv (hEc.intervalIntegrable _ _)
      intervalIntegrable_const hEb
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh
  have hnorm := htransport hU hV hUR hc hi hrc hr0 hφ hrd hp hf hx u hu ww v hwv hband
  have hinc : |Real.log ((u : ℝ) * ν u v / B.F (x.1 u v 0)) -
        Real.log ((u : ℝ) * ν u ww / B.F (x.1 u ww 0))| +
      |Real.log (B.z (x.1 u v 0)) - Real.log (B.z (x.1 u ww 0)) - a * ((v : ℝ) - w)| < ε / 2 := by
    apply hnorm.trans_lt
    apply (mul_le_mul_of_nonneg_left hI hC).trans_lt
    have hh := mul_le_mul_of_nonneg_left (show (v : ℝ) - w ≤ L by dsimp only [w]; linarith only [hdL])
      (by positivity : 0 ≤ C * Cm * Real.exp (-γ * w))
    have hh' : C * (Cm * Real.exp (-γ * w) * ((v : ℝ) - w)) ≤
        (C * Cm * L) * Real.exp (-γ * w) := by nlinarith only [hh]
    exact hh'.trans_lt (hT₂ w hwT₂).2.2
  have hinitJ : |Real.log (a * ((u : ℝ) * ν u ww / B.F (x.1 u ww 0)))| < ε / 4 :=
    hJnear (by rw [Metric.mem_ball, Real.dist_eq]; exact hsec.2.1.trans_le (min_le_left _ _))
  have hinitP : |Real.log (B.z (x.1 u ww 0) / ((u : ℝ) * (cν * Real.exp (a * w))))| < ε / 4 :=
    hPnear (by rw [Metric.mem_ball, Real.dist_eq]; exact hsec.2.2.trans_le (min_le_right _ _))
  have hwband : x.1 u ww 0 ∈ Ioo B.inner B.event := ⟨hY.trans_le hstart.1, hstart.2.trans_lt hZ⟩
  have hJpos (t : Icc 0 V) (ht : x.1 u t 0 ∈ Ioo B.inner B.event) :
      0 < (u : ℝ) * ν u t / B.F (x.1 u t 0) :=
    div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hu (hn t)) (B.F_neg ht)
  have hjeq : Real.log (a * ((u : ℝ) * ν u v / B.F (x.1 u v 0))) =
      (Real.log ((u : ℝ) * ν u v / B.F (x.1 u v 0)) -
        Real.log ((u : ℝ) * ν u ww / B.F (x.1 u ww 0))) +
          Real.log (a * ((u : ℝ) * ν u ww / B.F (x.1 u ww 0))) := by
    rw [Real.log_mul ha.ne' (hJpos v hvband).ne', Real.log_mul ha.ne' (hJpos ww hwband).ne']
    ring
  have hpeq : Real.log (B.z (x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (a * v)))) =
      (Real.log (B.z (x.1 u v 0)) - Real.log (B.z (x.1 u ww 0)) - a * ((v : ℝ) - w)) +
        Real.log (B.z (x.1 u ww 0) / ((u : ℝ) * (cν * Real.exp (a * w)))) := by
    rw [Real.log_div (B.z_pos hvband).ne' (mul_pos hu (mul_pos hcν (Real.exp_pos _))).ne',
      Real.log_div (B.z_pos hwband).ne' (mul_pos hu (mul_pos hcν (Real.exp_pos _))).ne',
      Real.log_mul hu.ne' (mul_pos hcν (Real.exp_pos _)).ne',
      Real.log_mul hu.ne' (mul_pos hcν (Real.exp_pos _)).ne',
      Real.log_mul hcν.ne' (Real.exp_ne_zero _), Real.log_mul hcν.ne' (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp]
    simp only [Real.log_exp]
    ring
  refine ⟨hvband, ?_⟩
  change |Real.log (a * ((u : ℝ) * ν u v / B.F (x.1 u v 0)))| +
    |Real.log (B.z (x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (a * v))))| < ε
  rw [hjeq, hpeq]
  exact (add_le_add (abs_add_le _ _) (abs_add_le _ _)).trans_lt
    (by linarith only [hinc, hinitJ, hinitP])

end CauchyHorizon.Background
