import CauchyHorizon.Characteristic.PrearrivalNormalization
import CauchyHorizon.Characteristic.BandRadiationDomain
import CauchyHorizon.Reduced.RadialLevel

/-! Uniform phase and logarithmic speed on a compact band of actual radii. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

theorem exists_compact_arrival_speed_tolerance (B : Background) {Y Z ε : ℝ}
    (hY : B.inner < Y) (hZ : Z < B.event) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ y ∈ Icc Y Z, ∀ n κ m : ℝ, 0 < n →
      |Real.log n| < η → |κ - 1| + |m - B.mass| < η →
      |B.outerRate * κ * (1 - 2 * (m - B.mass) / (y * B.F y)) / n - B.outerRate| < ε := by
  have hy (y : ℝ) (hy : y ∈ Icc Y Z) : y ∈ Ioo B.inner B.event :=
    ⟨hY.trans_le hy.1, hy.2.trans_lt hZ⟩
  have hcont : ContinuousOn (fun y => 2 / (y * B.F y)) (Icc Y Z) := by
    intro y hyz
    have hy0 := B.inner_pos.trans (hy y hyz).1
    exact (continuousAt_const.div (continuousAt_id.mul
      (B.F_hasDerivAt hy0.ne').continuousAt) (mul_ne_zero hy0.ne' (B.F_neg (hy y hyz)).ne)).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let C := max 1 C₀
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let F := fun q : ℝ × ℝ => a * q.2 * Real.exp (-q.1)
  have hFc : Continuous F := by fun_prop
  have hzero : |F (0, 1) - a| < min (ε / 2) 1 := by
    simpa only [F, neg_zero, Real.exp_zero, mul_one, sub_self, abs_zero] using
      lt_min (half_pos hε) zero_lt_one
  obtain ⟨η₀, hη₀, hnear⟩ := Metric.mem_nhds_iff.1
    (((hFc.continuousAt.tendsto.sub_const a).abs).eventually_lt_const hzero)
  let η := min η₀ (ε / (2 * (a + 1) * C))
  have hη : 0 < η := lt_min hη₀ (by positivity)
  refine ⟨η, hη, ?_⟩
  intro y hyz n κ m hn hlog hm
  have hκ : |κ - 1| < η₀ := ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt hm).trans_le (min_le_left _ _)
  have hdm : |m - B.mass| < ε / (2 * (a + 1) * C) :=
    ((le_add_of_nonneg_left (abs_nonneg _)).trans_lt hm).trans_le (min_le_right _ _)
  have hF := hnear (show (Real.log n, κ) ∈ Metric.ball (0, 1) η₀ by
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using
      And.intro (hlog.trans_le (min_le_left _ _)) hκ)
  change |F (Real.log n, κ) - a| < min (ε / 2) 1 at hF
  have hFa : |F (Real.log n, κ)| < a + 1 := by
    have hh := (abs_sub_le (F (Real.log n, κ)) a 0)
    rw [sub_zero, sub_zero, abs_of_pos ha] at hh
    linarith only [hh, hF.trans_le (min_le_right _ _)]
  have hCy₀ : |2 / (y * B.F y)| ≤ C₀ := by simpa only [Real.norm_eq_abs] using hC₀ y hyz
  have hCy : |2 / (y * B.F y)| ≤ C := hCy₀.trans (le_max_right _ _)
  have hprod : |F (Real.log n, κ) * (2 / (y * B.F y)) * (m - B.mass)| < ε / 2 := by
    rw [abs_mul, abs_mul]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul hFa.le hCy (abs_nonneg _) (by positivity : 0 ≤ a + 1)) (abs_nonneg (m - B.mass))
    have hd := (lt_div_iff₀ (by positivity : 0 < 2 * (a + 1) * C)).1 hdm
    nlinarith only [hh, hd]
  have heq : a * κ * (1 - 2 * (m - B.mass) / (y * B.F y)) / n - a =
      (F (Real.log n, κ) - a) - F (Real.log n, κ) * (2 / (y * B.F y)) * (m - B.mass) := by
    simp only [F, Real.exp_neg, Real.exp_log hn, div_eq_mul_inv]
    ring
  rw [heq]
  have hh := abs_sub_le (F (Real.log n, κ) - a) 0
    (F (Real.log n, κ) * (2 / (y * B.F y)) * (m - B.mass))
  simp only [sub_zero, zero_sub, abs_neg] at hh
  exact hh.trans_lt ((add_lt_add (hF.trans_le (min_le_left _ _)) hprod).trans_eq (by ring))

set_option maxHeartbeats 1600000 in
theorem exists_compact_prefix_normalization (B : Background) {s H dH A Y Z j D : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hY : B.inner < Y) (hYZ : Y ≤ Z) (hZ : Z < B.event) (hj : 0 < j) (hD : 0 < D)
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
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → T ≤ V →
        (∀ u v, Y ≤ x.1 u v 0) → U * Real.exp (B.outerRate * V) ≤ D →
        ∀ u : Icc 0 U, j ≤ (u : ℝ) * Real.exp (B.outerRate * V) →
          let v : Icc 0 V := ⟨V, hV, le_rfl⟩
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          x.1 u v 0 ≤ Z →
            |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F (x.1 u v 0)))| +
              |Real.log (B.z (x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (B.outerRate * V))))| +
                |x.2.1 u v 0 / ((u : ℝ) * ν u v) - B.outerRate| < ε := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let c := min s a / 2
  have hc0 : 0 < c := half_pos (lt_min hs ha)
  have hca : c < a := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  have hcs : c ≤ s := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (half_le_self hs.le)
  have hcHalf : c ≤ a / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let γ := min a (2 * c)
  have hγ : 0 < γ := lt_min ha (by positivity)
  have hY0 : 0 < Y := B.inner_pos.trans hY
  obtain ⟨U₀, Cm, hU₀, _hU₀r, _hCm, hfeedback⟩ := B.exists_bounded_width_feedback_decay
    hs hH hdH hdHR hA hY0 (by linarith only [hYZ, hZ, hdH]) hD.le hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  intro ε hε
  obtain ⟨η₀, hη₀, hspeed⟩ := B.exists_compact_arrival_speed_tolerance hY hZ (half_pos hε)
  let η := min η₀ (ε / 2)
  have hη : 0 < η := lt_min hη₀ (half_pos hε)
  obtain ⟨T₁, hT₁, hnorm⟩ := B.exists_prearrival_normalization
    hs hH hdH hdHR hA hY (hYZ.trans_lt hZ) hj hD hc hb hrc hrb hrd hrdec hOut η hη
  have hexp (b : ℝ) (hb : 0 < b) : Tendsto (fun t : ℝ => Real.exp (-b * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hb))
  have hwidth := (hexp a ha).const_mul D
  have hmass := (hexp γ hγ).const_mul Cm
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1
    ((hwidth.eventually_lt_const (by simpa only [mul_zero] using hU₀)).and
      (hmass.eventually_lt_const (by simpa only [mul_zero] using hη₀)))
  refine ⟨max T₁ T₂, hT₁.trans (le_max_left _ _), ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hVT hfloor hDwidth u hju
  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v
  let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
  intro hrZ
  have hvT₁ := (le_max_left _ _).trans hVT
  have hvT₂ := (le_max_right _ _).trans hVT
  have hUU : U ≤ U₀ := by
    have hh := mul_le_mul_of_nonneg_right hDwidth (Real.exp_pos (-a * V)).le
    change U * Real.exp (a * V) * Real.exp (-a * V) ≤ _ at hh
    have he : U ≤ D * Real.exp (-a * V) := by
      simpa only [mul_assoc, ← Real.exp_add, show a * V + -a * V = 0 by ring,
        Real.exp_zero, mul_one] using hh
    exact he.trans (hT₂ V hvT₂).1.le
  have hcp : c ≤ a * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le
    linarith only [hcHalf, hh, ha]
  have hm : |κ - 1| + |m - B.mass| < η₀ :=
    (hfeedback U V hU hV hUR p hp f hf x hx hfn hcp hUU hfloor hDwidth u).trans_lt (hT₂ V hvT₂).2
  have hu : 0 < (u : ℝ) := (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 (hj.trans_le hju)
  have hn : ν u v < 0 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1
  have hrband : x.1 u v 0 ∈ Icc Y Z := ⟨hfloor u v, hrZ⟩
  have hrpos : 0 < x.1 u v 0 := hY0.trans_le hrband.1
  have hF := B.F_neg ⟨hY.trans_le hrband.1, hrband.2.trans_lt hZ⟩
  let Q := a * ((u : ℝ) * ν u v / B.F (x.1 u v 0))
  have hQ : 0 < Q := mul_pos ha (div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hu hn) hF)
  have hlogs := (hnorm U V hU hV hUR p hp f hf x hx hfn u v hvT₁ hju
    ((mul_le_mul_of_nonneg_right u.property.2 (Real.exp_pos _).le).trans hDwidth)
    (fun q _ t _ => hfloor q t)).2
  have hlog : |Real.log Q| < η₀ :=
    ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt hlogs).trans_le (min_le_left _ _)
  have hsp := hspeed (x.1 u v 0) hrband Q κ m hQ hlog hm
  have he := (renormalizedMass_first_order (hx.choose u v) hn.ne
    (x.2.1 u v 0) (x.1 u v 2) B.charge B.cosmological).1
  change x.2.1 u v 0 = κ * horizonFunction (x.1 u v 0) m B.charge B.cosmological at he
  rw [horizonFunction_mass_difference] at he
  change x.2.1 u v 0 = κ * (B.F (x.1 u v 0) - 2 * (m - B.mass) / x.1 u v 0) at he
  have heq : x.2.1 u v 0 / ((u : ℝ) * ν u v) =
      a * κ * (1 - 2 * (m - B.mass) / (x.1 u v 0 * B.F (x.1 u v 0))) / Q := by
    rw [he]
    dsimp only [Q]
    field_simp [hu.ne', hn.ne, hF.ne, hrpos.ne', ha.ne']
  rw [← heq] at hsp
  exact (add_lt_add (hlogs.trans_le (min_le_right _ _)) hsp).trans_eq (by ring)

set_option maxHeartbeats 1600000 in
theorem exists_compact_band_normalization (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Z ≤ R →
        ∃ U₀ T : ℝ, ∃ τ σ : Ioi (0 : ℝ) → ℝ,
          0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ (∀ ε, T ≤ τ ε) ∧ (∀ W, T ≤ σ W) ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
            MemLp f p (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∃ gY gZ : ℝ → ℝ,
              ContinuousOn gY (Ici T) ∧ StrictAntiOn gY (Ici T) ∧ Tendsto gY atTop (𝓝 0) ∧
              ContinuousOn gZ (Ici T) ∧ StrictAntiOn gZ (Ici T) ∧ Tendsto gZ atTop (𝓝 0) ∧
              (∀ t ∈ Ici T, 0 < gY t ∧ 0 < gZ t) ∧
              (∀ (W : Ioi (0 : ℝ)) (t : ℝ), σ W ≤ t → gY t < W ∧ gZ t < W) ∧
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
                ∀ (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
                  (hx : IsWaveIntegral hU hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR hp hfU) x),
                  (∀ t ∈ Icc T V,
                    (gY t ≤ U → x.1 (projIcc 0 U hU (gY t)) (projIcc 0 V hV t) 0 = Y) ∧
                    (gZ t ≤ U → x.1 (projIcc 0 U hU (gZ t)) (projIcc 0 V hV t) 0 = Z)) ∧
                  (∀ v : Icc 0 V, T ≤ (v : ℝ) → gY v ≤ U → gZ v ≤ U →
                    ∀ y ∈ Icc Y Z, ∃! u : Icc 0 U,
                      gZ v ≤ (u : ℝ) ∧ (u : ℝ) ≤ gY v ∧ x.1 u v 0 = y) ∧
                  ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
                    gZ v ≤ (u : ℝ) → (u : ℝ) ≤ gY v →
                    let ν := radialNuField hV B.charge B.cosmological
                      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                    x.1 u v 0 ∈ Icc Y Z ∧ ∀ ε : Ioi (0 : ℝ), τ ε ≤ (v : ℝ) →
                      |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F (x.1 u v 0)))| +
                        |Real.log (B.z (x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (B.outerRate * v))))| +
                          |x.2.1 u v 0 / ((u : ℝ) * ν u v) - B.outerRate| < ε := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let c := min s a / 2
  have hc0 : 0 < c := half_pos (lt_min hs ha)
  have hca : c < a := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  have hcs : c ≤ s := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (half_le_self hs.le)
  have hcHalf : c ≤ a / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨δ, R, hδ, hδr, hR, _hRr, hdomain⟩ := B.exists_band_radiation_domain
    hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, ?_⟩
  intro Y Z hY hYZ hZR
  obtain ⟨UY, TY, _jY, DY, _ηY, _CY, _NY, _LY,
    hUY, hUYδ, hTY, _hjY, hDY, _hηY, _hCY, _hNY, _hLY, hsolveY⟩ := hdomain Y hY (hYZ.le.trans hZR)
  obtain ⟨UZ, TZ, jZ, DZ, _ηZ, _CZ, _NZ, _LZ,
    hUZ, _hUZδ, hTZ, hjZ, _hDZ, _hηZ, _hCZ, _hNZ, _hLZ, hsolveZ⟩ := hdomain Z (hY.trans hYZ) hZR
  have hnorm (ε : Ioi (0 : ℝ)) := B.exists_compact_prefix_normalization
    hs hH hdH hdHR hA hY hYZ.le (hZR.trans_lt hR.2) hjZ hDY hc hb hrc hrb hrd hrdec hOut ε ε.property
  choose τ₀ _hτ₀ hnorm using hnorm
  let T := max TY TZ
  have hzero : Tendsto (fun t : ℝ => max DY DZ * Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha))).const_mul (max DY DZ)
  have hentry (W : Ioi (0 : ℝ)) := eventually_atTop.1 (hzero.eventually_lt_const W.property)
  choose σ₀ hσ₀ using hentry
  let σ := fun W => max T (σ₀ W)
  refine ⟨min UY UZ, T, (fun ε => max T (τ₀ ε)), σ, lt_min hUY hUZ,
    (min_le_left _ _).trans hUYδ, hTY.trans_le (le_max_left _ _),
    (fun _ => le_max_left _ _), (fun _ => le_max_left _ _), ?_⟩
  intro p hp f hf hfn
  have hcp : c ≤ a * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le
    linarith only [hcHalf, hh, ha]
  obtain ⟨gY, hYc, hYa, hYl, _hYdc, _hYstart, hYpoint, hYphysical⟩ := hsolveY p hp f hf hfn hcp
  obtain ⟨gZ, hZc, hZa, hZl, _hZdc, _hZstart, hZpoint, hZphysical⟩ := hsolveZ p hp f hf hfn hcp
  have hsubY : Ici T ⊆ Ici TY := fun _ ht => (le_max_left TY TZ).trans ht
  have hsubZ : Ici T ⊆ Ici TZ := fun _ ht => (le_max_right TY TZ).trans ht
  refine ⟨gY, gZ, hYc.mono hsubY, hYa.mono hsubY, hYl,
    hZc.mono hsubZ, hZa.mono hsubZ, hZl,
    fun t ht => ⟨(hYpoint t (hsubY ht)).1.1, (hZpoint t (hsubZ ht)).1.1⟩, ?_, ?_⟩
  · intro W t ht
    have htT : T ≤ t := (le_max_left _ _).trans ht
    have hsmall := hσ₀ W t ((le_max_right _ _).trans ht)
    have hscale (g : ℝ) (hg : g * Real.exp (a * t) ≤ max DY DZ) : g < W := by
      have hh := mul_le_mul_of_nonneg_right hg (Real.exp_pos (-a * t)).le
      have he : g ≤ max DY DZ * Real.exp (-a * t) := by
        simpa only [mul_assoc, ← Real.exp_add, show a * t + -a * t = 0 by ring,
          Real.exp_zero, mul_one] using hh
      exact he.trans_lt hsmall
    exact ⟨hscale (gY t) ((hYpoint t (hsubY htT)).2.1.trans (le_max_left _ _)),
      hscale (gZ t) ((hZpoint t (hsubZ htT)).2.1.trans (le_max_right _ _))⟩
  intro U V hU hV hUR hUU hfU x hx
  have hphysY := hYphysical U V hU hV hUR (hUU.trans (min_le_left _ _)) hfU x hx
  have hphysZ := hZphysical U V hU hV hUR (hUU.trans (min_le_right _ _)) hfU x hx
  have hlevelY (t : ℝ) (ht : t ∈ Icc T V) (hgt : gY t ≤ U) := hphysY.2.1 t ⟨hsubY ht.1, ht.2⟩ hgt
  have hlevelZ (t : ℝ) (ht : t ∈ Icc T V) (hgt : gZ t ≤ U) := hphysZ.2.1 t ⟨hsubZ ht.1, ht.2⟩ hgt
  have hanti (v : Icc 0 V) := hx.radial_strictAnti hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hfU (horizonPhi h r 0)).1 v
    (fun q => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU q v).2.2.1)
  refine ⟨fun t ht => ⟨fun hgt => hlevelY t ht hgt, fun hgt => hlevelZ t ht hgt⟩, ?_, ?_⟩
  · intro v hv hYv hZv y hyz
    have hgY : gY v ∈ Icc 0 U := ⟨(hYpoint v (hsubY hv)).1.1.le, hYv⟩
    have hgZ : gZ v ∈ Icc 0 U := ⟨(hZpoint v (hsubZ hv)).1.1.le, hZv⟩
    have hrY := hlevelY v ⟨hv, v.property.2⟩ hYv
    have hrZ := hlevelZ v ⟨hv, v.property.2⟩ hZv
    simp only [intervalExtension_apply, projIcc_of_mem hU hgY, projIcc_of_mem hU hgZ,
      projIcc_of_mem hV v.property] at hrY hrZ
    change x.1 ⟨gY v, hgY⟩ v 0 = Y at hrY
    change x.1 ⟨gZ v, hgZ⟩ v 0 = Z at hrZ
    have horder : gZ v ≤ gY v := by
      by_contra hn
      have hh := hanti v (show (⟨gY v, hgY⟩ : Icc 0 U) < ⟨gZ v, hgZ⟩ from lt_of_not_ge hn)
      change x.1 ⟨gZ v, hgZ⟩ v 0 < x.1 ⟨gY v, hgY⟩ v 0 at hh
      rw [hrY, hrZ] at hh
      exact (not_lt_of_ge hYZ.le) hh
    have hcR : Continuous (fun t => intervalExtension hU x.1 t v 0) := by fun_prop
    have hyR : y ∈ Icc (intervalExtension hU x.1 (gY v) v 0)
        (intervalExtension hU x.1 (gZ v) v 0) := by
      simpa only [intervalExtension_apply, projIcc_of_mem hU hgY, projIcc_of_mem hU hgZ,
        hrY, hrZ] using hyz
    obtain ⟨q, hq, heq⟩ := intermediate_value_Icc' horder hcR.continuousOn hyR
    have hqU : q ∈ Icc 0 U := ⟨hgZ.1.trans hq.1, hq.2.trans hgY.2⟩
    have hhit : x.1 ⟨q, hqU⟩ v 0 = y := by
      simpa only [intervalExtension_apply, projIcc_of_mem hU hqU] using heq
    exact ⟨⟨q, hqU⟩, ⟨hq.1, hq.2, hhit⟩, fun w hw => (hanti v).injective (hw.2.2.trans hhit.symm)⟩
  intro u v hv hZu huY
  have hvY := hsubY hv
  have hvZ := hsubZ hv
  have hfloor (q : Icc 0 U) (hqu : q ≤ u) (w : Icc 0 V) (hwv : w ≤ v) : Y ≤ x.1 q w 0 := by
    have hh := hYa.antitoneOn (le_max_left TY (w : ℝ)) hvY (max_le hvY hwv)
    exact (hphysY.1 q w ((show (q : ℝ) ≤ u from hqu).trans (huY.trans hh))).1
  have hgZ : gZ v ∈ Icc 0 U := ⟨(hZpoint v hvZ).1.1.le, hZu.trans u.property.2⟩
  have hrZ : x.1 u v 0 ≤ Z := by
    have hh := (hanti v).antitone (show (⟨gZ v, hgZ⟩ : Icc 0 U) ≤ u from hZu)
    have hhit := hlevelZ v ⟨hv, v.property.2⟩ hgZ.2
    simp only [intervalExtension_apply, projIcc_of_mem hU hgZ, projIcc_of_mem hV v.property] at hhit
    exact hh.trans_eq hhit
  refine ⟨⟨hfloor u le_rfl v le_rfl, hrZ⟩, ?_⟩
  intro ε hεv
  let hf' := hfU.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
  let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (v : ℝ))
    le_rfl (by simpa only [zero_add] using u.property.2) le_rfl (by simpa only [zero_add] using v.property.2) x
  have hy := hx.horizon_prefix hU hV hUR u.property.1 v.property.1 u.property.2 v.property.2 hc hi hrc hr0 hp hfU
  let uu : Icc 0 (u : ℝ) := ⟨u, u.property.1, le_rfl⟩
  let vv : Icc 0 (v : ℝ) := ⟨v, v.property.1, le_rfl⟩
  have hyfloor (b t) : Y ≤ y.1 b t 0 := hfloor _
    (by change 0 + (b : ℝ) ≤ u; simpa only [zero_add] using b.property.2) _
    (by change 0 + (t : ℝ) ≤ v; simpa only [zero_add] using t.property.2)
  have hj := (hZpoint v hvZ).2.2.2.2.1.trans (mul_le_mul_of_nonneg_right hZu (Real.exp_pos _).le)
  have hD := (mul_le_mul_of_nonneg_right huY (Real.exp_pos _).le).trans (hYpoint v hvY).2.1
  have hnormf := (scalar_prefix_norm_le (u.property.2.trans (hUU.trans ((min_le_left _ _).trans hUYδ))) hf).trans hfn
  have he := hy.horizon_overlap u.property.1 v.property.1 (u.property.2.trans_lt hUR) hU hV hUR
    hc hi hrc hr0 hp hf' hfU hx uu.property u.property vv.property v.property
  have hne := hy.horizon_overlap_nu u.property.1 v.property.1 (u.property.2.trans_lt hUR) hU hV hUR
    hc hi hrc hr0 hp hf' hfU hx uu.property u.property vv.property v.property
  have hhit : y.1 uu vv 0 ≤ Z := by rw [he.1]; exact hrZ
  have hh := hnorm ε u v u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    p hp f hf' y hy hnormf ((le_max_right _ _).trans hεv) hyfloor hD uu hj hhit
  rw [he.1, he.2, hne] at hh
  exact hh

end CauchyHorizon.Background
