import CauchyHorizon.Characteristic.PrearrivalNormalization
import CauchyHorizon.Characteristic.BandArrival

/-! The actual arrival phase and its time Jacobian, with uniform data cutoffs. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

theorem exists_arrival_speed_tolerance (B : Background) (Y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ n κ m : ℝ, 0 < n → |Real.log n| < η →
      |κ - 1| + |m - B.mass| < η →
      |B.outerRate * κ * (1 - 2 * (m - B.mass) / (Y * B.F Y)) / n - B.outerRate| < ε := by
  let F := fun q : ℝ × ℝ × ℝ =>
    B.outerRate * q.2.1 * (1 - 2 * q.2.2 / (Y * B.F Y)) * Real.exp (-q.1)
  have hc : Continuous F := by fun_prop
  have hzero : |F (0, 1, 0) - B.outerRate| < ε := by
    simpa only [F, mul_zero, zero_div, sub_zero, mul_one, neg_zero, Real.exp_zero, sub_self, abs_zero] using hε
  obtain ⟨η, hη, hnear⟩ := Metric.mem_nhds_iff.1
    (((hc.continuousAt.tendsto.sub_const B.outerRate).abs).eventually_lt_const hzero)
  refine ⟨η, hη, ?_⟩
  intro n κ m hn hlog hm
  have hκ : |κ - 1| < η := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt hm
  have hmass : |m - B.mass| < η := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt hm
  have hh := hnear (show (Real.log n, κ, m - B.mass) ∈ Metric.ball (0, 1, 0) η by
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using
      And.intro hlog (And.intro hκ hmass))
  change |F (Real.log n, κ, m - B.mass) - B.outerRate| < ε at hh
  simpa only [F, Real.exp_neg, Real.exp_log hn, div_eq_mul_inv] using hh

set_option maxHeartbeats 1600000 in
theorem exists_arrival_phase_normalization (B : Background) {s H dH A : ℝ}
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
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧ R < r 0 ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ T : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
        0 < T ∧ (∀ ε, T ≤ τ ε) ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
          MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧ Tendsto g atTop (𝓝 0) ∧
            ∀ t ∈ Ici T, g t ∈ Ioo 0 δ ∧ DifferentiableAt ℝ g t ∧
              HasDerivAt (fun w => Real.log (B.z Y / (g w * (cν * Real.exp (B.outerRate * w)))))
                (-deriv g t / g t - B.outerRate) t ∧
              (∀ ε : Ioi (0 : ℝ), τ ε ≤ t →
                |Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t))))| +
                  |-deriv g t / g t - B.outerRate| < ε) ∧
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
                (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x),
                g t ≤ U → t ≤ V →
                  let u := projIcc 0 U hU (g t)
                  let v := projIcc 0 V hV t
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                  x.1 u v 0 = Y ∧ HasDerivAt g (-x.2.1 u v 0 / ν u v) t ∧
                  ∀ ε : Ioi (0 : ℝ), τ ε ≤ t →
                    |Real.log (B.outerRate * (g t * ν u v / B.F Y))| < ε := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  let a := B.outerRate
  let cν := Real.exp (∫ t in Ioi 0,
    2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - a)
  have ha : 0 < a := B.outerRate_pos
  have hcν : 0 < cν := Real.exp_pos _
  let c := min s a / 2
  have hc0 : 0 < c := half_pos (lt_min hs ha)
  have hca : c < a := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  have hcs : c ≤ s := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (half_le_self hs.le)
  have hcHalf : c ≤ a / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let γ := min a (2 * c)
  have hγ : 0 < γ := lt_min ha (by positivity)
  obtain ⟨δ, R, hδ, hδr, hR, hRr, harrival⟩ := B.exists_band_arrival
    hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, hRr, ?_⟩
  intro Y hY hYR
  have hYband : Y ∈ Ioo B.inner B.event := ⟨hY, hYR.trans_lt hR.2⟩
  have hY0 := B.inner_pos.trans hY
  have hF := B.F_neg hYband
  obtain ⟨ε₀, j, D, b, C, T, n, N, L, E, l, σ, Cm,
    hε₀, hεδ, hj, hD, _hb, _hC, hT, hn, _hN, _hL, _hE, _hl, hσ, hσε, _hCm, hsolve⟩ := harrival Y hY hYR
  have htol (ε : Ioi (0 : ℝ)) := B.exists_arrival_speed_tolerance Y (half_pos ε.property)
  choose η₀ hη₀ hspeed using htol
  let η := fun ε : Ioi (0 : ℝ) => min (η₀ ε) ((ε : ℝ) / 2)
  have hη (ε) : 0 < η ε := lt_min (hη₀ ε) (half_pos ε.property)
  have hnorm (ε : Ioi (0 : ℝ)) := B.exists_prearrival_normalization
    hs hH hdH hdHR hA hY hYband.2 hj hD hc hb hrc hrb hrd hrdec hOut (η ε) (hη ε)
  choose τ₀ _hτ₀ hnorm using hnorm
  have hmzero : Tendsto (fun t : ℝ => Cm * Real.exp (-γ * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hγ))).const_mul Cm
  have hmt (ε : Ioi (0 : ℝ)) := eventually_atTop.1 (hmzero.eventually_lt_const (hη ε))
  choose τm hτm using hmt
  let τ := fun ε => max T (max (τ₀ ε) (τm ε))
  refine ⟨T, τ, hT, fun _ => le_max_left _ _, ?_⟩
  intro p hp f hf hfn
  have hcp : c ≤ a * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le
    linarith only [hcHalf, hh, ha]
  obtain ⟨arrival, g, _hac, haa, _hal, haT, haσ, hgc, hga, hgl, hpoint, _hinv, hwitness⟩ :=
    hsolve p hp f hf hfn hcp
  have hsub : Ici T ⊆ Ioi (arrival (ε₀ / 2)) := fun _ ht => haT.trans_le ht
  refine ⟨g, hgc.mono hsub, hga.mono hsub, hgl, ?_⟩
  intro t ht
  have hpt := hpoint t (hsub ht)
  have hgt : g t ∈ Ioo 0 ε₀ := ⟨hpt.1.1, hpt.1.2.trans (half_lt_self hε₀)⟩
  obtain ⟨hat, _hj, _hD, _hb', _hC', W, Z, hW, hZ, hWR, hfW, z, hz, hgW, hatZ,
    hWε, _hfloor, hhit, _hlneg, hnlo, _hnhi, _hlam, _hlabs, _hk, _hscalar,
    hpre, _hda, _hjac, hgd, herr⟩ := hwitness (g t) hgt
  have hgtW : g t ∈ Icc 0 W := ⟨hgt.1.le, hgW.le⟩
  have htZ : t ∈ Icc 0 Z := ⟨hT.le.trans ht, hpt.2.1.symm.trans_le hatZ.le⟩
  let u : Icc 0 W := ⟨g t, hgtW⟩
  let v : Icc 0 Z := ⟨t, htZ⟩
  let ν := radialNuField hZ B.charge B.cosmological
    (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose
  let m := massField B.charge B.cosmological z.1 z.2.1 ν hz.choose u v
  let κ := -Real.exp (z.1 u v 2) / (4 * ν u v)
  have hdg := (hgd hpt.1.2).1.hasDerivAt
  have hveq : (⟨arrival (g t), hat.le, hatZ.le⟩ : Icc 0 Z) = v := Subtype.ext hpt.2.1
  rw [hveq] at hdg hnlo hhit hpre herr
  rw [hpt.2.1] at hdg herr
  change HasDerivAt g (-z.2.1 u v 0 / ν u v) t at hdg
  have hnneg : ν u v < 0 := by
    have hpos := mul_pos hn hj
    have hh : 0 < g t * (-ν u v) := hpos.trans_le hnlo
    exact neg_pos.1 ((mul_pos_iff_of_pos_left hgt.1).1 hh)
  have hgs : g t ≤ σ := by
    by_contra hnot
    have hh := haa.antitoneOn ⟨hσ, hσε.trans (half_lt_self hε₀)⟩ hgt (le_of_not_ge hnot)
    rw [hpt.2.1] at hh
    exact (not_lt_of_ge ht) (hh.trans_lt haσ)
  have hm : |κ - 1| + |m - B.mass| ≤ Cm * Real.exp (-γ * t) := herr hgs
  have hnormPoint (ε : Ioi (0 : ℝ)) (hεt : τ ε ≤ t) :
      |Real.log (a * (g t * ν u v / B.F Y))| +
        |Real.log (B.z Y / (g t * (cν * Real.exp (a * t))))| < η ε := by
    have ht₀ : τ₀ ε ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans hεt)
    have hh := (hnorm ε W Z hW hZ hWR p hp f hfW z hz
      ((scalar_prefix_norm_le (hWε.trans hεδ) hf).trans hfn) u v ht₀
      hpt.2.2.2.1 hpt.2.2.2.2.1 (fun q hq w hw => (hpre q hq w hw).1)).2
    rwa [hhit] at hh
  have hphase : HasDerivAt (fun w => Real.log (B.z Y / (g w * (cν * Real.exp (a * w)))))
      (-deriv g t / g t - a) t := by
    have hden := hpt.2.2.1.hasDerivAt.mul ((((hasDerivAt_id t).const_mul a).exp).const_mul cν)
    have hh := ((hasDerivAt_const t (B.z Y)).div hden
      (mul_pos hgt.1 (mul_pos hcν (Real.exp_pos _))).ne').log
      (div_pos (B.z_pos hYband) (mul_pos hgt.1 (mul_pos hcν (Real.exp_pos _)))).ne'
    apply hh.congr_deriv
    rw [← hpt.2.2.1.hasDerivAt.deriv]
    simp only [Pi.mul_apply, Pi.div_apply, id_eq]
    field_simp [hgt.1.ne', hcν.ne', (B.z_pos hYband).ne', Real.exp_ne_zero]
    ring
  refine ⟨⟨hgt.1, hgt.2.trans_le hεδ⟩, hdg.differentiableAt, hphase, ?_, ?_⟩
  · intro ε hεt
    have htm : τm ε ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans hεt)
    have hh := hnormPoint ε hεt
    let Q := a * (g t * ν u v / B.F Y)
    have hQ : 0 < Q := mul_pos ha (div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hgt.1 hnneg) hF)
    have hlog : |Real.log Q| < η₀ ε :=
      ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt hh).trans_le (min_le_left _ _)
    have hmη : |κ - 1| + |m - B.mass| < η₀ ε :=
      (hm.trans_lt (hτm ε t htm)).trans_le (min_le_left _ _)
    have hsp := hspeed ε Q κ m hQ hlog hmη
    have he := (renormalizedMass_first_order (hz.choose u v) hnneg.ne
      (z.2.1 u v 0) (z.1 u v 2) B.charge B.cosmological).1
    change z.2.1 u v 0 = κ * horizonFunction (z.1 u v 0) m B.charge B.cosmological at he
    rw [hhit, horizonFunction_mass_difference] at he
    change z.2.1 u v 0 = κ * (B.F Y - 2 * (m - B.mass) / Y) at he
    have heq : -deriv g t / g t = a * κ * (1 - 2 * (m - B.mass) / (Y * B.F Y)) / Q := by
      rw [hdg.deriv, he]
      dsimp only [Q]
      field_simp [hgt.1.ne', hnneg.ne, hF.ne, hY0.ne', ha.ne']
    rw [← heq] at hsp
    have hph := ((le_add_of_nonneg_left (abs_nonneg _)).trans_lt hh).trans_le (min_le_right _ _)
    exact add_lt_add hph hsp |>.trans_eq (by ring)
  · intro U V hU hV hUR hfU x hx hgtU htV
    have hgu : g t ∈ Icc 0 U := ⟨hgt.1.le, hgtU⟩
    have htv : t ∈ Icc 0 V := ⟨hT.le.trans ht, htV⟩
    have ho := hz.horizon_overlap hW hZ hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
      hgtW hgu htZ htv
    have hno := hz.horizon_overlap_nu hW hZ hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
      hgtW hgu htZ htv
    rw [projIcc_of_mem hU hgu, projIcc_of_mem hV htv]
    have hhit' : x.1 ⟨g t, hgu⟩ ⟨t, htv⟩ 0 = Y := by rw [← ho.1]; exact hhit
    refine ⟨hhit', ?_, ?_⟩
    · rw [ho.2, hno] at hdg
      exact hdg
    · intro ε hεt
      have hh := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt (hnormPoint ε hεt)
      rw [hno] at hh
      exact hh.trans_le ((min_le_right _ _).trans (half_le_self ε.property.le))

end CauchyHorizon.Background
