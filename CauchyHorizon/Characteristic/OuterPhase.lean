import CauchyHorizon.Characteristic.ArrivalPhase

/-! Exact normalization on the late near-event family, including its past radius floor. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_thin_prefix_normalization (B : Background) {s H dH A : ℝ}
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
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ r 0 / 4 ∧
      ∀ j ε : ℝ, 0 < j → 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
          (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x),
          (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
          U * Real.exp (B.outerRate * V) ≤ δ₀ →
          ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
            j ≤ (u : ℝ) * Real.exp (B.outerRate * v) →
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
            x.1 u v 0 ∈ Ioo B.inner B.event ∧
              |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F (x.1 u v 0)))| +
                |Real.log (B.z (x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (B.outerRate * v))))| +
                (|(-Real.exp (x.1 u v 2) / (4 * ν u v)) - 1| +
                  |massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v - B.mass|) < ε := by
  intro hi hr0 cν
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let c := min s a / 2
  have hc0 : 0 < c := half_pos (lt_min hs ha)
  have hca : c < a := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  have hcs : c ≤ s := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (half_le_self hs.le)
  have hcHalf : c ≤ a / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hcp (p : ℝ≥0∞) (hp : 4 ≤ p) : c ≤ a * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le
    linarith only [hcHalf, hh, ha]
  have hrmono : MonotoneOn r (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t =>
      horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (convex_Ici _) hrc.continuousOn
    · intro t ht
      exact (hrd t (interior_subset ht)).mono interior_subset
    · intro t ht
      exact (hOut.2.2.2.2.1 t (interior_subset ht)).le
  let ρ := (B.inner + min (r 0) B.event) / 2
  have hρi : B.inner < ρ := by
    have hh := lt_min hrinit B.inner_lt_event
    dsimp only [ρ]
    linarith only [hh]
  have hρr : ρ < r 0 := by
    have hh := min_le_left (r 0) B.event
    dsimp only [ρ] at *
    linarith only [hh, hrinit]
  have hρe : ρ < B.event := by
    have hh := min_le_right (r 0) B.event
    dsimp only [ρ] at *
    linarith only [hh, B.inner_lt_event]
  have hρ : 0 < ρ := B.inner_pos.trans hρi
  obtain ⟨D, n, N, L, q, K, T₀, hD, hDr, _hn, hN, _hL, _hq, _hK, _hT₀, hsolve⟩ :=
    B.exists_outer_flux_prefix hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0.le hca hcs hA
  obtain ⟨U₀, C, hU₀, _hU₀r, _hC, hfeedback⟩ := B.exists_bounded_width_feedback_decay
    hs hH hdH hdHR hA hρ (by linarith only [hρe, hdH]) hD.le hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  let δ₀ := min D (min U₀ ((r 0 - ρ) / N))
  have hδ₀ : 0 < δ₀ := lt_min hD (lt_min hU₀ (div_pos (sub_pos.2 hρr) hN))
  have hδD : δ₀ ≤ D := min_le_left _ _
  have hδU : δ₀ ≤ U₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδN : N * δ₀ ≤ r 0 - ρ := by
    have hh := (le_div_iff₀ hN).1
      (show δ₀ ≤ (r 0 - ρ) / N from (min_le_right _ _).trans (min_le_right _ _))
    simpa only [mul_comm] using hh
  refine ⟨δ₀, hδ₀, hδD.trans hDr, ?_⟩
  intro j ε hj hε
  obtain ⟨T₁, hT₁, hnorm⟩ := B.exists_prearrival_normalization hs hH hdH hdHR hA
    hρi hρe hj hD hc hb hrc hrb hrd hrdec hOut (ε / 2) (half_pos hε)
  let γ := min a (2 * c)
  have hγ : 0 < γ := lt_min ha (by positivity)
  have he : Tendsto (fun t : ℝ => C * Real.exp (-γ * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hγ))).const_mul C
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 (he.eventually_lt_const (half_pos hε))
  refine ⟨max T₁ T₂, hT₁.trans (le_max_left _ _), ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hwidth u v hv hju
  have hwD : U * Real.exp (a * V) ≤ D := hwidth.trans hδD
  have hUU : U ≤ U₀ := (le_mul_of_one_le_right hU
    (Real.one_le_exp_iff.2 (mul_nonneg ha.le hV))).trans (hwidth.trans hδU)
  obtain ⟨y, ⟨hy, hg⟩, _⟩ := hsolve U V hU hV hUR p hp f hf hfn (hcp p hp) hwD
  have hyx : y = x := hy.incoming_unique hU hV hUR hp hf hx
  subst y
  have hfloor (b : Icc 0 U) (t : Icc 0 V) : ρ ≤ x.1 b t 0 := by
    have hh := (hg b t).2.2.2.2.2.2.1
    have ht := hrmono (show (0 : ℝ) ∈ Ici (0 : ℝ) by simp) t.property.1 t.property.1
    have hw : (b : ℝ) * Real.exp (a * t) ≤ δ₀ :=
      (mul_le_mul b.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left t.property.2 ha.le))
        (Real.exp_pos _).le hU).trans hwidth
    have hbN := (mul_le_mul_of_nonneg_left hw hN.le).trans hδN
    nlinarith only [hh, ht, hbN]
  have huv : (u : ℝ) * Real.exp (a * v) ≤ D :=
    (mul_le_mul u.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 ha.le))
      (Real.exp_pos _).le hU).trans hwD
  have hn := hnorm U V hU hV hUR p hp f hf x hx hfn u v
    ((le_max_left _ _).trans hv) hju huv (fun b _ t _ => hfloor b t)
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let z := waveTranslate (a := 0) (U := U) (b := 0) (V := (v : ℝ))
    le_rfl (by simp only [zero_add, le_refl]) le_rfl (by simpa only [zero_add] using v.property.2) x
  have hz := hx.horizon_prefix hU hV hUR hU v.property.1 le_rfl v.property.2 hc hi hrc hr0 hp hf
  have hzfloor (b t) : ρ ≤ z.1 b t 0 := hfloor _ _
  have hwv : U * Real.exp (a * v) ≤ D :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 ha.le)) hU).trans hwD
  have hm := hfeedback U v hU v.property.1 hUR p hp f hf z hz hfn (hcp p hp) hUU hzfloor hwv u
  have ho := hz.horizon_overlap hU v.property.1 hUR hU hV hUR hc hi hrc hr0 hp hf hf hx
    u.property u.property (show (v : ℝ) ∈ Icc 0 (v : ℝ) from ⟨v.property.1, le_rfl⟩) v.property
  have hno := hz.horizon_overlap_nu hU v.property.1 hUR hU hV hUR hc hi hrc hr0 hp hf hf hx
    u.property u.property (show (v : ℝ) ∈ Icc 0 (v : ℝ) from ⟨v.property.1, le_rfl⟩) v.property
  simp only [massField_apply] at hm
  rw [ho.1, ho.2, hno] at hm
  exact ⟨hn.1, (add_lt_add hn.2 (hm.trans_lt (hT₂ v ((le_max_right _ _).trans hv)))).trans_eq (by ring)⟩

set_option maxHeartbeats 1600000 in
theorem exists_outer_phase_family (B : Background) {s H dH A : ℝ}
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
    ∃ δ₀ α β η : ℝ, 0 < δ₀ ∧ δ₀ ≤ r 0 / 4 ∧ 0 < α ∧ 0 < β ∧ 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ Y T : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
        Y = B.event - α * δ ∧ Y ∈ Ioo B.inner B.event ∧ 0 < T ∧ (∀ ε, T ≤ τ ε) ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
          MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧ Tendsto g atTop (𝓝 0) ∧
            ∀ t ∈ Ici T, g t ∈ Ioo 0 δ ∧ DifferentiableAt ℝ g t ∧
              β * δ ≤ g t * Real.exp (B.outerRate * t) ∧
              g t * Real.exp (B.outerRate * t) ≤ 3 * δ / 16 ∧ η ≤ -deriv g t / g t ∧
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
                  x.1 u v 0 = Y ∧ HasDerivAt g (-x.2.1 u v 0 / ν u v) t := by
  intro hi hr0 cν
  have ha : 0 < B.outerRate := B.outerRate_pos
  have hcν : 0 < cν := Real.exp_pos _
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δn, hδn, _hδnr, hnorm⟩ := B.exists_thin_prefix_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δg, α, β, η, hδg, hδgr, hα, hβ, hη, hfamily⟩ :=
    B.exists_outer_arrival_family hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut
      (c := 0) le_rfl ha hs.le hA
  refine ⟨min δn δg, α, β, η, lt_min hδn hδg, (min_le_right _ _).trans hδgr, hα, hβ, hη, ?_⟩
  intro δ hδ hδcap
  have hδδn := hδcap.trans (min_le_left _ _)
  have hδδg := hδcap.trans (min_le_right _ _)
  obtain ⟨Y, T₀, j, J, b, C, ε₀, hYeq, hjeq, hJeq, hηb, hY, hT₀, hj, _hJ, _hJδ,
    _hb, _hC, _hε₀, harrival⟩ := hfamily δ hδ hδδg
  have htol (ε : Ioi (0 : ℝ)) := B.exists_arrival_speed_tolerance Y (half_pos ε.property)
  choose θ hθ hspeed using htol
  let ζ := fun ε : Ioi (0 : ℝ) => min (θ ε) ((ε : ℝ) / 2)
  have hζ (ε) : 0 < ζ ε := lt_min (hθ ε) (half_pos ε.property)
  have hnt (ε : Ioi (0 : ℝ)) := hnorm j (ζ ε) hj (hζ ε)
  choose τ₀ _hτ₀ hnt using hnt
  let T := T₀ + 1
  have hT : 0 < T := by dsimp only [T]; linarith only [hT₀]
  let τ := fun ε => max T (τ₀ ε)
  refine ⟨Y, T, τ, hYeq, hY, hT, fun _ => le_max_left _ _, ?_⟩
  intro p hp f hf hfn
  have hcp : 0 ≤ B.outerRate * (1 - 1 / p.toReal) :=
    mul_nonneg ha.le (by linarith only [(incoming_exponent_bounds hp).1])
  obtain ⟨g, inv, hgc, hga, hgl, _hic, _hil, _higi, _higg, hpoint⟩ := harrival p hp f hf hfn hcp
  have hsub : Ici T ⊆ Ioi T₀ := fun _ ht => (lt_add_one T₀).trans_le ht
  refine ⟨g, hgc.mono hsub, hga.mono hsub, hgl, ?_⟩
  intro t ht
  obtain ⟨hgt, hjg, hJg, hbg, _hCg, W, Z, hW, hZ, hWR, hfW, z, hz, u, v,
    hueq, hveq, huin, hvin, hhit, hwidth, hdg, _hjac⟩ := hpoint t (hsub ht)
  let ν := radialNuField hZ B.charge B.cosmological
    (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose
  let m := massField B.charge B.cosmological z.1 z.2.1 ν hz.choose u v
  let κ := -Real.exp (z.1 u v 2) / (4 * ν u v)
  change HasDerivAt g (-z.2.1 u v 0 / ν u v) t at hdg
  have ht0 : 0 ≤ t := hT.le.trans ht
  have hWδ : W ≤ δ := (le_mul_of_one_le_right hW
    (Real.one_le_exp_iff.2 (mul_nonneg ha.le hZ))).trans_eq hwidth
  have hgδ : g t < δ := by
    have hh := le_mul_of_one_le_right hgt.le (Real.one_le_exp_iff.2 (mul_nonneg ha.le ht0))
    rw [hJeq] at hJg
    exact (hh.trans hJg).trans_lt (by linarith only [hδ])
  have hnneg : ν u v < 0 := (hz.interior_gauge hW hZ hWR hc hi hrc hr0 hφ hrd hp hfW u v).2.2.1
  have hphase : HasDerivAt (fun w => Real.log (B.z Y / (g w * (cν * Real.exp (B.outerRate * w)))))
      (-deriv g t / g t - B.outerRate) t := by
    have hden := hdg.mul ((((hasDerivAt_id t).const_mul B.outerRate).exp).const_mul cν)
    have hh := ((hasDerivAt_const t (B.z Y)).div hden
      (mul_pos hgt (mul_pos hcν (Real.exp_pos _))).ne').log
      (div_pos (B.z_pos hY) (mul_pos hgt (mul_pos hcν (Real.exp_pos _)))).ne'
    apply hh.congr_deriv
    rw [hdg.deriv]
    simp only [Pi.mul_apply, Pi.div_apply, id_eq]
    field_simp [hgt.ne', hcν.ne', (B.z_pos hY).ne', Real.exp_ne_zero]
    ring
  refine ⟨⟨hgt, hgδ⟩, hdg.differentiableAt, hjeq ▸ hjg, hJeq ▸ hJg, hηb.trans hbg,
    hphase, ?_, ?_⟩
  · intro ε hεt
    have hh := (hnt ε W Z hW hZ hWR p hp f hfW z hz
      ((scalar_prefix_norm_le hWδ hf).trans hfn) (hwidth.le.trans hδδn) u v
      (by rw [hveq]; exact (le_max_right _ _).trans hεt) (by rw [hueq, hveq]; exact hjg)).2
    change |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F (z.1 u v 0)))| +
      |Real.log (B.z (z.1 u v 0) / ((u : ℝ) * (cν * Real.exp (B.outerRate * v))))| +
      (|κ - 1| + |m - B.mass|) < ζ ε at hh
    rw [hhit, hueq, hveq] at hh
    let Q := B.outerRate * (g t * ν u v / B.F Y)
    have hQ : 0 < Q := mul_pos ha
      (div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hgt hnneg) (B.F_neg hY))
    have hlog : |Real.log Q| < θ ε := by
      have hh' := hh.trans_le (min_le_left _ _)
      dsimp only [Q]
      linarith only [hh', abs_nonneg (Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t))))),
        abs_nonneg (κ - 1), abs_nonneg (m - B.mass)]
    have hm : |κ - 1| + |m - B.mass| < θ ε := by
      have hh' := hh.trans_le (min_le_left _ _)
      linarith only [hh', abs_nonneg (Real.log Q),
        abs_nonneg (Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t)))))]
    have hph : |Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t))))| < (ε : ℝ) / 2 := by
      have hh' := hh.trans_le (min_le_right _ _)
      linarith only [hh', abs_nonneg (Real.log Q), abs_nonneg (κ - 1), abs_nonneg (m - B.mass)]
    have hsp := hspeed ε Q κ m hQ hlog hm
    have he := (renormalizedMass_first_order (hz.choose u v) hnneg.ne
      (z.2.1 u v 0) (z.1 u v 2) B.charge B.cosmological).1
    change z.2.1 u v 0 = κ * horizonFunction (z.1 u v 0) m B.charge B.cosmological at he
    rw [hhit, horizonFunction_mass_difference] at he
    change z.2.1 u v 0 = κ * (B.F Y - 2 * (m - B.mass) / Y) at he
    have heq : -deriv g t / g t =
        B.outerRate * κ * (1 - 2 * (m - B.mass) / (Y * B.F Y)) / Q := by
      rw [hdg.deriv, he]
      dsimp only [Q]
      field_simp [hgt.ne', hnneg.ne, (B.F_neg hY).ne, (B.inner_pos.trans hY.1).ne', ha.ne']
    rw [← heq] at hsp
    exact (add_lt_add hph hsp).trans_eq (by ring)
  · intro U V hU hV hUR hfU x hx hgtU htV
    have hgu : g t ∈ Icc 0 U := ⟨hgt.le, hgtU⟩
    have htv : t ∈ Icc 0 V := ⟨ht0, htV⟩
    have hguW : g t ∈ Icc 0 W := hueq ▸ u.property
    have htvZ : t ∈ Icc 0 Z := hveq ▸ v.property
    have ho := hz.horizon_overlap hW hZ hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
      hguW hgu htvZ htv
    have hno := hz.horizon_overlap_nu hW hZ hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
      hguW hgu htvZ htv
    have hu' : (⟨g t, hguW⟩ : Icc 0 W) = u := Subtype.ext hueq.symm
    have hv' : (⟨t, htvZ⟩ : Icc 0 Z) = v := Subtype.ext hveq.symm
    rw [hu', hv'] at ho hno
    rw [projIcc_of_mem hU hgu, projIcc_of_mem hV htv]
    refine ⟨by rw [← ho.1]; exact hhit, ?_⟩
    change HasDerivAt g (-z.2.1 u v 0 / ν u v) t at hdg
    change radialNuField hZ B.charge B.cosmological
      (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose u v = _ at hno
    change HasDerivAt g (-z.2.1 u v 0 /
      radialNuField hZ B.charge B.cosmological
        (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose u v) t at hdg
    rw [ho.2, hno] at hdg
    exact hdg

end CauchyHorizon.Background
