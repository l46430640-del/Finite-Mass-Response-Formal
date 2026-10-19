import CauchyHorizon.Characteristic.MatchingConformal
import CauchyHorizon.Characteristic.RadiusTransport
import CauchyHorizon.Radial.Band

/-! Uniform decay of the lapse and fixed-radius speed derivatives on bounded-width prefixes. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_compact_prefix_transport_decay (B : Background) {s H dH A Y Z D c : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hY : B.inner < Y) (hYZ : Y ≤ Z) (hZ : Z < B.event) (hD : 0 ≤ D)
    (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ C d T : ℝ, 0 < U₀ ∧ U₀ ≤ r 0 / 4 ∧ 0 ≤ C ∧ 0 < d ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) → U ≤ U₀ →
        (∀ u v, Y ≤ x.1 u v 0) → U * Real.exp (B.outerRate * V) ≤ D → T ≤ V →
        ∀ u : Icc 0 U,
          let v : Icc 0 V := ⟨V, hV, le_rfl⟩
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
          let K := horizonK (x.1 u v 0) (massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v)
            B.charge B.cosmological
          let Q := x.2.1 u v 2 - 2 * κ * K
          x.1 u v 0 ≤ Z → x.2.1 u v 0 ≤ -d ∧
            |Q| + |Q / x.2.1 u v 0 -
              (x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2)| ≤
                C * Real.exp (-(min B.outerRate (2 * c)) * V) := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have hY0 : 0 < Y := B.inner_pos.trans hY
  have hZ0 : 0 < Z := hY0.trans_le hYZ
  have hYR : Y ≤ B.event + dH := by linarith only [hYZ, hZ, hdH]
  obtain ⟨Ug, n, N, L, hUg, hUgr, _hn, hN, hL, hgeom⟩ := B.exists_bounded_width_geometry
    (D := D) hs hH hdH hdHR hA hY0 hYR hc hb hrc hrb hrd hrdec hOut
  obtain ⟨Um, Cm, hUm, _hUmr, hCm, hmass⟩ := B.exists_bounded_width_feedback_decay
    hs hH hdH hdHR hA hY0 hYR hD hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  obtain ⟨Ue, Ce, hUe, _hUer, hCe, hconf⟩ := B.exists_bounded_width_conformal_decay
    hs hH hdH hdHR hA hY0 hYR hD hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  obtain ⟨ε, q, hε, hq, hmargin⟩ := B.exists_band_margin hY hYZ hZ
  let d := q / 2
  have hd : 0 < d := half_pos hq
  let γ := min B.outerRate (2 * c)
  have hγ : 0 < γ := lt_min B.outerRate_pos (by positivity)
  have hKc : ContinuousOn (fun z : ℝ × ℝ => horizonK z.1 z.2 B.charge B.cosmological)
      (Icc Y Z ×ˢ Icc (B.mass - Cm) (B.mass + Cm)) := by
    intro z hz
    have hz0 : z.1 ≠ 0 := (hY0.trans_le hz.1.1).ne'
    unfold horizonK
    fun_prop (disch := positivity)
  obtain ⟨K₀, hKbound⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hKc
  let Km := max K₀ 0
  have hKm : 0 ≤ Km := le_max_right _ _
  let E := ((H + L * (r 0 / Y) * (A * max 1 D)) / Y) *
    Real.exp (L * N * D / (Y ^ 2 * (B.outerRate - c)))
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  let CQ := Ce + 2 * Cm * Km
  have hCQ : 0 ≤ CQ := by dsimp only [CQ]; positivity
  let C := CQ + CQ / d + Z * E ^ 2 / d ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hzero : Tendsto (fun t : ℝ => Cm * Real.exp (-γ * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hγ))).const_mul Cm
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hzero.eventually_lt_const (lt_min (by norm_num : (0 : ℝ) < 1 / 2) hε))
  refine ⟨min Ug (min Um Ue), C, d, max 0 T, lt_min hUg (lt_min hUm hUe),
    (min_le_left _ _).trans hUgr, hC, hd, le_max_left _ _, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcp hUU hfloor hwidth hTV u
  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v
  let K := horizonK (x.1 u v 0) m B.charge B.cosmological
  let Q := x.2.1 u v 2 - 2 * κ * K
  intro hrZ
  have hg := hgeom U V hU hV hUR p hp f hf x hx hfn (hUU.trans (min_le_left _ _)) hfloor hwidth
  have hm := hmass U V hU hV hUR p hp f hf x hx hfn hcp
    (hUU.trans ((min_le_right _ _).trans (min_le_left _ _))) hfloor hwidth u
  change |κ - 1| + |m - B.mass| ≤ Cm * Real.exp (-γ * V) at hm
  have he := hconf U V hU hV hUR p hp f hf x hx hfn hcp
    (hUU.trans ((min_le_right _ _).trans (min_le_right _ _))) hfloor hwidth u
  change |x.2.1 u v 2 - 2 * K| ≤ Ce * Real.exp (-γ * V) at he
  have hsmall := hm.trans_lt (hT V ((le_max_right _ _).trans hTV))
  have hκ : |κ - 1| ≤ Cm * Real.exp (-γ * V) := (le_add_of_nonneg_right (abs_nonneg _)).trans hm
  have hdm : |m - B.mass| ≤ Cm * Real.exp (-γ * V) := (le_add_of_nonneg_left (abs_nonneg _)).trans hm
  have hκlo : 1 / 2 ≤ κ := by
    have hh := (abs_lt.1 (((le_add_of_nonneg_right (abs_nonneg _)).trans_lt hsmall).trans_le (min_le_left _ _))).1
    linarith only [hh]
  have hmlo : B.mass - ε ≤ m := by
    have hh := (abs_lt.1 (((le_add_of_nonneg_left (abs_nonneg _)).trans_lt hsmall).trans_le (min_le_right _ _))).1
    linarith only [hh]
  have hmargin' := hmargin (x.1 u v 0) ⟨hfloor u v, hrZ⟩ m hmlo
  have hfo := (renormalizedMass_first_order (hx.choose u v)
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1.ne
    (x.2.1 u v 0) (x.1 u v 2) B.charge B.cosmological).1
  change x.2.1 u v 0 = κ * horizonFunction (x.1 u v 0) m B.charge B.cosmological at hfo
  have hl : x.2.1 u v 0 ≤ -d := by
    have hh := mul_le_mul_of_nonneg_left hmargin' (by linarith only [hκlo] : 0 ≤ κ)
    rw [← hfo] at hh
    dsimp only [d]
    nlinarith only [hh, hκlo, hq]
  have hlneg : x.2.1 u v 0 < 0 := hl.trans_lt (neg_neg_of_pos hd)
  have hK : |K| ≤ Km := by
    have hdm' := hdm.trans (mul_le_of_le_one_right hCm
      (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hγ.le) hV)))
    have hz : (x.1 u v 0, m) ∈ Icc Y Z ×ˢ Icc (B.mass - Cm) (B.mass + Cm) :=
      ⟨⟨hfloor u v, hrZ⟩, by constructor <;> linarith only [(abs_le.1 hdm').1, (abs_le.1 hdm').2]⟩
    have hh : |K| ≤ K₀ := by simpa only [Real.norm_eq_abs] using hKbound _ hz
    exact hh.trans (le_max_left _ _)
  have hQ : |Q| ≤ CQ * Real.exp (-γ * V) := by
    have htriangle := abs_sub_le (x.2.1 u v 2 - 2 * K) 0 (2 * (κ - 1) * K)
    rw [sub_zero, zero_sub, abs_neg, show x.2.1 u v 2 - 2 * K - 2 * (κ - 1) * K = Q by dsimp only [Q]; ring,
      abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htriangle
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hκ (by norm_num : (0 : ℝ) ≤ 2)) hK
      (abs_nonneg K) (by positivity)
    change |Q| ≤ (Ce + 2 * Cm * Km) * Real.exp (-γ * V)
    nlinarith only [htriangle, he, hh]
  have hnhi (w : Icc 0 U) (t : Icc 0 V) : |ν w t| ≤ N * Real.exp (B.outerRate * t) := by
    rw [abs_of_neg (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf w t).2.2.1]
    exact (hg w t).2.2.2
  have hout (t : Icc 0 V) : Real.exp (c * t) * |h t| ≤ H := by
    have hh := mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos (c * t)).le
    rw [Real.norm_eq_abs] at hh
    have he' : Real.exp (c * t) * Real.exp (-s * t) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith only [mul_nonneg (sub_nonneg.2 hcs) t.property.1]
    nlinarith only [hh, mul_le_mul_of_nonneg_left he' hH]
  have hscalar := (hx.horizon_weighted_scalar hU hV hUR hc hi hrc hr0 hφ hrd hp hf hA hfn
    hc0.le hca hcp hY0 hN.le hL hH hD hfloor hnhi (fun w t => (hg w t).2.1) hout hwidth).1 u v
  change |x.2.1 u v 1| ≤ E * Real.exp (-c * V) at hscalar
  have hinv : 1 / |x.2.1 u v 0| ≤ 1 / d := by
    apply one_div_le_one_div_of_le hd
    rw [abs_of_neg hlneg]
    linarith only [hl]
  have hfirst : |Q / x.2.1 u v 0| ≤ (CQ / d) * Real.exp (-γ * V) := by
    rw [abs_div, div_eq_mul_one_div]
    have hh := mul_le_mul hQ hinv (by positivity) (by positivity)
    exact hh.trans_eq (by ring)
  have hrpos : 0 < x.1 u v 0 := hY0.trans_le (hfloor u v)
  have hsecond : |(x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2)| ≤
      (Z * E ^ 2 / d ^ 2) * Real.exp (-γ * V) := by
    have hsq : (x.2.1 u v 1) ^ 2 ≤ E ^ 2 * Real.exp (-(2 * c) * V) := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hE (Real.exp_pos _).le)).2 hscalar
      rw [sq_abs, mul_pow, pow_two (Real.exp _), ← Real.exp_add,
        show -c * V + -c * V = -(2 * c) * V by ring] at hh
      exact hh
    have hinv2 := (sq_le_sq₀ (by positivity : 0 ≤ 1 / |x.2.1 u v 0|) (by positivity : 0 ≤ 1 / d)).2 hinv
    have hnum := mul_le_mul hrZ hsq (sq_nonneg _) (hrpos.le.trans hrZ)
    have hh := mul_le_mul hnum hinv2 (sq_nonneg _) (by positivity)
    have hexp := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      (neg_le_neg (min_le_right B.outerRate (2 * c))) hV)
    have htail := mul_le_mul_of_nonneg_left hexp
      (show 0 ≤ Z * E ^ 2 / d ^ 2 from by positivity)
    have heq : |(x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2)| =
        (x.1 u v 0 * (x.2.1 u v 1) ^ 2) * (1 / |x.2.1 u v 0|) ^ 2 := by
      rw [abs_of_nonneg (by positivity), div_pow, sq_abs]
      field_simp [hrpos.ne']
    rw [heq]
    apply hh.trans
    convert htail using 1
    ring
  refine ⟨hl, ?_⟩
  have hcv := abs_sub_le (Q / x.2.1 u v 0) 0
    ((x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * (x.2.1 u v 0) ^ 2))
  simp only [sub_zero, zero_sub, abs_neg] at hcv
  change |Q| + |_ - _| ≤ C * Real.exp (-γ * V)
  dsimp only [C]
  nlinarith only [hQ, hcv, hfirst, hsecond]

end CauchyHorizon.Background
