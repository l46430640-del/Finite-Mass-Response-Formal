import CauchyHorizon.Characteristic.ConformalBound
import CauchyHorizon.Characteristic.MatchingFeedback

/-! Uniform conformal error decay on actual prefixes of bounded exponential width. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_bounded_width_conformal_decay (B : Background) {s H dH A ρ D c : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hρ : 0 < ρ) (hρR : ρ ≤ B.event + dH) (hD : 0 ≤ D)
    (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ C : ℝ, 0 < U₀ ∧ U₀ ≤ r 0 / 4 ∧ 0 ≤ C ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → c ≤ B.outerRate * (1 - 1 / p.toReal) →
        U ≤ U₀ → (∀ u v, ρ ≤ x.1 u v 0) → U * Real.exp (B.outerRate * V) ≤ D → ∀ u : Icc 0 U,
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let v : Icc 0 V := ⟨V, hV, le_rfl⟩
          |x.2.1 u v 2 - 2 * horizonK (x.1 u v 0)
            (massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v) B.charge B.cosmological| ≤
              C * Real.exp (-(min B.outerRate (2 * c)) * V) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let R := B.event + dH
  have hR : 0 ≤ R := hρ.le.trans hρR
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  obtain ⟨U₁, n, N, L, hU₁, hU₁r, hn, hN, hL, hgeom⟩ :=
    B.exists_bounded_width_geometry (D := D) hs hH hdH hdHR hA hρ hρR hc hb hrc hrb hrd hrdec hOut
  obtain ⟨U₂, Cm, hU₂, _hU₂r, hCm, hmass⟩ :=
    B.exists_bounded_width_feedback_decay hs hH hdH hdHR hA hρ hρR hD hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  obtain ⟨C₀, D₀, hC₀, hD₀, hfeedback⟩ := exists_weighted_feedback_envelope hc hi hrc hr0 hφ hrd
    hc0 hca hρ hR hn hN.le hL hH hA hD
  obtain ⟨P, hP, hpot⟩ := radialPotential_bounded B.charge B.cosmological (R := R) hρ
  have hKc : ContinuousOn (fun z : ℝ × ℝ => horizonK z.1 z.2 B.charge B.cosmological)
      (Icc ρ R ×ˢ Icc (B.mass - Cm) (B.mass + Cm)) := by
    intro z hz
    have hz0 : z.1 ≠ 0 := (hρ.trans_le hz.1.1).ne'
    unfold horizonK
    fun_prop (disch := positivity)
  obtain ⟨K₀, hKbound⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hKc
  let Kmax := max K₀ 0
  let E := ((H + L * (r 0 / ρ) * (A * max 1 D)) / ρ) * Real.exp (L * N * D / (ρ ^ 2 * (B.outerRate - c)))
  let S := C₀ + D₀
  let Ck := 2 * Kmax + (4 * R * P) / ρ + 1
  let γ := min B.outerRate (2 * c)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hS : 0 ≤ S := add_nonneg hC₀ hD₀
  have hCk : 0 ≤ Ck := by dsimp only [Ck, Kmax]; positivity
  have hγ : 0 < γ := lt_min B.outerRate_pos (mul_pos (by norm_num) hc0)
  refine ⟨min U₁ U₂, Ck * S + E ^ 2 / ρ * R, lt_min hU₁ hU₂,
    (min_le_left _ _).trans hU₁r, by positivity, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb hUU hlo hwidth u
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v
  let K := horizonK (x.1 u v 0) m B.charge B.cosmological
  let Q := ∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
    (-intervalExtension hU ν t v)
  have hg := hgeom U V hU hV hUR p hp f hf x hx hfn (hUU.trans (min_le_left _ _)) hlo hwidth
  have hnhi (w : Icc 0 U) (t : Icc 0 V) : |ν w t| ≤ N * Real.exp (B.outerRate * t) := by
    rw [abs_of_neg (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf w t).2.2.1]
    exact (hg w t).2.2.2
  have hout (t : Icc 0 V) : Real.exp (c * t) * |h t| ≤ H := by
    have hh := mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos (c * t)).le
    rw [Real.norm_eq_abs] at hh
    have he : Real.exp (c * t) * Real.exp (-s * t) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith only [mul_nonneg (sub_nonneg.2 hcs) t.property.1]
    nlinarith only [hh, mul_le_mul_of_nonneg_left he hH]
  have he (z : ℝ) (hz : γ ≤ z) : Real.exp (-z * V) ≤ Real.exp (-γ * V) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hz) hV)
  have heg : Real.exp (-γ * V) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hγ.le) hV)
  have hm := hmass U V hU hV hUR p hp f hf x hx hfn hcb (hUU.trans (min_le_right _ _)) hlo hwidth u
  have hm' : |m - B.mass| ≤ Cm := by
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hm.trans (mul_le_of_le_one_right hCm heg))
  have hK : |K| ≤ Kmax := by
    have hz : (x.1 u v 0, m) ∈ Icc ρ R ×ˢ Icc (B.mass - Cm) (B.mass + Cm) :=
      ⟨⟨hlo u v, (hg u v).1⟩, by constructor <;> linarith only [(abs_le.1 hm').1, (abs_le.1 hm').2]⟩
    have hh : |K| ≤ K₀ := by simpa only [Real.norm_eq_abs] using hKbound _ hz
    exact hh.trans (le_max_left _ _)
  have henergy := (hfeedback U V hU hV hUR p hp f hf x hx hfn hcb hlo
    (fun w t => (hg w t).1) (fun w t => (hg w t).2.2.1) hnhi (fun w t => (hg w t).2.1) hout hwidth u).1
  have hQ : Q ≤ S * Real.exp (-γ * V) := by
    apply henergy.trans
    have hh := add_le_add (mul_le_mul_of_nonneg_left (he _ (min_le_left _ _)) hC₀)
      (mul_le_mul_of_nonneg_left (he _ (min_le_right _ _)) hD₀)
    simpa only [S, add_mul] using hh
  have hscalar := (hx.horizon_weighted_scalar hU hV hUR hc hi hrc hr0 hφ hrd hp hf hA hfn
    hc0.le hca hcb hρ hN.le hL hH hD hlo hnhi (fun w t => (hg w t).2.1) hout hwidth).1
  have hG (w : Icc 0 U) :
      |1 - B.charge ^ 2 / (x.1 w v 0) ^ 2 - B.cosmological * (x.1 w v 0) ^ 2| ≤ 4 * R * P := by
    have hrw : 0 < x.1 w v 0 := hρ.trans_le (hlo w v)
    have hid : 1 - B.charge ^ 2 / (x.1 w v 0) ^ 2 - B.cosmological * (x.1 w v 0) ^ 2 =
        (-4 * x.1 w v 0) * radialPotential (x.1 w v 0) B.charge B.cosmological := by
      unfold radialPotential
      field_simp [hrw.ne']
      ring
    rw [hid, abs_mul, abs_mul, abs_of_neg (by norm_num : (-4 : ℝ) < 0), neg_neg, abs_of_pos hrw]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hg w v).1 (by norm_num))
      (hpot _ ⟨hlo w v, (hg w v).1⟩) (abs_nonneg _) (by positivity)
  have hconf := hx.horizon_conformal_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf hρ v
    (fun w => hlo w v) hG (fun w => hscalar w v) u
  change |x.2.1 u v 2 - 2 * K| ≤ (2 * |K| + (4 * R * P) / ρ + 1) * Q +
    ((E * Real.exp (-c * V)) ^ 2 / ρ) * (r V - x.1 u v 0) at hconf
  have hcoef : 0 ≤ 2 * |K| + (4 * R * P) / ρ + 1 := by positivity
  have hmain : (2 * |K| + (4 * R * P) / ρ + 1) * Q ≤ Ck * S * Real.exp (-γ * V) := by
    calc
      _ ≤ (2 * |K| + (4 * R * P) / ρ + 1) * (S * Real.exp (-γ * V)) := mul_le_mul_of_nonneg_left hQ hcoef
      _ ≤ Ck * (S * Real.exp (-γ * V)) :=
        mul_le_mul_of_nonneg_right (by dsimp only [Ck]; linarith only [hK]) (by positivity)
      _ = _ := by ring
  have hrhi : r V ≤ R := by
    have hh := (hg ⟨0, le_rfl, hU⟩ v).1
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v] at hh
    exact hh
  have hrad : r V - x.1 u v 0 ≤ R := by linarith only [hrhi, hlo u v, hρ]
  have htail : ((E * Real.exp (-c * V)) ^ 2 / ρ) * (r V - x.1 u v 0) ≤
      (E ^ 2 / ρ * R) * Real.exp (-γ * V) := by
    have hid : (E * Real.exp (-c * V)) ^ 2 / ρ = (E ^ 2 / ρ) * Real.exp (-(2 * c) * V) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      rw [show -c * V + -c * V = -(2 * c) * V by ring]
      ring
    calc
      _ ≤ ((E * Real.exp (-c * V)) ^ 2 / ρ) * R := mul_le_mul_of_nonneg_left hrad (by positivity)
      _ = (E ^ 2 / ρ * R) * Real.exp (-(2 * c) * V) := by rw [hid]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (he _ (min_le_right _ _)) (by positivity)
  change |x.2.1 u v 2 - 2 * K| ≤ (Ck * S + E ^ 2 / ρ * R) * Real.exp (-γ * V)
  nlinarith only [hconf, hmain, htail]

end CauchyHorizon.Background
