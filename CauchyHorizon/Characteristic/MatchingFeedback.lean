import CauchyHorizon.Characteristic.BoundedWidthGeometry
import CauchyHorizon.Characteristic.WeightedScalar

/-! Quantitative mass and lapse errors on actual prefixes of bounded exponential width. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 1200000 in
theorem exists_bounded_width_feedback_decay (B : Background) {s H dH A ρ D c : ℝ}
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
          |(-Real.exp (x.1 u v 2) / (4 * ν u v)) - 1| +
            |massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v - B.mass| ≤
              C * Real.exp (-(min B.outerRate (2 * c)) * V) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let R := B.event + dH
  have hR : 0 ≤ R := hρ.le.trans hρR
  obtain ⟨U₀, n, N, L, hU₀, hU₀r, hn, hN, hL, hgeom⟩ :=
    B.exists_bounded_width_geometry (D := D) hs hH hdH hdHR hA hρ hρR hc hb hrc hrb hrd hrdec hOut
  obtain ⟨C₀, D₀, hC₀, hD₀, hfeedback⟩ := exists_weighted_feedback_envelope hc hi hrc hr0 hφ hrd
    hc0 hca hρ hR hn hN.le hL hH hA hD
  let S := C₀ + D₀
  let P := R * L / 2
  let F := H ^ 2 / (4 * s)
  let γ := min B.outerRate (2 * c)
  have hS : 0 ≤ S := add_nonneg hC₀ hD₀
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hγ : 0 < γ := lt_min B.outerRate_pos (mul_pos (by norm_num) hc0)
  refine ⟨U₀, (1 + P * Real.exp S) * S + F, hU₀, hU₀r, by positivity, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb hUU hlo hwidth u
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
  let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v
  let Q := C₀ * Real.exp (-B.outerRate * V) + D₀ * Real.exp (-(2 * c) * V)
  have hg := hgeom U V hU hV hUR p hp f hf x hx hfn hUU hlo hwidth
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
  obtain ⟨_henergy, hk, hm⟩ := hfeedback U V hU hV hUR p hp f hf x hx hfn hcb hlo
    (fun w t => (hg w t).1) (fun w t => (hg w t).2.2.1) hnhi (fun w t => (hg w t).2.1) hout hwidth u
  change Real.exp (-Q) ≤ κ at hk
  change |m - horizonMass B.mass h V| ≤ P * (Real.exp Q - 1) at hm
  have he (z : ℝ) (hz : γ ≤ z) : Real.exp (-z * V) ≤ Real.exp (-γ * V) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hz) hV)
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  have hQ : Q ≤ S * Real.exp (-γ * V) := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left (he _ (min_le_left _ _)) hC₀)
      (mul_le_mul_of_nonneg_left (he _ (min_le_right _ _)) hD₀)
    simpa only [Q, S, add_mul] using hh
  have hQS : Q ≤ S := hQ.trans (mul_le_of_le_one_right hS
    (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hγ.le) hV)))
  have hexp : Real.exp Q - 1 ≤ Real.exp S * Q := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-Q)) (Real.exp_pos Q).le
    have hmul : Real.exp Q * Real.exp (-Q) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [hmul] at hh
    have hb := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hQS) hQ0
    nlinarith only [hh, hb]
  have hκ1 : κ ≤ 1 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.2.2
  have hκ : |κ - 1| ≤ Q := by
    rw [abs_of_nonpos (sub_nonpos.2 hκ1)]
    have hh := Real.add_one_le_exp (-Q)
    linarith only [hk, hh]
  have hhm : |horizonMass B.mass h V - B.mass| ≤ F * Real.exp (-(2 * s) * V) := by
    obtain ⟨hm0, hmb⟩ := horizonMass_bounds hs hH hb B.mass V
    rw [abs_sub_comm, abs_of_nonneg hm0]
    exact hmb
  have hhm' : |horizonMass B.mass h V - B.mass| ≤ F * Real.exp (-γ * V) :=
    hhm.trans (mul_le_mul_of_nonneg_left (he _ ((min_le_right _ _).trans (by linarith only [hcs]))) hF)
  have hm' : |m - B.mass| ≤ P * (Real.exp S * Q) + F * Real.exp (-γ * V) := by
    calc
      _ = |(m - horizonMass B.mass h V) + (horizonMass B.mass h V - B.mass)| := by congr 1; ring
      _ ≤ |m - horizonMass B.mass h V| + |horizonMass B.mass h V - B.mass| := abs_add_le _ _
      _ ≤ _ := add_le_add (hm.trans (mul_le_mul_of_nonneg_left hexp hP)) hhm'
  change |κ - 1| + |m - B.mass| ≤ ((1 + P * Real.exp S) * S + F) * Real.exp (-γ * V)
  have hh := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 1 + P * Real.exp S)
  nlinarith only [hκ, hm', hh]

end CauchyHorizon.Background
