import CauchyHorizon.Characteristic.BandPassage

/-! A positive arrival scale puts every sufficiently small ray at a strictly trapped level. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 1000000 in
theorem exists_band_crossing (B : Background) {s H dH A c : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧ R < r 0 ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ U₀ j D n N L E τ : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ U₀ ≤ 1 ∧ U₀ < r 0 ∧ 0 < j ∧ 0 < D ∧
        0 < n ∧ 0 < N ∧ 0 ≤ L ∧ 0 ≤ E ∧ 0 < τ ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A → c ≤ B.outerRate * (1 - 1 / p.toReal) →
          ∀ (U : ℝ) (hU : 0 < U) (hUR : U < r 0) (hfU : MemLp f p (volume.restrict (Icc 0 U))),
            U ≤ U₀ → ∃ T : ℝ, ∃ hT : 0 < T, ∃ x : WaveState U T,
              ∃ hx : IsWaveIntegral hU.le hT.le B.charge B.cosmological
                (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x,
              let ν := radialNuField hT.le B.charge B.cosmological
                (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
              let uU : Icc 0 U := ⟨U, hU.le, le_rfl⟩
              let vT : Icc 0 T := ⟨T, hT.le, le_rfl⟩
              (∀ u v, Y ≤ x.1 u v 0) ∧ x.1 uU vT 0 = Y ∧
              (∀ (u : Icc 0 U) (v : Icc 0 T), (v : ℝ) < T → Y < x.1 u v 0) ∧
              j ≤ U * Real.exp (B.outerRate * T) ∧ U * Real.exp (B.outerRate * T) ≤ D ∧
              n * j ≤ U * (-ν uU vT) ∧ U * (-ν uU vT) ≤ N * D ∧ τ ≤ -x.2.1 uU vT 0 ∧
              (∀ u v, x.1 u v 0 ≤ B.event + dH ∧ |x.2.1 u v 0| ≤ L ∧
                n * Real.exp (B.outerRate * v) ≤ -ν u v ∧ -ν u v ≤ N * Real.exp (B.outerRate * v) ∧
                (3 / 4 : ℝ) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧ |x.2.1 u v 1| ≤ E * Real.exp (-c * v)) ∧
              (∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 T,
                |x.2.2 u v 1| ≤ (r 0 / Y) * |f u| + (N / (Y * (B.outerRate - c))) * E * Real.exp ((B.outerRate - c) * v)) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have hrmono : MonotoneOn r (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t =>
      horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (convex_Ici _) hrc.continuousOn
    · intro t ht
      exact (hrd t (interior_subset ht)).mono interior_subset
    · intro t ht
      exact (hOut.2.2.2.2.1 t (interior_subset ht)).le
  obtain ⟨δ, R, hδ, hδr, hR, hRr, hpass⟩ :=
    B.exists_band_passage hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, hRr, ?_⟩
  intro Y hY hYR
  have hYr : Y < r 0 := hYR.trans_lt hRr
  obtain ⟨U₁, D, n, N, L, E, hU₁, hU₁δ, hU₁1, hU₁r, hD, hn, hN, hL, hE, hsolve⟩ := hpass Y hY hYR
  obtain ⟨U₂, T₀, q, _P, hU₂, _hU₂r, _hT₀, hq, _hP, hlate⟩ :=
    B.exists_late_band_geometry hY hYR hR.2 hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  let j := (r 0 - Y) / N
  have hj : 0 < j := div_pos (sub_pos.2 hYr) hN
  let U₀ := min U₁ (min U₂ (j * Real.exp (-B.outerRate * T₀) / 2))
  have hU₀ : 0 < U₀ := by dsimp only [U₀]; positivity
  have hU₀U₁ : U₀ ≤ U₁ := min_le_left _ _
  have hU₀U₂ : U₀ ≤ U₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hU₀T : U₀ ≤ j * Real.exp (-B.outerRate * T₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨U₀, j, D, n, N, L, E, (3 / 4) * q, hU₀, hU₀U₁.trans hU₁δ,
    hU₀U₁.trans hU₁1, hU₀U₁.trans_lt hU₁r, hj, hD, hn, hN, hL, hE, by positivity, ?_⟩
  intro p hp f hf hfn hcb U hU hUR hfU hUU
  obtain ⟨T, hT, x, hx, hlo, hhit, hbefore, hw, hg, hscalar⟩ :=
    hsolve p hp f hf hfn hcb U hU hUR hfU (hUU.trans hU₀U₁)
  let ν := radialNuField hT.le B.charge B.cosmological
    (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
  let uU : Icc 0 U := ⟨U, hU.le, le_rfl⟩
  let vT : Icc 0 T := ⟨T, hT.le, le_rfl⟩
  have hν (u : Icc 0 U) (v : Icc 0 T) : ν u v < 0 :=
    (hx.interior_gauge hU.le hT.le hUR hc hi hrc hr0 hφ hrd hp hfU u v).2.2.1
  have hnu (u : Icc 0 U) (v : Icc 0 T) : |ν u v| ≤ N * Real.exp (B.outerRate * v) := by
    rw [abs_of_neg (hν u v)]
    exact (hg u v).2.2.2.1
  have hgap := (hx.radial_gap_weighted_bound hx.choose rfl
    (incomingWave_constraint_data hU.le hUR hp hfU (horizonPhi h r 0)).1
    (fun u v => (hν u v).le) hnu uU vT).2
  rw [(hx.horizon_traces hU.le hT.le hUR hc hi hrc hr0 hφ hrd hp hfU).2 vT, hhit] at hgap
  change r T - Y ≤ N * U * Real.exp (B.outerRate * T) at hgap
  have hlower : j ≤ U * Real.exp (B.outerRate * T) := by
    apply (div_le_iff₀ hN).2
    have hrT := hrmono (show (0 : ℝ) ∈ Ici 0 by simp) hT.le hT.le
    nlinarith only [hgap, hrT]
  have hlateT : T₀ ≤ T := by
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (hUU.trans hU₀T) (Real.exp_pos (B.outerRate * T₀)).le
    have he : Real.exp (-B.outerRate * T₀) * Real.exp (B.outerRate * T₀) = 1 := by
      rw [← Real.exp_add, show -B.outerRate * T₀ + B.outerRate * T₀ = 0 by ring, Real.exp_zero]
    have hsmall : U * Real.exp (B.outerRate * T₀) ≤ j / 2 := by
      apply hmul.trans_eq
      calc
        _ = (j / 2) * (Real.exp (-B.outerRate * T₀) * Real.exp (B.outerRate * T₀)) := by ring
        _ = _ := by rw [he, mul_one]
    have hmono := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (lt_of_not_ge hnot).le B.outerRate_pos.le)) hU.le
    linarith only [hlower, hsmall, hmono, hj]
  have hfnU := (scalar_prefix_norm_le ((hUU.trans hU₀U₁).trans hU₁δ) hf).trans hfn
  have hlam := (hlate U T hU.le hT.le hUR p hp f hfU x hx hfnU (hUU.trans hU₀U₂)
    uU vT vT hlateT le_rfl (3 / 4) (by norm_num)
    (fun v hv => by
      have he : v = vT := le_antisymm hv.2 hv.1
      rw [he, hhit]
      exact ⟨le_rfl, hYR⟩)
    (fun v _ => (hg uU v).2.2.2.2.1)).1 vT ⟨le_rfl, le_rfl⟩
  have hnl := mul_le_mul_of_nonneg_left (hg uU vT).2.2.1 hU.le
  have hnh := mul_le_mul_of_nonneg_left (hg uU vT).2.2.2.1 hU.le
  have hjn := mul_le_mul_of_nonneg_left hlower hn.le
  have hDN := mul_le_mul_of_nonneg_left hw hN.le
  exact ⟨T, hT, x, hx, hlo, hhit, hbefore, hlower, hw,
    by nlinarith only [hnl, hjn], by nlinarith only [hnh, hDN], hlam, hg, hscalar⟩

end CauchyHorizon.Background
