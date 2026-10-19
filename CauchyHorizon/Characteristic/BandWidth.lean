import CauchyHorizon.Characteristic.OuterArrival
import CauchyHorizon.Characteristic.BandGeometry

/-! Exponential width follows from actual outer arrival and the band bootstrap. -/

open MeasureTheory Set
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_band_width (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ U₀ D : ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < D ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (_hf : MemLp f p (volume.restrict (Icc 0 δ))),
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
            (hx : IsWaveIntegral hU hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x),
            U ≤ U₀ → (∀ u v, Y ≤ x.1 u v 0) →
            (∀ u v, (1 / 2 : ℝ) ≤ -Real.exp (x.1 u v 2) /
              (4 * radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose u v)) →
            U * Real.exp (B.outerRate * V) ≤ D := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have ha := B.outerRate_pos
  obtain ⟨δ, R, T, j, J, b, C, ε, hδ, hδr, hR, hT, hj, hJ, _hJδ, _hb, _hC, hε, harr⟩ :=
    B.exists_outer_arrival hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut
      (c := 0) le_rfl ha hs.le hA
  refine ⟨δ, R, hδ, hδr, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨U₁, T₁, q, P, hU₁, _hU₁r, _hT₁, hq, _hP, hband⟩ :=
    B.exists_late_band_geometry hY hYR hR.2 hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  let U₀ := min δ (min (ε / 2) (min U₁ (j * Real.exp (-B.outerRate * T₁) / 2)))
  let d := (R - Y) / ((1 / 2) * q)
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.2 hYR) (by positivity)
  have hU₀ : 0 < U₀ := by dsimp only [U₀]; positivity
  have hU₀δ : U₀ ≤ δ := min_le_left _ _
  have hU₀ε : U₀ ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hU₀U₁ : U₀ ≤ U₁ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hU₀T : U₀ ≤ j * Real.exp (-B.outerRate * T₁) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨U₀, J * Real.exp (B.outerRate * d), hU₀, hU₀δ, by positivity, ?_⟩
  intro p hp f hf hfn
  have hcb : (0 : ℝ) ≤ B.outerRate * (1 - 1 / p.toReal) :=
    mul_nonneg ha.le (by linarith only [(incoming_exponent_bounds hp).1])
  obtain ⟨g, inv, _hcg, _hag, _hlim, _hci, _hli, hright, _hleft, hphys⟩ := harr p hp f hf hfn hcb
  intro U V hU hV hUR hfU x hx hUU hlo hk
  by_cases hUz : U = 0
  · simpa only [hUz, zero_mul] using (mul_pos hJ (Real.exp_pos (B.outerRate * d))).le
  have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hUz)
  have hUε : U ∈ Ioo 0 ε := ⟨hUp, (hUU.trans hU₀ε).trans_lt (half_lt_self hε)⟩
  let t := inv U
  obtain ⟨htT, hgt, _hdinv⟩ := hright U hUε
  change g t = U at hgt
  have ht : T < t := by linarith only [htT]
  have ht0 : 0 ≤ t := hT.trans ht.le
  obtain ⟨_hgpos, hscaleLo, hscaleHi, _hslo, _hshi, W, Z, hW, hZ, hWR, hfW, z, hz,
    u, v, hu, hv, _hui, _hvi, hrR, _hw, _hder, _hjac⟩ := hphys t ht
  rw [hgt] at hscaleLo hscaleHi
  have hentry : T₁ ≤ t := by
    by_contra hnot
    have hlt : t < T₁ := lt_of_not_ge hnot
    have hmul := mul_le_mul_of_nonneg_right (hUU.trans hU₀T) (Real.exp_pos (B.outerRate * T₁)).le
    have he : Real.exp (-B.outerRate * T₁) * Real.exp (B.outerRate * T₁) = 1 := by
      rw [← Real.exp_add, show -B.outerRate * T₁ + B.outerRate * T₁ = 0 by ring, Real.exp_zero]
    have hsmall : U * Real.exp (B.outerRate * T₁) ≤ j / 2 := by
      apply hmul.trans_eq
      calc
        _ = (j / 2) * (Real.exp (-B.outerRate * T₁) * Real.exp (B.outerRate * T₁)) := by ring
        _ = _ := by rw [he, mul_one]
    have hmono := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hlt.le ha.le)) hU
    linarith only [hscaleLo, hsmall, hmono, hj]
  have hfactor : U * Real.exp (B.outerRate * V) =
      (U * Real.exp (B.outerRate * t)) * Real.exp (B.outerRate * (V - t)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have htime : V - t ≤ d := by
    by_cases htV : t ≤ V
    · have huW : U ∈ Icc 0 W := by simpa only [hu, hgt] using u.property
      have hvZ : t ∈ Icc 0 Z := by simpa only [hv] using v.property
      let uU : Icc 0 U := ⟨U, hU, le_rfl⟩
      let vT : Icc 0 V := ⟨t, ht0, htV⟩
      have ho := hz.horizon_overlap hW hZ hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
        huW uU.property hvZ vT.property
      have hrz : z.1 ⟨U, huW⟩ ⟨t, hvZ⟩ 0 = R := by
        have heu : (⟨U, huW⟩ : Icc 0 W) = u := Subtype.ext (by simpa only [hgt] using hu.symm)
        have hev : (⟨t, hvZ⟩ : Icc 0 Z) = v := Subtype.ext hv.symm
        rw [heu, hev]
        exact hrR
      have hrx : x.1 uU vT 0 = R := (congrArg (fun z : WaveVector => z 0) ho.1).symm.trans hrz
      have hfnU := (scalar_prefix_norm_le (hUU.trans hU₀δ) hf).trans hfn
      have hstart := (hband U V hU hV hUR p hp f hfU x hx hfnU (hUU.trans hU₀U₁)
        uU vT vT hentry le_rfl (1 / 2) (by norm_num)
        (fun w hw => by have he : w = vT := le_antisymm hw.2 hw.1; rw [he, hrx]; exact ⟨hYR, le_rfl⟩)
        (fun w _ => hk uU w)).1 vT ⟨le_rfl, le_rfl⟩
      have hlam : x.2.1 uU vT 0 < 0 := by linarith only [hstart, hq]
      have hbandRange (w : Icc 0 V) (hw : w ∈ Icc vT ⟨V, hV, le_rfl⟩) :
          x.1 uU w 0 ∈ Icc Y R := ⟨hlo uU w, by
        rw [← hrx]
        exact (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hfU uU vT w hw.1 hlam).2⟩
      exact (hband U V hU hV hUR p hp f hfU x hx hfnU (hUU.trans hU₀U₁) uU vT ⟨V, hV, le_rfl⟩
        hentry htV (1 / 2) (by norm_num) hbandRange (fun w _ => hk uU w)).2.1
    · exact (sub_nonpos.2 (le_of_not_ge htV)).trans hd
  rw [hfactor]
  exact mul_le_mul hscaleHi (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htime ha.le))
    (Real.exp_pos _).le hJ.le

end CauchyHorizon.Background
