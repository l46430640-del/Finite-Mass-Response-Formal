import CauchyHorizon.Characteristic.RadiusContact
import CauchyHorizon.Characteristic.BandClosure

/-! Uniform row continuation constructs a finite first passage to a radius level. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 800000 in
theorem exists_horizon_radius_passage {M e Λ U Y A a D : ℝ} {h r : ℝ → ℝ}
    (hU : 0 < U) (hU1 : U ≤ 1) (hUR : U < r 0) (hY : 0 < Y) (hinit : Y < r 0 - U)
    (hA : 0 ≤ A) (ha : 0 < a) (hD : 0 < D)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hfn : (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A)
    (hstart : ∃ x : WaveState U 0, IsWaveIntegral hU.le le_rfl e Λ
      (incomingWaveCurve hU.le hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ 0 hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hwidth : ∀ (V : ℝ) (hV : 0 ≤ V) (x : WaveState U V),
      IsWaveIntegral hU.le hV e Λ (incomingWaveCurve hU.le hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x →
      (∀ u v, Y ≤ x.1 u v 0) → U * Real.exp (a * V) ≤ D) :
    ∃ T : ℝ, ∃ hT : 0 < T, ∃ x : WaveState U T,
      IsWaveIntegral hU.le hT.le e Λ (incomingWaveCurve hU.le hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ T hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x ∧
      (∀ u v, Y ≤ x.1 u v 0) ∧ x.1 ⟨U, hU.le, le_rfl⟩ ⟨T, hT.le, le_rfl⟩ 0 = Y ∧
      (∀ (u : Icc 0 U) (v : Icc 0 T), (v : ℝ) < T → Y < x.1 u v 0) ∧ U * Real.exp (a * T) ≤ D := by
  let Vmax := (D / U + 1) / a
  have hVmax : 0 < Vmax := by dsimp only [Vmax]; positivity
  have hlarge : D < U * Real.exp (a * Vmax) := by
    have he := Real.add_one_le_exp (a * Vmax)
    have heq : a * Vmax = D / U + 1 := by dsimp only [Vmax]; field_simp
    rw [heq] at he
    have hh := mul_le_mul_of_nonneg_left he hU.le
    have hcancel : U * (D / U) = D := by field_simp
    rw [heq]
    nlinarith only [hh, hcancel, hU]
  have hrp : 0 < r 0 := hU.trans hUR
  obtain ⟨d, hd, _hd1, hext⟩ := exists_horizon_row_extension hVmax.le hrp hc hi hrc hr0 hφ hrd hY hA
  let Q := ∃ T : ℝ, ∃ hT : 0 < T, ∃ x : WaveState U T,
    IsWaveIntegral hU.le hT.le e Λ (incomingWaveCurve hU.le hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ T hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x ∧
    (∀ u v, Y ≤ x.1 u v 0) ∧ x.1 ⟨U, hU.le, le_rfl⟩ ⟨T, hT.le, le_rfl⟩ 0 = Y ∧
    (∀ (u : Icc 0 U) (v : Icc 0 T), (v : ℝ) < T → Y < x.1 u v 0)
  let P := fun t : ℝ => Q ∨ ∃ ht : 0 ≤ t, ∃ x : WaveState U t,
    IsWaveIntegral hU.le ht e Λ (incomingWaveCurve hU.le hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ t hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x ∧
    ∀ u v, Y ≤ x.1 u v 0
  have hbase : P 0 := by
    obtain ⟨x, hx⟩ := hstart
    refine Or.inr ⟨le_rfl, x, hx, ?_⟩
    intro u v
    have hv : v = ⟨0, le_rfl, le_rfl⟩ := Subtype.ext (le_antisymm v.property.2 v.property.1)
    rw [hv, (hx.horizon_traces hU.le le_rfl hUR hc hi hrc hr0 hφ hrd hp hf).1 u]
    change Y ≤ r 0 - u
    linarith only [hinit, u.property.2]
  have hstep (t s : ℝ) (_ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s ≤ Vmax) (hsd : s ≤ d)
      (hP : P t) : P (t + s) := by
    rcases hP with hQ | ⟨ht, x, hx, hlo⟩
    · exact Or.inl hQ
    obtain ⟨y, hy, _hloy, _hold⟩ := hext hU.le ht hs hU1 hsd hts hUR hp hf hfn hx hlo
    by_cases hbad : ∃ u v, y.1 u v 0 ≤ Y
    · obtain ⟨τ, hτ, hhit, hbefore, hfloor⟩ := hy.exists_first_radius_contact hU.le (add_nonneg ht hs)
        hUR hc hi hrc hr0 hφ hrd hp hf hinit hbad
      let z := waveTranslate (a := 0) (U := U) (b := 0) (V := (τ : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using τ.property.2) y
      have hz : IsWaveIntegral hU.le hτ.le e Λ (incomingWaveCurve hU.le hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ τ hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) z :=
        hy.horizon_prefix hU.le (add_nonneg ht hs) hUR hU.le hτ.le le_rfl τ.property.2 hc hi hrc hr0 hp hf
      have hze (u : Icc 0 U) (v : Icc 0 (τ : ℝ)) :
          z.1 u v = y.1 u ⟨v, v.property.1, v.property.2.trans τ.property.2⟩ := by
        change y.1 (intervalTranslate (a := 0) (U := U) le_rfl (by simp) u)
          (intervalTranslate (a := 0) (U := (τ : ℝ)) le_rfl (by simpa only [zero_add] using τ.property.2) v) = _
        rw [intervalTranslate_zero]
        congr 1
        exact Subtype.ext (zero_add _)
      refine Or.inl ⟨τ, hτ, z, hz, ?_, ?_, ?_⟩
      · intro u v
        rw [hze]
        exact hfloor u _ v.property.2
      · rw [hze]
        exact hhit
      · intro u v hvt
        rw [hze]
        exact hbefore u _ hvt
    · refine Or.inr ⟨add_nonneg ht hs, y, hy, ?_⟩
      intro u v
      exact (lt_of_not_ge (fun hv => hbad ⟨u, v, hv⟩)).le
  have hQ : Q := by
    rcases interval_subdivision_induction hVmax.le hd hbase hstep with hQ | ⟨ht, x, hx, hlo⟩
    · exact hQ
    · exact (hlarge.not_ge (hwidth Vmax ht x hx hlo)).elim
  obtain ⟨T, hT, x, hx, hlo, hhit, hbefore⟩ := hQ
  exact ⟨T, hT, x, hx, hlo, hhit, hbefore, hwidth T hT.le x hx hlo⟩

namespace Background

set_option maxHeartbeats 800000 in
theorem exists_band_passage (B : Background) {s H dH A c : ℝ}
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
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ U₀ D n N L E : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ U₀ ≤ 1 ∧ U₀ < r 0 ∧ 0 < D ∧ 0 < n ∧ 0 < N ∧ 0 ≤ L ∧ 0 ≤ E ∧
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
              (∀ u v, Y ≤ x.1 u v 0) ∧ x.1 ⟨U, hU.le, le_rfl⟩ ⟨T, hT.le, le_rfl⟩ 0 = Y ∧
              (∀ (u : Icc 0 U) (v : Icc 0 T), (v : ℝ) < T → Y < x.1 u v 0) ∧ U * Real.exp (B.outerRate * T) ≤ D ∧
              (∀ u v, x.1 u v 0 ≤ B.event + dH ∧ |x.2.1 u v 0| ≤ L ∧
                n * Real.exp (B.outerRate * v) ≤ -ν u v ∧ -ν u v ≤ N * Real.exp (B.outerRate * v) ∧
                (3 / 4 : ℝ) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧ |x.2.1 u v 1| ≤ E * Real.exp (-c * v)) ∧
              (∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 T,
                |x.2.2 u v 1| ≤ (r 0 / Y) * |f u| + (N / (Y * (B.outerRate - c))) * E * Real.exp ((B.outerRate - c) * v)) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have hrp : 0 < r 0 := B.inner_pos.trans hrinit
  obtain ⟨δ, R, hδ, hδr, hR, hbound⟩ :=
    B.exists_band_bounds hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  obtain ⟨d, hd, hdr, hd1, hstart⟩ :=
    exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0 hrp hφ hrd A hA
  let R₀ := min R ((r 0 + B.inner) / 2)
  have hR₀ : B.inner < R₀ := lt_min hR.1 (by linarith only [hrinit])
  have hR₀R : R₀ ≤ R := min_le_left _ _
  have hR₀r : R₀ < r 0 := (min_le_right _ _).trans_lt (by linarith only [hrinit])
  refine ⟨δ, R₀, hδ, hδr, ⟨hR₀, hR₀R.trans_lt hR.2⟩, hR₀r, ?_⟩
  intro Y hY hYR
  have hY0 : 0 < Y := B.inner_pos.trans hY
  have hYr : Y < r 0 := hYR.trans_lt hR₀r
  obtain ⟨U₁, D, n, N, L, E, hU₁, hU₁δ, hD, hn, hN, hL, hE, hbnd⟩ :=
    hbound Y hY (hYR.trans hR₀R)
  let U₀ := min U₁ (min d ((r 0 - Y) / 2))
  have hU₀ : 0 < U₀ := lt_min hU₁ (lt_min hd (half_pos (sub_pos.2 hYr)))
  have hU₀U₁ : U₀ ≤ U₁ := min_le_left _ _
  have hU₀d : U₀ ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hU₀Y : U₀ ≤ (r 0 - Y) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨U₀, D, n, N, L, E, hU₀, hU₀U₁.trans hU₁δ, hU₀d.trans hd1, hU₀d.trans_lt hdr,
    hD, hn, hN, hL, hE, ?_⟩
  intro p hp f hf hfn hcb U hU hUR hfU hUU
  have hUδ := (hUU.trans hU₀U₁).trans hU₁δ
  have hfnU := (scalar_prefix_norm_le hUδ hf).trans hfn
  have hinit : Y < r 0 - U := by linarith only [hUU.trans hU₀Y, hYr]
  obtain ⟨x₀, hx₀, _htraces⟩ := hstart hU.le le_rfl hUR (hUU.trans hU₀d) hd.le hp hfU hfnU
  obtain ⟨T, hT, x, hx, hlo, hhit, hbefore, hw⟩ := exists_horizon_radius_passage hU
    ((hUU.trans hU₀d).trans hd1) hUR hY0 hinit hA B.outerRate_pos hD hc hi hrc hr0 hφ hrd hp hfU hfnU
    ⟨x₀, hx₀⟩ (fun V hV y hy hry =>
      (hbnd p hp f hf hfn hcb U V hU.le hV hUR hfU y hy (hUU.trans hU₀U₁) hry).1)
  exact ⟨T, hT, x, hx, hlo, hhit, hbefore, hw,
    (hbnd p hp f hf hfn hcb U T hU.le hT.le hUR hfU x hx (hUU.trans hU₀U₁) hlo).2⟩

end Background

end CauchyHorizon
