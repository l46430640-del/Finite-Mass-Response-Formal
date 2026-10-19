import CauchyHorizon.Characteristic.LateMass

/-! A bounded time shift from a thin prefix preserves the exact outer rate. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1200000 in
theorem exists_bounded_width_geometry (B : Background) {s H dH A ρ D : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hρ : 0 < ρ) (hρR : ρ ≤ B.event + dH)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ n N L : ℝ, 0 < U₀ ∧ U₀ ≤ r 0 / 4 ∧ 0 < n ∧ 0 < N ∧ 0 ≤ L ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ U₀ →
        (∀ u v, ρ ≤ x.1 u v 0) → U * Real.exp (B.outerRate * V) ≤ D → ∀ u v,
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          x.1 u v 0 ≤ B.event + dH ∧ |x.2.1 u v 0| ≤ L ∧
            n * Real.exp (B.outerRate * v) ≤ -ν u v ∧ -ν u v ≤ N * Real.exp (B.outerRate * v) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let μ := (B.event - dH) / 2
  let R := B.event + dH
  have hμ : 0 < μ := half_pos (sub_pos.2 hdHR)
  have hR : 0 < R := hρ.trans_le hρR
  obtain ⟨L₀, hL₀, hrlam⟩ := B.horizon_radius_lambda_bounds hs hH hdH hdHR hb hrdec
  have haxis (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : r t ∈ Icc (2 * μ) R := by
    have hh := (hrlam t ht).1
    exact ⟨by dsimp only [μ]; linarith only [hh.1], hh.2⟩
  have hlout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      |horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological| ≤ L₀ :=
    (hrlam t ht).2.trans (mul_le_of_le_one_right hL₀ (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) ht)))
  have hout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : Real.exp (0 * t) * |h t| ≤ H := by
    simp only [zero_mul, Real.exp_zero, one_mul]
    have hh : |h t| ≤ H * Real.exp (-s * t) := by simpa only [Real.norm_eq_abs] using hb t
    exact hh.trans (mul_le_of_le_one_right hH (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hs.le) ht)))
  obtain ⟨nH, NH, hnH, _hnH1, hNH, hνaxis⟩ := hOut.nu_bounds hs hc hi hrc hr0
  obtain ⟨δ, _L, hδ, _hδ1, hδr, _hL, houter⟩ := exists_horizon_outer_bounds
    hc hi hrc hr0 hφ hrd ha le_rfl ha hμ hnH (zero_lt_one.trans_le hNH) hH hL₀ hA haxis hνaxis hout hlout
  obtain ⟨P, hP, hpot⟩ := radialPotential_bounded B.charge B.cosmological (R := R) hρ
  have hlim : Tendsto (fun t : ℝ => δ * Real.exp (a * t)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)).const_mul_atTop hδ
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually_ge_atTop D)
  let τ := max 0 T
  have hτ : 0 ≤ τ := le_max_left _ _
  have hD : D ≤ δ * Real.exp (a * τ) := hT τ (le_max_right _ _)
  let n₀ := (9 / 16) * nH
  let N₀ := (5 / 3) * NH
  let c₀ := (ρ / R) * Real.exp (-(4 * P) * τ)
  let C₀ := (R / ρ) * Real.exp (4 * P * τ)
  let n := min n₀ (c₀ * n₀ * Real.exp (-a * τ))
  let N := max N₀ (C₀ * N₀)
  let L := (R * L₀ + 4 * R ^ 2 * P) / ρ
  have hn₀ : 0 < n₀ := by dsimp only [n₀]; positivity
  have hN₀ : 0 < N₀ := by dsimp only [N₀]; positivity
  have hc₀ : 0 < c₀ := by dsimp only [c₀]; positivity
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨δ, n, N, L, hδ, hδr, by dsimp only [n]; positivity,
    hN₀.trans_le (le_max_left _ _), by dsimp only [L]; positivity, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hUU hlo hwidth
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hn (u : Icc 0 U) (v : Icc 0 V) : ν u v < 0 := (hg u v).2.2.1
  have hΩ (u : Icc 0 U) (v : Icc 0 V) : Real.exp (x.1 u v 2) ≤ -4 * ν u v := by
    have hh := (div_le_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) (hn u v))).1
      (hg u v).2.2.2.2
    linarith only [hh]
  have hflux := hx.finite_radial_flux_bound hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 hρ hρR hP hpot hlo
    (fun v => by rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]; exact (haxis v v.property.1).2)
    (fun v => hlout v v.property.1) (fun u v => (hn u v).le) hΩ
  let W := max 0 (V - τ)
  have hW : 0 ≤ W := le_max_left _ _
  have hWV : W ≤ V := max_le hV (by linarith only [hτ])
  have hthin : U * Real.exp (a * W) ≤ δ := by
    by_cases hVT : V ≤ τ
    · have hWz : W = 0 := max_eq_left (sub_nonpos.2 hVT)
      simpa only [hWz, mul_zero, Real.exp_zero, mul_one] using hUU
    · have hWe : W = V - τ := max_eq_right (sub_nonneg.2 (le_of_not_ge hVT))
      apply (mul_le_mul_iff_left₀ (Real.exp_pos (a * τ))).1
      calc
        _ = U * Real.exp (a * V) := by
          rw [mul_assoc, ← Real.exp_add, hWe]
          congr 2
          ring
        _ ≤ _ := hwidth.trans hD
  let y := waveTranslate (a := 0) (U := U) (b := 0) (V := W) le_rfl (by simp)
    le_rfl (by simpa only [zero_add] using hWV) x
  have hy : IsWaveIntegral hU hW B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological W hc hi hrc hr0)
      (incomingWaveVelocity hUR hp hf) y :=
    hx.horizon_prefix hU hV hUR hU hW le_rfl hWV hc hi hrc hr0 hp hf
  have hye (u : Icc 0 U) (w : Icc 0 W) : y.1 u w = x.1 u ⟨w, w.property.1, w.property.2.trans hWV⟩ := by
    change x.1 (intervalTranslate (a := 0) (U := U) le_rfl (by simp) u)
      (intervalTranslate (a := 0) (U := W) le_rfl (by simpa only [zero_add] using hWV) w) = _
    rw [intervalTranslate_zero]
    congr 1
    exact Subtype.ext (zero_add _)
  have hcb : (0 : ℝ) ≤ a * (1 - 1 / p.toReal) :=
    mul_nonneg ha.le (by linarith only [(incoming_exponent_bounds hp).1])
  have houter' := houter U W hU hW hUR p hp f hf y hy hfn hcb hthin
  have hbefore (u : Icc 0 U) (v : Icc 0 V) (hvW : (v : ℝ) ≤ W) :
      n₀ * Real.exp (a * v) ≤ -ν u v ∧ -ν u v ≤ N₀ * Real.exp (a * v) := by
    let w : Icc 0 W := ⟨v, v.property.1, hvW⟩
    have hne := radialNuField_prefix_eq hW hV hWV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 y.1 hx.choose hy.choose hye u w
    have hh := (houter' u w).2.2.2
    rw [hne] at hh
    exact hh
  intro u v
  refine ⟨(hflux u v).1, (hflux u v).2.2, ?_⟩
  by_cases hvW : (v : ℝ) ≤ W
  · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le).trans (hbefore u v hvW).1,
      (hbefore u v hvW).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩
  have hWv : W ≤ (v : ℝ) := le_of_not_ge hvW
  let w : Icc 0 V := ⟨W, hW, hWV⟩
  have htime : (v : ℝ) - W ≤ τ := by linarith only [v.property.2, le_max_right 0 (V - τ)]
  have hseg := radialNuField_flux_segment_bound hx.choose (fun u v => (hg u v).2.1) hn u w v hWv
    (fun t _ => hpot _ ⟨hlo u t, (hflux u t).1⟩) (fun t _ => (hg u t).2.2.2.2)
  have hlowExp : Real.exp (-(4 * P) * τ) ≤ Real.exp (-(4 * P) * ((v : ℝ) - W)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left htime (neg_nonpos.2 (by positivity)))
  have hhighExp : Real.exp (4 * P * ((v : ℝ) - W)) ≤ Real.exp (4 * P * τ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htime (by positivity))
  have hlow : c₀ * (-ν u w) ≤ -ν u v := by
    apply (le_of_mul_le_mul_left ?_ hR)
    have h1 := mul_le_mul_of_nonneg_right hlowExp (mul_nonneg (hg u w).2.1.le (neg_pos.2 (hn u w)).le)
    have h2 := mul_le_mul_of_nonneg_right (hlo u w) (mul_nonneg (Real.exp_pos (-(4 * P) * τ)).le (neg_pos.2 (hn u w)).le)
    have h3 := mul_le_mul_of_nonneg_right (hflux u v).1 (neg_pos.2 (hn u v)).le
    have he : R * (c₀ * (-ν u w)) = ρ * Real.exp (-(4 * P) * τ) * (-ν u w) := by dsimp only [c₀]; field_simp
    rw [he]
    nlinarith only [hseg.1, h1, h2, h3]
  have hhigh : -ν u v ≤ C₀ * (-ν u w) := by
    apply (le_of_mul_le_mul_left ?_ hρ)
    have h1 := mul_le_mul_of_nonneg_right hhighExp (mul_nonneg (hg u w).2.1.le (neg_pos.2 (hn u w)).le)
    have h2 := mul_le_mul_of_nonneg_right (hflux u w).1 (mul_nonneg (Real.exp_pos (4 * P * τ)).le (neg_pos.2 (hn u w)).le)
    have h3 := mul_le_mul_of_nonneg_right (hlo u v) (neg_pos.2 (hn u v)).le
    have he : ρ * (C₀ * (-ν u w)) = R * Real.exp (4 * P * τ) * (-ν u w) := by dsimp only [C₀]; field_simp
    rw [he]
    nlinarith only [hseg.2, h1, h2, h3]
  have hbnd := hbefore u w le_rfl
  constructor
  · apply (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le).trans
    apply le_trans ?_ hlow
    have he : (c₀ * n₀ * Real.exp (-a * τ)) * Real.exp (a * v) =
        c₀ * (n₀ * Real.exp (a * ((v : ℝ) - τ))) := by
      have hexp : Real.exp (-a * τ) * Real.exp (a * v) = Real.exp (a * ((v : ℝ) - τ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = c₀ * (n₀ * (Real.exp (-a * τ) * Real.exp (a * v))) := by ring
        _ = _ := by rw [hexp]
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hc₀.le
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
      (by linarith only [htime]) ha.le)) hn₀.le).trans hbnd.1
  · apply hhigh.trans
    apply le_trans (mul_le_mul_of_nonneg_left hbnd.2 hC₀.le)
    have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hWv ha.le))
      (mul_nonneg hC₀.le hN₀.le)
    have he' : C₀ * (N₀ * Real.exp (a * W)) ≤ (C₀ * N₀) * Real.exp (a * v) := by
      simpa only [mul_assoc] using he
    exact he'.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

end CauchyHorizon.Background
