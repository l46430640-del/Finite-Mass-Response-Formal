import CauchyHorizon.Characteristic.RadiusTimeMap
import CauchyHorizon.Characteristic.InnerFunction

/-! Inner radius sections lie before the original gamma at sufficiently late times. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_nested_radius_sections (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R L : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧ 0 < L ∧
      ∀ Y Z β U : ℝ, B.inner < Y → Y < Z → Z ≤ R → 0 < β → 0 < U →
        ∃ T : ℝ, 0 < T ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
            MemLp f p (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Ici T) ∧
              (∀ t ∈ Ici T, t < ψ t ∧ ψ t ≤ (1 + β) * t) ∧
              ∀ (W V : ℝ) (hW : 0 ≤ W) (hV : 0 ≤ V) (hWR : W < r 0)
                (hfW : MemLp f p (volume.restrict (Icc 0 W))) (x : WaveState W V)
                (_hx : IsWaveIntegral hW hV B.charge B.cosmological
                  (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hWR hp hfW) x),
                U ≤ W → ∀ t ∈ Ici T, ψ t ≤ V → ∀ u : Icc 0 W,
                  x.1 u (projIcc 0 V hV t) 0 = Z →
                    x.1 u (projIcc 0 V hV (ψ t)) 0 = Y ∧
                    ∀ hr : ∀ q v, x.1 q v 0 ≠ 0,
                      let ν := radialNuField hV B.charge B.cosmological
                        (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) x.1 hr
                      let v := projIcc 0 V hV (ψ t)
                      Real.exp (-1) * (-B.F Y) / B.outerRate ≤ (u : ℝ) * (-ν u v) ∧
                      (u : ℝ) * (-ν u v) ≤ Real.exp 1 * (-B.F Y) / B.outerRate ∧
                      0 < -x.2.1 u v 0 ∧ -x.2.1 u v 0 ≤ L * (Y - B.inner) := by
  dsimp only
  let a := B.outerRate
  let cν := Real.exp (∫ t in Ioi 0,
    2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - a)
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R₀, hδ, hδr, hR₀, hmaps⟩ := B.exists_radius_time_map
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨LF, hLF, hFbound⟩ := B.exists_inner_F_bound
  let R := min R₀ (2 * B.inner)
  let L := 2 * Real.exp 1 * LF
  have hR : R ∈ Ioo B.inner B.event :=
    ⟨lt_min hR₀.1 (by linarith only [B.inner_pos]), (min_le_left _ _).trans_lt hR₀.2⟩
  refine ⟨δ, R, L, hδ, hδr, hR, by dsimp only [L]; positivity, ?_⟩
  intro Y Z β U hY hYZ hZR hβ hU
  have hYband : Y ∈ Ioo B.inner B.event := ⟨hY, (hYZ.trans_le hZR).trans hR.2⟩
  have hFY : -B.F Y ≤ LF * (Y - B.inner) := by
    have hh := hFbound Y ⟨by linarith only [hY, B.inner_pos],
      (hYZ.le.trans hZR).trans (min_le_right _ _)⟩ B.mass 1 ⟨by norm_num, le_rfl⟩
    change |1 * B.F Y| ≤ LF * (|Y - B.inner| + |B.mass - B.mass|) at hh
    simpa only [one_mul, sub_self, abs_zero, add_zero, abs_of_neg (B.F_neg hYband),
      abs_of_pos (sub_pos.2 hY)] using hh
  obtain ⟨T₀, _τ, hT₀, _hτ, hsolve⟩ := hmaps Y Z hY hYZ (hZR.trans (min_le_left _ _))
  let D := Real.exp 1 * B.z Z / cν
  let C := (|Real.log (B.z Y) - Real.log (B.z Z)| + 2) / a
  have hlim : Tendsto (fun t : ℝ => D * Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (neg_neg_of_pos B.outerRate_pos))).const_mul D
  obtain ⟨S, hS⟩ := eventually_atTop.1 (hlim.eventually_lt_const hU)
  let T := max T₀ (max S (C / β))
  have hTT : T₀ ≤ T := le_max_left _ _
  refine ⟨T, hT₀.trans_le hTT, ?_⟩
  intro p hp f hf hfn
  obtain ⟨_gY, gZ, ψ, hψc, hpoint, _herr, hphysical⟩ := hsolve p hp f hf hfn
  have hsub : Ici T ⊆ Ici T₀ := fun _ ht => hTT.trans ht
  have hwidth (t : ℝ) (ht : T ≤ t) : gZ t ≤ U := by
    have hh := (le_div_iff₀ (Real.exp_pos (a * t))).2 (hpoint t (hsub ht)).2.2.2.2.2
    have hh' : gZ t ≤ D * Real.exp (-a * t) := by
      simpa only [D, cν, a, neg_mul, Real.exp_neg, div_eq_mul_inv] using hh
    exact hh'.trans (hS t (((le_max_left _ _).trans (le_max_right _ _)).trans ht)).le
  refine ⟨ψ, hψc.mono hsub, ?_, ?_⟩
  · intro t ht
    have hh := hpoint t (hsub ht)
    have hCt : C ≤ β * t := (div_le_iff₀ hβ).1
      (((le_max_right _ _).trans (le_max_right _ _)).trans ht) |>.trans_eq (mul_comm _ _)
    exact ⟨hh.1, by linarith only [(abs_le.1 hh.2.2.2.2.1).2, hCt]⟩
  · intro W V hW hV hWR hfW x hx hUW t ht hψV u hu
    have hpnt := hpoint t (hsub ht)
    have hgw : gZ t ∈ Icc 0 W := ⟨hpnt.2.1.le, (hwidth t ht).trans hUW⟩
    have hh := hphysical W V hW hV hWR hfW x hx t (hsub ht) hgw.2 hψV
    rw [projIcc_of_mem hW hgw] at hh
    have hanti := hx.radial_strictAnti hx.choose rfl
      (incomingWave_constraint_data hW hWR hp hfW (horizonPhi h r 0)).1 (projIcc 0 V hV t)
      (fun q => (hx.interior_gauge hW hV hWR hc (horizon_mass_integrable hs hH hc hb) hrc
        (fun z => ((sub_pos.2 hdHR).trans_le (hrb z)).ne') hφ hrd hp hfW q (projIcc 0 V hV t)).2.2.1)
    have heq : u = ⟨gZ t, hgw⟩ := hanti.injective (hu.trans hh.1.symm)
    rw [heq]
    refine ⟨hh.2.1, ?_⟩
    intro hr
    refine ⟨hh.2.2.2.1, hh.2.2.2.2.1, hh.2.2.2.2.2.1, ?_⟩
    exact hh.2.2.2.2.2.2.trans ((mul_le_mul_of_nonneg_left hFY (by positivity : 0 ≤ 2 * Real.exp 1)).trans_eq
      (by dsimp only [L]; ring))

end CauchyHorizon.Background
