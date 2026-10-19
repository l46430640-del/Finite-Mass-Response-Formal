import CauchyHorizon.Characteristic.ArrivalPhase

/-! Late normalization at every physical point of a fixed radius. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1200000 in
theorem exists_physical_radius_normalization (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R →
        ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ, (∀ ε U, 0 < τ ε U) ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
            MemLp f p (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (ε U : Ioi (0 : ℝ)) (W V : ℝ) (hW : 0 ≤ W) (hV : 0 ≤ V) (hWR : W < r 0),
              U ≤ W → ∀ (hfW : MemLp f p (volume.restrict (Icc 0 W))) (x : WaveState W V)
                (hx : IsWaveIntegral hW hV B.charge B.cosmological
                  (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hWR hp hfW) x) (u : Icc 0 W) (v : Icc 0 V),
                τ ε U ≤ v → x.1 u v 0 = Y →
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) x.1 hx.choose
                  0 < (u : ℝ) ∧ |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F Y))| < ε := by
  classical
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  let a := B.outerRate
  let cν := Real.exp (∫ t in Ioi 0,
    2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - a)
  have hcν : 0 < cν := Real.exp_pos _
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hsolve⟩ := B.exists_arrival_phase_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y hY hYR
  have hYb : Y ∈ Ioo B.inner B.event := ⟨hY, hYR.trans_lt hR.2⟩
  obtain ⟨T, σ, hT, hσ, hnorm⟩ := hsolve Y hY hYR
  let D := Real.exp 1 * B.z Y / cν
  have hlim : Tendsto (fun t : ℝ => D * Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (neg_neg_of_pos B.outerRate_pos))).const_mul D
  have hcut (U : Ioi (0 : ℝ)) : ∃ S : ℝ, ∀ t ≥ S, D * Real.exp (-a * t) < U :=
    eventually_atTop.1 (hlim.eventually_lt_const U.property)
  choose S hS using hcut
  let τ := fun ε U => max (σ ε) (max (σ ⟨1, by norm_num⟩) (S U))
  refine ⟨τ, fun ε U => hT.trans_le ((hσ ε).trans (le_max_left _ _)), ?_⟩
  intro p hp f hf hfn ε U W V hW hV hWR hUW hfW x hx u v hlate hrad
  obtain ⟨g, _hgc, _hga, _hgl, hpoint⟩ := hnorm p hp f hf hfn
  have hε : σ ε ≤ v := (le_max_left _ _).trans hlate
  have h1 : σ ⟨1, by norm_num⟩ ≤ v := ((le_max_left _ _).trans (le_max_right _ _)).trans hlate
  have hTv : T ≤ (v : ℝ) := (hσ ε).trans hε
  have hg := hpoint v hTv
  have hgW : g v ≤ W := by
    have herr := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt (hg.2.2.2.1 ⟨1, by norm_num⟩ h1)
    have hlog : Real.log (B.z Y / (g v * (cν * Real.exp (a * v)))) =
        Real.log (B.z Y) - Real.log (g v) - Real.log cν - a * v := by
      rw [Real.log_div (B.z_pos hYb).ne' (mul_pos hg.1.1 (mul_pos hcν (Real.exp_pos _))).ne',
        Real.log_mul hg.1.1.ne' (mul_pos hcν (Real.exp_pos _)).ne',
        Real.log_mul hcν.ne' (Real.exp_pos _).ne', Real.log_exp (a * v)]
      ring
    rw [hlog] at herr
    have he := Real.exp_le_exp.2 (show Real.log (g v) + a * v ≤ 1 + Real.log (B.z Y) - Real.log cν by
      linarith only [(abs_lt.1 herr).1])
    have hwidth : g v * Real.exp (a * v) ≤ D := by
      simpa only [D, Real.exp_sub, Real.exp_add, Real.exp_log hg.1.1,
        Real.exp_log (B.z_pos hYb), Real.exp_log hcν] using he
    have hh := (le_div_iff₀ (Real.exp_pos (a * v))).2 hwidth
    have hh' : g v ≤ D * Real.exp (-a * v) := by
      simpa only [neg_mul, Real.exp_neg, div_eq_mul_inv] using hh
    exact (hh'.trans (hS U v (((le_max_right _ _).trans (le_max_right _ _)).trans hlate)).le).trans hUW
  have hgmem : g v ∈ Icc 0 W := ⟨hg.1.1.le, hgW⟩
  have hphysical := hg.2.2.2.2 W V hW hV hWR hfW x hx hgW v.property.2
  simp only [projIcc_of_mem hW hgmem, projIcc_of_mem hV v.property] at hphysical
  have hanti := hx.radial_strictAnti hx.choose rfl
    (incomingWave_constraint_data hW hWR hp hfW (horizonPhi h r 0)).1 v
    (fun q => (hx.interior_gauge hW hV hWR hc hi hrc hr0 hφ hrd hp hfW q v).2.2.1)
  have heq : u = ⟨g v, hgmem⟩ := hanti.injective (hrad.trans hphysical.1.symm)
  rw [heq]
  exact ⟨hg.1.1, hphysical.2.2 ε hε⟩

end CauchyHorizon.Background
