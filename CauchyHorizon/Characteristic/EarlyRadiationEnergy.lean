import CauchyHorizon.Characteristic.BandSourceEnergy
import CauchyHorizon.Characteristic.EarlyExactGeometry
import CauchyHorizon.Characteristic.EarlyMovingEnergy
import CauchyHorizon.Reduced.TerminalRadiationEnergy

/-! Uniform critical radiation energy on the actual band and early region. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 2400000 in
theorem exists_early_radiation_energy (G : Background) {s H dH A Apt c ε d β b : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event) (hA : 0 ≤ A)
    (hApt : 0 ≤ Apt) (hc0 : 0 < c) (hca : c < G.outerRate) (hcs : c ≤ s)
    (hε : 0 < ε) (hεk : ε < G.innerRate) (hd : 0 < d) (hβ : 0 ≤ β)
    (hℓ : c < 2 * (G.innerRate - ε) - d)
    (hJ : 0 < 2 * c - max 0 (2 * (G.innerRate + ε) + d - 2 * c) * β)
    (hQ : 0 < 2 * c - 2 * (G.innerRate + ε) * β)
    (hb : 0 < b) (hb1 : b < 1) (hcrit : G.innerRate = G.outerRate * b) (hks : G.innerRate < s)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hcb : c ≤ G.outerRate * (1 - 1 / p.toReal))
    (hkp : G.innerRate ≤ G.outerRate * (1 - 1 / p.toReal))
    {h r : ℝ → ℝ} (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t) (hrinit : G.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) (Ycap : ℝ) (hYcap : G.inner < Ycap) :
    let hi := horizon_mass_integrable hs hH hc hout
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y U₀ T jr D η C E₀ E₁ F₀ F₁ Dlo Dhi : ℝ,
      0 < δ ∧ δ ≤ r 0 / 4 ∧ Y ∈ Ioo G.inner G.event ∧ Y ≤ Ycap ∧
      0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ 0 < jr ∧ 0 < D ∧ 0 < η ∧ 0 < C ∧
      0 ≤ E₀ ∧ 0 ≤ E₁ ∧ 0 ≤ F₀ ∧ 0 ≤ F₁ ∧ 0 < Dlo ∧ 0 < Dhi ∧
      ∀ (ℓ : ℝ) (P : ℝ →ᵇ ℝ), Integrable (fun t => P t ^ 2) →
        MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 δ)) →
        (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        (∀ᵐ t ∂volume.restrict (Icc 0 δ),
          |logarithmicIncoming b ℓ P t| ≤ Apt * t ^ (-1 / p.toReal)) →
        ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧
          Tendsto g atTop (𝓝 0) ∧ ContinuousOn (deriv g) (Ici T) ∧ U₀ < g T ∧
          (∀ t ∈ Ici T, 0 < g t ∧ g t * Real.exp (G.outerRate * t) ≤ D ∧
            DifferentiableAt ℝ g t ∧ η ≤ -deriv g t / g t ∧
            jr ≤ g t * Real.exp (G.outerRate * t) ∧ -deriv g t / g t ≤ C) ∧
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
            ∀ (hfU : MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 U)))
              (x : WaveState U V)
              (hx : IsWaveIntegral hU.le hV G.charge G.cosmological
                (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x),
              ∃ (w : C(Icc 0 V, ℝ)) (hw0 : ∀ v, 0 ≤ w v),
                (∀ v, w v = g (max T (v : ℝ))) ∧ Antitone w ∧
                (∀ v : Icc 0 V, T ≤ v → g v ≤ U →
                  x.1 (projIcc 0 U hU.le (g v)) v 0 = Y) ∧
                (∀ t : ℝ, T ≤ t → g t ≤ U → 0 < β → (1 + β) * t ≤ V →
                  let u := projIcc 0 U hU.le (g t)
                  let a := projIcc 0 V hV t
                  Dlo * g t ≤ -x.2.1 u a 0 / Real.exp (x.1 u a 2) ∧
                  -x.2.1 u a 0 / Real.exp (x.1 u a 2) ≤ Dhi * g t ∧
                  (∫ v in t..(1 + β) * t, intervalExtension hV (x.1 u) v 0 *
                    (intervalExtension hV (x.2.1 u) v 1) ^ 2 /
                      (-intervalExtension hV (x.2.1 u) v 0)) ≤ 1 / 16 ∧
                  ∀ hr : ∀ q v, x.1 q v 0 ≠ 0,
                    let ν := radialNuField hV G.charge G.cosmological
                      (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hr
                    ∀ a' b' : Icc 0 V, t ≤ a' → a' ≤ b' → (b' : ℝ) ≤ (1 + β) * t →
                      G.inner / 2 ≤ x.1 u b' 0 ∧
                      |ν u b'| ≤ (2 * Real.exp 2) * (-ν u a') * Real.exp (-2 * G.innerRate * ((b' : ℝ) - a')) ∧
                      |x.2.1 u b' 0| ≤ (Real.exp (2 + 1 / 16) * (-x.2.1 u a' 0)) *
                        Real.exp (-2 * G.innerRate * ((b' : ℝ) - a'))) ∧
                let W : C(Icc 0 V, ℝ) := ⟨fun v => w (projIcc 0 V hV ((v : ℝ) / (1 + β))), by fun_prop⟩
                let hW0 := fun v : Icc 0 V => hw0 (projIcc 0 V hV ((v : ℝ) / (1 + β)))
                let M := movingSpatialRadiationEnvelope W hW0 0 G.innerRate 0 x
                let Z := fun t v : ℝ => g t * Real.exp (G.innerRate * t) *
                  (intervalExtension hV (intervalExtension hU.le x.1 (g t)) v 0 *
                    derivWithin (fun u => intervalExtension hV (intervalExtension hU.le x.1 u) v 1)
                      (Icc 0 U) (g t))
                (∫ t in (0 : ℝ)..V,
                  (M (projIcc 0 V hV t)) ^ 2) ≤ E₀ + E₁ * ∫ t, P t ^ 2 ∧
                (∀ l q : ℝ, T ≤ l → l ≤ q → q ≤ V → g l ≤ U →
                  (∫ t in l..q, (Z t t) ^ 2) ≤ F₀ + F₁ * ∫ t, P t ^ 2) ∧
                (∀ t : ℝ, T ≤ t → g t ≤ U → (1 + β) * t ≤ V →
                  |Z t ((1 + β) * t)| ≤ |Z t t| + (2 * Real.exp 1) * D / (G.inner / 2) *
                    ∫ v in t..(1 + β) * t, Real.exp (-(3 * G.innerRate) * (v - t)) *
                      M (projIcc 0 V hV v)) ∧
                ∀ l q : ℝ, T ≤ l → l ≤ q → (1 + β) * q ≤ V → g l ≤ U →
                  (∫ t in l..q, (Z t ((1 + β) * t)) ^ 2) ≤
                    2 * (F₀ + F₁ * ∫ t, P t ^ 2) +
                      2 * ((2 * Real.exp 1) * D / (G.inner / 2) / (3 * G.innerRate)) ^ 2 *
                        (E₀ + E₁ * ∫ t, P t ^ 2) := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hout
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hout hrb
  obtain ⟨δb, R, hδb, hδbr, hR, _hRr, hband⟩ := G.exists_band_source_energy
    hs hH hdH hdHR hA hb hb1 hcrit hks hc hout hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δe, Y, Ue, Ly, j, _De, Olo, Ohi, hδe, hδer, hY, hYR, hUe, hUeδ,
    hLy, hj, _hDe, hOlo, hOhi, hsmall, hearly⟩ := G.exists_early_exact_geometry
    hs hH hdH hdHR hA hApt hc0 hca hcs hε hεk hd hβ hℓ hJ hQ hp hcb
      hc hout hrc hrb hrinit hrd hrdec hOut (min R Ycap) (lt_min hR.1 hYcap)
  obtain ⟨Ub, T, jr, D, η, C, B₀, B₁, F₀, F₁, hUb, hUbδ, hT, hjr, hD, hη, hC,
    hB₀, hB₁, hF₀, hF₁, hsource⟩ :=
    hband Y hY (hYR.trans (min_le_left _ _))
  let U₀ := min Ub (min Ue (j * Real.exp (-G.outerRate * T)))
  have hU₀ : 0 < U₀ := by dsimp only [U₀]; positivity
  have hU₀e : U₀ ≤ Ue := (min_le_right _ _).trans (min_le_left _ _)
  have hU₀b : U₀ ≤ Ub := min_le_left _ _
  have hU₀T : U₀ ≤ j * Real.exp (-G.outerRate * T) := (min_le_right _ _).trans (min_le_right _ _)
  let Q := (Real.exp 2 * Ly) * Ly / (G.inner / 2) / G.innerRate
  let E₀ := 8 * B₀ + 8 * Q ^ 2 * (4 / Olo) ^ 2 * F₀
  let E₁ := 8 * B₁ + 8 * Q ^ 2 * (4 / Olo) ^ 2 * F₁
  refine ⟨max δb δe, Y, U₀, T, jr, D, η, C, E₀, E₁, F₀, F₁, Olo, Ohi, hδb.trans_le (le_max_left _ _),
    max_le hδbr hδer, ⟨hY, (hYR.trans (min_le_left _ _)).trans_lt hR.2⟩,
    hYR.trans (min_le_right _ _), hU₀,
    (hU₀b.trans hUbδ).trans (le_max_left _ _), hT, hjr, hD, hη, hC,
    by dsimp only [E₀]; positivity, by dsimp only [E₁]; positivity, hF₀, hF₁, hOlo, hOhi, ?_⟩
  intro ℓ P hP hf hfn hpoint
  let f := logarithmicIncoming b ℓ P
  let hfb := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_left δb δe)) le_rfl)
  let hfe := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_right δb δe)) le_rfl)
  have hfnb := (scalar_prefix_norm_le (le_max_left δb δe) hf).trans hfn
  have hfne := (scalar_prefix_norm_le (le_max_right δb δe) hf).trans hfn
  have hpte := ae_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_right δb δe)) le_rfl) hpoint
  obtain ⟨arrival, _hac, haa, _hal, hpos, hscale, hmatch, hpre, hchart, hgeom⟩ := hearly f hfe hfne hpte
  obtain ⟨g, hgc, hga, hgl, hdc, hstart, hgp, hphysical⟩ := hsource Olo hOlo p hp ℓ P hP hfb hfnb hkp
  have hlate (u : ℝ) (hu : u ∈ Ioc 0 U₀) : T ≤ arrival u := by
    have hh := mul_le_mul_of_nonneg_right (hu.2.trans hU₀T) (Real.exp_pos (G.outerRate * T)).le
    have hh' : u * Real.exp (G.outerRate * T) ≤ j := by
      simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] using hh
    have he : Real.exp (G.outerRate * T) ≤ Real.exp (G.outerRate * arrival u) := by
      nlinarith only [hh'.trans (hscale u ⟨hu.1, hu.2.trans hU₀e⟩).1, hu.1]
    nlinarith only [Real.exp_le_exp.1 he, G.outerRate_pos]
  have hα : 0 < 1 + β := by linarith only [hβ]
  refine ⟨g, hgc, hga, hgl, hdc, hU₀b.trans_lt hstart, hgp, ?_⟩
  intro U V hU hV hUR hUU hfU x hx
  obtain ⟨w, hw0, S, hw, hwa, hS0, hbandE, hlevel, hidentify, hnuY, htraceE, hSE, hS⟩ :=
    hphysical U V hU hV hUR (hUU.trans hU₀b) hfU x hx
  let W : C(Icc 0 V, ℝ) := ⟨fun v => w (projIcc 0 V hV ((v : ℝ) / (1 + β))), by fun_prop⟩
  have hW0 (v) : 0 ≤ W v := hw0 _
  let M := movingSpatialRadiationEnvelope W hW0 0 G.innerRate 0 x
  let l : Icc 0 V := projIcc 0 V hV (arrival U)
  have hUgT : U ≤ g T := ((hUU.trans hU₀b).trans_lt hstart).le
  have hentry (u : Icc 0 U) (hu : 0 < (u : ℝ)) (a : Icc 0 V) (ha : (a : ℝ) = arrival u) :
      x.1 u a 0 = Y ∧ x.2.1 u a 0 < 0 ∧ g a = u := by
    have hm := hmatch U V hU hV hUR hfU hx (hUU.trans hU₀e) u hu a ha
    have ht : x.2.1 u a 0 < 0 := by
      have hh := (mul_pos hOlo hu).trans_le hm.2.2.1
      exact neg_pos.1 ((div_pos_iff.mp hh).resolve_right
        (by intro hn; exact (Real.exp_pos _).not_gt hn.2)).1
    exact ⟨hm.2.2.2.2.1, ht, hidentify u a hu hm.2.2.2.2.1 ht⟩
  have hafter (u : Icc 0 U) (v : Icc 0 V) (hwu : w v < (u : ℝ)) :
      T ≤ v ∧ 0 < (u : ℝ) ∧ arrival u ≤ v := by
    have hTv : T ≤ (v : ℝ) := by
      by_contra hn
      have hh : w v = g T := by rw [hw, max_eq_left (not_le.1 hn).le]
      linarith only [hUgT, u.property.2, hwu, hh]
    have hwb : w v = g v := by rw [hw, max_eq_right hTv]
    have hu : 0 < (u : ℝ) := (hw0 v).trans_lt hwu
    have huE : (u : ℝ) ∈ Ioc 0 Ue := ⟨hu, (u.property.2.trans hUU).trans hU₀e⟩
    have hgu : g v < (u : ℝ) := hwb ▸ hwu
    have hgv : g v ∈ Icc 0 U := ⟨(hgp v hTv).1.le, hgu.le.trans u.property.2⟩
    have hav : arrival u ≤ v := by
      by_contra hn
      have hrY := hpre hU.le hV hUR hfU hx u huE u le_rfl v (not_le.1 hn).le
      have hrad := hlevel v hTv hgv.2
      rw [projIcc_of_mem hU.le hgv] at hrad
      have hanti := hx.radial_strictAnti hx.choose rfl
        (incomingWave_constraint_data hU.le hUR hp hfU (horizonPhi h r 0)).1 v
        (fun q => (hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU q v).2.2.1)
      have hlt := hanti (show (⟨g v, hgv⟩ : Icc 0 U) < u from hgu)
      linarith only [hrY, hrad, hlt]
    exact ⟨hTv, hu, hav⟩
  have hentered (u : Icc 0 U) (v : Icc 0 V) (hwu : w v < (u : ℝ)) (huW : (u : ℝ) ≤ W v) :
      T ≤ v ∧ 0 < (u : ℝ) ∧ arrival u ≤ v ∧ (v : ℝ) ≤ (1 + β) * arrival u := by
    obtain ⟨hTv, hu, hav⟩ := hafter u v hwu
    have huE : (u : ℝ) ∈ Ioc 0 Ue := ⟨hu, (u.property.2.trans hUU).trans hU₀e⟩
    let a : Icc 0 V := ⟨arrival u, (hpos u huE).le, hav.trans v.property.2⟩
    have hgaU := (hentry u hu a rfl).2.2
    have hTa := hlate u ⟨hu, u.property.2.trans hUU⟩
    have hdivV : (v : ℝ) / (1 + β) ∈ Icc 0 V :=
      ⟨div_nonneg v.property.1 hα.le,
        (div_le_self v.property.1 (by linarith only [hβ])).trans v.property.2⟩
    have hwindow : (v : ℝ) / (1 + β) ≤ arrival u := by
      by_cases hvT : (v : ℝ) / (1 + β) ≤ T
      · exact hvT.trans hTa
      · have hWv : W v = g ((v : ℝ) / (1 + β)) := by
          simp only [W, ContinuousMap.coe_mk, projIcc_of_mem hV hdivV, hw,
            max_eq_right (not_le.1 hvT).le]
        by_contra hn
        have hh := hga hTa (not_le.1 hvT).le (not_le.1 hn)
        rw [show g (arrival u) = u from hgaU, ← hWv] at hh
        exact (not_lt_of_ge huW) hh
    exact ⟨hTv, hu, hav, by simpa only [mul_comm] using (div_le_iff₀ hα).1 hwindow⟩
  have henergy := hx.early_moving_radiation_energy hU.le hV hUR hp hfU G.innerRate_pos
    (half_pos G.inner_pos) (by positivity : 0 ≤ 2 * Real.exp 1)
    (by positivity : 0 ≤ Real.exp 2 * Ly) hLy.le
    (hsmall.le.trans (by nlinarith only [mul_nonneg (sq_nonneg G.innerRate) (sq_nonneg (G.inner / 2))]))
    (by linarith only [hβ] : 1 ≤ 1 + β) l w hw0 hwa S hS0
  have hclosed := (henergy (by
    intro u v hwu huW
    obtain ⟨hTv, hu, hav, hwindow⟩ := hentered u v hwu huW
    obtain ⟨z, hzu, T', hz, hTz, hder, hdata⟩ :=
      hchart hU hV hUR hfU hx (hUU.trans hU₀e) u v hu hav hwindow
    have hzdata := hdata z (left_mem_Icc.2 (show (z : ℝ) ≤ u from hzu))
    simp only [projIcc_of_mem hU.le z.property, hTz] at hzdata
    have hgz := hidentify z v hz hzdata.2.2.1 hzdata.2.2.2.2.2.1
    have hlu := monotone_projIcc hV
      (hdata u (right_mem_Icc.2 (show (z : ℝ) ≤ u from hzu))).2.2.2.2.2.2.2.1
    refine ⟨z, hzu, T', by rw [hw, max_eq_right hTv, hgz], hTz,
      by simpa only [projIcc_of_mem hV (T' (projIcc (z : ℝ) u hzu u)).property] using hlu,
      (fun t ht => (hdata t ht).2.1), (fun t ht => (hdata t ht).2.2.2.1),
      (fun t ht => ⟨(hdata t ht).2.2.2.2.1, (hdata t ht).2.2.2.2.2.1⟩), hder,
      (fun t ht q hq => ((hdata t ht).2.2.2.2.2.2.2.2 q hq).1),
      (fun t ht q hq => by simpa only [neg_mul] using ((hdata t ht).2.2.2.2.2.2.2.2 q hq).2.1),
      (fun t ht => by simpa only [neg_mul] using
        ((hdata t ht).2.2.2.2.2.2.2.2 v (right_mem_Icc.2 (hdata t ht).2.1)).2.2), ?_⟩
    filter_upwards [hS] with t ht
    intro htz
    obtain ⟨_heq, _htv, hrY, _hn, _hlo, hlam, hO, hlt, _hhist⟩ := hdata t htz
    exact ht _ ((hlate U ⟨hU, hUU⟩).trans hlt) (hz.trans_le htz.1) hrY hlam hO)).2.2.2
  have hbandE' : (∫ t in (0 : ℝ)..V,
      (movingSpatialRadiationEnvelope w hw0 0 G.innerRate 0 x (projIcc 0 V hV t)) ^ 2) ≤
        B₀ + B₁ * ∫ t, P t ^ 2 := by
    simpa only [movingSpatialRadiationEnvelope, movingSpatialRadiationRows, zero_mul, sub_zero] using hbandE
  have hsourceE : (∫ t in (l : ℝ)..V, (S (projIcc 0 V hV t)) ^ 2) ≤
      (4 / Olo) ^ 2 * (F₀ + F₁ * ∫ t, P t ^ 2) := by
    by_cases haV : arrival U ≤ V
    · have ha : arrival U ∈ Icc 0 V := ⟨(hpos U ⟨hU, hUU.trans hU₀e⟩).le, haV⟩
      have hgaU := (hentry ⟨U, hU.le, le_rfl⟩ hU ⟨arrival U, ha⟩ rfl).2.2
      simpa only [l, projIcc_of_mem hV ha] using
        hSE (arrival U) V (hlate U ⟨hU, hUU⟩) haV le_rfl hgaU.le
    · simp only [l, projIcc_of_right_le hV (not_le.1 haV).le, intervalIntegral.integral_same]
      exact mul_nonneg (sq_nonneg _) (add_nonneg hF₀
        (mul_nonneg hF₁ (integral_nonneg (fun t => sq_nonneg (P t)))))
  have hfc : ContinuousOn f (Ioi 0) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.mul (continuousOn_id.rpow_const (fun u hu => Or.inl hu.ne'))
    · exact P.continuous.comp_continuousOn
        (continuousOn_const.sub (continuousOn_id.log (fun u hu => hu.ne')))
  have hif : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hfU u 1 = f u := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hfU] with u hu
    rw [hu]
    rfl
  let Z := fun t v : ℝ => g t * Real.exp (G.innerRate * t) *
    (intervalExtension hV (intervalExtension hU.le x.1 (g t)) v 0 *
      derivWithin (fun u => intervalExtension hV (intervalExtension hU.le x.1 u) v 1)
        (Icc 0 U) (g t))
  have hME : (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
      E₀ + E₁ * ∫ t, P t ^ 2 :=
    (hclosed.trans (add_le_add (mul_le_mul_of_nonneg_left hbandE' (by norm_num))
      (mul_le_mul_of_nonneg_left hsourceE (by positivity)))).trans_eq (by dsimp only [E₀, E₁, Q]; ring)
  have hmatchingTime (t : ℝ) (hTt : T ≤ t) (hgtU : g t ≤ U) (htV : t < V) :
      arrival (projIcc 0 U hU.le (g t)) = t := by
    have ht0 := hT.trans_le hTt
    have hgt := (hgp t hTt).1
    let u : Icc 0 U := ⟨g t, hgt.le, hgtU⟩
    have hat : arrival u ≤ t := by
      by_contra hn
      let v := (t + min (arrival u) V) / 2
      have hvlo : t < v := by
        have hh := lt_min (not_le.1 hn) htV
        dsimp only [v]
        linarith only [hh]
      have hvhi : v < arrival u := by
        have hh := min_le_left (arrival u) V
        dsimp only [v]
        linarith only [hh, not_le.1 hn]
      have hvV : v ≤ V := by
        have hh := min_le_right (arrival u) V
        dsimp only [v]
        linarith only [hh, htV]
      have hTv : T ≤ v := hTt.trans hvlo.le
      have hh := hafter u ⟨v, ht0.le.trans hvlo.le, hvV⟩ (by
        rw [hw, max_eq_right hTv]
        exact hga hTt hTv hvlo)
      exact (not_lt_of_ge hh.2.2) hvhi
    have ha0 := hpos u ⟨hgt, (hgtU.trans hUU).trans hU₀e⟩
    have hat' : arrival u = t := hga.injOn (hlate u ⟨hgt, hgtU.trans hUU⟩) hTt
      ((hentry u hgt ⟨arrival u, ha0.le, hat.trans htV.le⟩ rfl).2.2)
    rw [show projIcc 0 U hU.le (g t) = u from projIcc_of_mem hU.le u.property]
    exact hat'
  have hoptical (t : ℝ) (hTt : T ≤ t) (hgtU : g t ≤ U) (hβpos : 0 < β)
      (hγV : (1 + β) * t ≤ V) :
      let u := projIcc 0 U hU.le (g t)
      let a := projIcc 0 V hV t
      Olo * g t ≤ -x.2.1 u a 0 / Real.exp (x.1 u a 2) ∧
      -x.2.1 u a 0 / Real.exp (x.1 u a 2) ≤ Ohi * g t ∧
      (∫ v in t..(1 + β) * t, intervalExtension hV (x.1 u) v 0 *
        (intervalExtension hV (x.2.1 u) v 1) ^ 2 /
          (-intervalExtension hV (x.2.1 u) v 0)) ≤ 1 / 16 ∧
      ∀ hr : ∀ q v, x.1 q v 0 ≠ 0,
        let ν := radialNuField hV G.charge G.cosmological
          (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hr
        ∀ a' b' : Icc 0 V, t ≤ a' → a' ≤ b' → (b' : ℝ) ≤ (1 + β) * t →
          G.inner / 2 ≤ x.1 u b' 0 ∧
          |ν u b'| ≤ (2 * Real.exp 2) * (-ν u a') * Real.exp (-2 * G.innerRate * ((b' : ℝ) - a')) ∧
          |x.2.1 u b' 0| ≤ (Real.exp (2 + 1 / 16) * (-x.2.1 u a' 0)) *
            Real.exp (-2 * G.innerRate * ((b' : ℝ) - a')) := by
    have ht0 := hT.trans_le hTt
    have htγ : t < (1 + β) * t := by nlinarith only [mul_pos hβpos ht0]
    have htV : t ∈ Icc 0 V := ⟨ht0.le, htγ.le.trans hγV⟩
    have hγmem : (1 + β) * t ∈ Icc 0 V := ⟨ht0.le.trans htγ.le, hγV⟩
    have hgt := (hgp t hTt).1
    let u : Icc 0 U := ⟨g t, hgt.le, hgtU⟩
    have hat : arrival u = t := by
      have hproj : projIcc 0 U hU.le (g t) = u := projIcc_of_mem hU.le u.property
      simpa only [hproj] using hmatchingTime t hTt hgtU (htγ.trans_le hγV)
    have hm := hmatch U V hU hV hUR hfU hx (hUU.trans hU₀e) u hgt
      (projIcc 0 V hV t) (by rw [projIcc_of_mem hV htV]; exact hat.symm)
    have hg := hgeom U V hU hV hUR hfU hx (hUU.trans hU₀e) u hgt
      ⟨(1 + β) * t, hγmem⟩ (by rw [hat])
    dsimp only
    rw [projIcc_of_mem hU.le u.property]
    refine ⟨hm.2.2.1, hm.2.2.2.1, ?_, ?_⟩
    · simpa only [hat] using (hg.2 (hat.trans_le htγ.le)).2.2.1
    · intro hr a' b' hta' ha'b' hb'γ
      have hh := hgeom U V hU hV hUR hfU hx (hUU.trans hU₀e) u hgt b' (by simpa only [hat] using hb'γ)
      exact ⟨hh.1, (hh.2 (hat.trans_le (hta'.trans ha'b'))).2.2.2 a' (hat.trans_le hta') ha'b'⟩
  have hgamma : ∀ t : ℝ, T ≤ t → g t ≤ U → (1 + β) * t ≤ V →
      |Z t ((1 + β) * t)| ≤ |Z t t| + (2 * Real.exp 1) * D / (G.inner / 2) *
        ∫ v in t..(1 + β) * t, Real.exp (-(3 * G.innerRate) * (v - t)) *
          M (projIcc 0 V hV v) := by
    dsimp only [Z]
    intro t hTt hgtU hγV
    by_cases hβ0 : β = 0
    · simp only [hβ0, add_zero, one_mul, intervalIntegral.integral_same, mul_zero, add_zero, le_refl]
    have ht0 : 0 < t := hT.trans_le hTt
    have htγ : t < (1 + β) * t := by nlinarith only [lt_of_le_of_ne hβ (Ne.symm hβ0), ht0]
    have htV : t ∈ Icc 0 V := ⟨ht0.le, htγ.le.trans hγV⟩
    have hγmem : (1 + β) * t ∈ Icc 0 V := ⟨ht0.le.trans htγ.le, hγV⟩
    have hgt : 0 < g t := (hgp t hTt).1
    let u : Icc 0 U := ⟨g t, hgt.le, hgtU⟩
    let a : Icc 0 V := ⟨t, htV⟩
    let b' : Icc 0 V := ⟨(1 + β) * t, hγmem⟩
    have hproj : projIcc 0 U hU.le (g t) = u := projIcc_of_mem hU.le u.property
    have hat' : arrival u = t := by
      simpa only [hproj] using hmatchingTime t hTt hgtU (htγ.trans_le hγV)
    let ν := radialNuField hV G.charge G.cosmological
      (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
    have hν0 := (hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU u a).2.2.1
    have hgeo (v : Icc 0 V) (hv : v ∈ Icc a b') :
        G.inner / 2 ≤ x.1 u v 0 ∧
        |ν u v| ≤ (2 * Real.exp 1) * (-ν u a) * Real.exp (-(2 * G.innerRate) * ((v : ℝ) - a)) := by
      have hh := hgeom U V hU hV hUR hfU hx (hUU.trans hU₀e) u hgt v
        (by rw [hat']; exact hv.2)
      exact ⟨hh.1, by simpa only [hat', projIcc_of_mem hV htV, neg_mul] using
        (hh.2 (hat'.trans_le hv.1)).1⟩
    have hmajor (v : Icc 0 V) (hv : v ∈ Icc a b') :
        Real.exp (G.innerRate * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v := by
      have hvdiv : (v : ℝ) / (1 + β) ∈ Icc 0 V :=
        ⟨div_nonneg v.property.1 hα.le,
          (div_le_self v.property.1 (by linarith only [hβ])).trans v.property.2⟩
      have hvdt : (v : ℝ) / (1 + β) ≤ t := (div_le_iff₀ hα).2
        (by simpa only [mul_comm] using (show (v : ℝ) ≤ (1 + β) * t from hv.2))
      have huW : (u : ℝ) ≤ W v := by
        simp only [W, ContinuousMap.coe_mk, projIcc_of_mem hV hvdiv, hw]
        exact hga.antitoneOn (show T ≤ max T ((v : ℝ) / (1 + β)) from le_max_left _ _)
          hTt (max_le hTt hvdt)
      simpa only [zero_mul, sub_zero] using
        (movingSpatialRadiationEnvelope_le_iff (a := 0) (k := G.innerRate) (σ := 0)
          hU.le W hW0 x v).1 le_rfl u huW
    have hh := hx.transverse_radiation_majorant (k := G.innerRate) (q := 2 * G.innerRate) rfl
      (incomingWave_constraint_data hU.le hUR hp hfU (horizonPhi h r 0)).1 hfc hif
      (half_pos G.inner_pos) (by positivity : 0 ≤ 2 * Real.exp 1) M u hgt a b' htγ.le
      hν0 (fun v hv => (hgeo v hv).1) (fun v hv => (hgeo v hv).2) hmajor
    have hweight : g t * (-ν u a) ≤ D := by
      have hh := hnuY a hTt hgtU
      change g t * |ν (projIcc 0 U hU.le (g t)) a| ≤ D at hh
      rw [hproj, abs_of_neg hν0] at hh
      exact hh
    have hcoef : g t * ((2 * Real.exp 1) * (-ν u a) / (G.inner / 2)) ≤
        (2 * Real.exp 1) * D / (G.inner / 2) := by
      calc
        _ = ((2 * Real.exp 1) / (G.inner / 2)) * (g t * (-ν u a)) := by ring
        _ ≤ ((2 * Real.exp 1) / (G.inner / 2)) * D :=
          mul_le_mul_of_nonneg_left hweight (div_nonneg (by positivity) (half_pos G.inner_pos).le)
        _ = _ := by ring
    have hI0 : 0 ≤ ∫ v in t..(1 + β) * t, Real.exp (-(3 * G.innerRate) * (v - t)) *
        M (projIcc 0 V hV v) := intervalIntegral.integral_nonneg htγ.le
          (fun v _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg (movingSpatialRadiationRows W hW0 0 G.innerRate 0 x _)))
    have hscaled := mul_le_mul_of_nonneg_left hh hgt.le
    rw [mul_add, ← mul_assoc (g t) ((2 * Real.exp 1) * (-ν u a) / (G.inner / 2)),
      show 2 * G.innerRate + G.innerRate = 3 * G.innerRate by ring] at hscaled
    have hfinal := hscaled.trans (add_le_add_right (mul_le_mul_of_nonneg_right hcoef hI0) _)
    simpa only [intervalExtension_apply, projIcc_of_mem hV htV, projIcc_of_mem hV hγmem,
      hproj, abs_mul, abs_of_pos hgt, abs_of_pos (Real.exp_pos _), mul_assoc] using hfinal
  refine ⟨w, hw0, hw, hwa, hlevel, hoptical, hME, htraceE, hgamma, ?_⟩
  intro l q hTl hlq hqV hglU
  have hl0 := hT.le.trans hTl
  have hq0 := hl0.trans hlq
  have hqV' : q ≤ V := (le_mul_of_one_le_left hq0 (by linarith only [hβ])).trans hqV
  have hsub : Icc l q ⊆ Ici T := fun _ ht => hTl.trans ht.1
  have hgu (t : ℝ) (ht : t ∈ Icc l q) : g t ∈ Ioc 0 U :=
    ⟨(hgp t (hsub ht)).1, (hga.antitoneOn hTl (hsub ht) ht.1).trans hglU⟩
  have hZc (v : ℝ → ℝ) (hv : ContinuousOn v (Icc l q)) :
      ContinuousOn (fun t => Z t (v t)) (Icc l q) := by
    have hh := hx.scalar_curve_continuous rfl
      (incomingWave_constraint_data hU.le hUR hp hfU (horizonPhi h r 0)).1
      hfc hif (hgc.mono hsub) hv hgu
    exact ((hgc.mono hsub).mul (by fun_prop)).mul hh
  have hbound := terminalExpIntegral_add_energy hV (mul_pos (by norm_num : (0 : ℝ) < 3) G.innerRate_pos)
    hl0 hlq hqV' M (hZc (fun t => (1 + β) * t) (by fun_prop)) (hZc id continuousOn_id)
    (C := (2 * Real.exp 1) * D / (G.inner / 2)) (fun t ht => ?_)
  · exact hbound.trans (add_le_add
      (mul_le_mul_of_nonneg_left (htraceE l q hTl hlq hqV' hglU) (by norm_num))
      (mul_le_mul_of_nonneg_left hME (by positivity)))
  · have ht0 := hl0.trans ht.1
    have htγ : t ≤ (1 + β) * t := le_mul_of_one_le_left ht0 (by linarith only [hβ])
    have hγV := (mul_le_mul_of_nonneg_left ht.2 hα.le).trans hqV
    have hkernel := intervalIntegral.integral_mono_interval le_rfl htγ hγV
      (Filter.Eventually.of_forall (fun v => mul_nonneg (Real.exp_pos _).le
        (norm_nonneg (movingSpatialRadiationRows W hW0 0 G.innerRate 0 x _))))
      (by apply Continuous.intervalIntegrable; fun_prop :
        IntervalIntegrable (fun v => Real.exp (-(3 * G.innerRate) * (v - t)) *
          M (projIcc 0 V hV v)) volume t V)
    exact (hgamma t (hsub ht) (hgu t ht).2 hγV).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hkernel
        (div_nonneg (by positivity) (half_pos G.inner_pos).le)) _)


end CauchyHorizon.Background
