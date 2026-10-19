import CauchyHorizon.Characteristic.EarlyClosure

/-! Actual unique physical prefixes extend through the full early-inner window. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_early_wave (B : Background) {s H dH A Apt c ε d β : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hApt : 0 ≤ Apt) (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    (hε : 0 < ε) (hεk : ε < B.innerRate) (hd : 0 < d) (hβ : 0 ≤ β)
    (hℓ : c < 2 * (B.innerRate - ε) - d)
    (hJ : 0 < 2 * c - max 0 (2 * (B.innerRate + ε) + d - 2 * c) * β)
    (hQ : 0 < 2 * c - 2 * (B.innerRate + ε) * β)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hcb : c ≤ B.outerRate * (1 - 1 / p.toReal))
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Δ Y U₀ He C η qR Lk LF j D Olo Ohi : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ 0 < Δ ∧ Δ ≤ B.inner / 4 ∧
      (∀ r ∈ Icc (B.inner - Δ) (B.inner + Δ), B.innerRate / 4 ≤ radialPotential r B.charge B.cosmological) ∧
      B.inner < Y ∧ Y ≤ B.inner + Δ / 2 ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ U₀ ≤ 1 ∧
      0 < He ∧ 0 < C ∧ 0 < η ∧ 0 < qR ∧ 0 < Lk ∧ 0 < LF ∧ 0 < j ∧ 0 < D ∧ 0 < Olo ∧ 0 < Ohi ∧
      ∀ f : ℝ → ℝ, MemLp f p (volume.restrict (Icc 0 δ)) →
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        (∀ᵐ t ∂volume.restrict (Icc 0 δ), |f t| ≤ Apt * t ^ (-1 / p.toReal)) →
        ∃ arrival : ℝ → ℝ, ContinuousOn arrival (Ioc 0 U₀) ∧ StrictAntiOn arrival (Ioc 0 U₀) ∧
          Tendsto arrival (𝓝[>] (0 : ℝ)) atTop ∧ (∀ u ∈ Ioc 0 U₀, 0 < arrival u) ∧
          (∀ u ∈ Ioc 0 U₀, j ≤ u * Real.exp (B.outerRate * arrival u) ∧
            u * Real.exp (B.outerRate * arrival u) ≤ D) ∧
          (∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V},
            IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x → U ≤ U₀ →
              ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V, (v : ℝ) = arrival u →
                Olo ≤ (u : ℝ) * Real.exp (x.1 u v 2) ∧ (u : ℝ) * Real.exp (x.1 u v 2) ≤ Ohi ∧
                Olo * (u : ℝ) ≤ -x.2.1 u v 0 / Real.exp (x.1 u v 2) ∧
                -x.2.1 u v 0 / Real.exp (x.1 u v 2) ≤ Ohi * (u : ℝ) ∧ x.1 u v 0 = Y) ∧
          (∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
            (_hx : IsWaveIntegral hU hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x) (u : ℝ), u ∈ Ioc 0 U₀ →
            ∀ q : Icc 0 U, (q : ℝ) ≤ u → ∀ v : Icc 0 V, (v : ℝ) ≤ arrival u → Y ≤ x.1 q v 0) ∧
          (∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V},
            IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x → U ≤ U₀ →
              ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V,
                0 < t → arrival t ≤ b → (b : ℝ) ≤ (1 + β) * arrival t →
                  |x.2.2 t b 1| ≤ C * |f t| + C * t ^ (-1 + c / B.outerRate)) ∧
          (∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V},
            IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x → U ≤ U₀ → V ≤ (1 + β) * arrival U →
              ∀ q v, 3 * B.inner / 4 ≤ x.1 q v 0) ∧
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))), U ≤ U₀ → V ≤ (1 + β) * arrival U →
            ∃! x : WaveState U V, ∃ hx : IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x,
              (∀ q v, 3 * B.inner / 4 ≤ x.1 q v 0) ∧
              (arrival U ≤ V →
                let u : Icc 0 U := ⟨U, hU.le, le_rfl⟩
                let v : Icc 0 V := ⟨V, hV, le_rfl⟩
                let ν := radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
                let K := horizonK (x.1 u v 0) (m u v) B.charge B.cosmological
                Real.exp (c * V) * |x.2.1 u v 1| ≤ He / 2 ∧
                  |x.1 u v 0 - B.inner| ≤ Δ / 2 ∧ |m u v - B.mass| ≤ Δ / 2 ∧
                  3 * B.inner / 4 ≤ x.1 u v 0 ∧ |K + B.innerRate| ≤ ε / 2 ∧
                  3 / 4 ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧ |x.2.1 u v 2 - 2 * K| ≤ d / 2 ∧
                  (V = (1 + β) * arrival U → -ν u v ≤
                    He * U ^ (-1 + (2 * (2 / 3) * (B.innerRate - ε) / B.outerRate) * β)) ∧
                  (∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V, 0 < t → arrival t ≤ b →
                    |x.2.2 t b 1| ≤ C * |f t| + C * t ^ (-1 + c / B.outerRate)) ∧
                  |(-Real.exp (x.1 u v 2) / (4 * ν u v)) - 1| + |x.2.1 u v 2 - 2 * K| ≤
                    C * Real.exp (-η * V) ∧
                  |m u v - B.mass| ≤ C * (1 + β * arrival U) * Real.exp (-η * arrival U) ∧
                  let J := ∫ t in arrival U..V, intervalExtension hV (x.1 u) t 0 *
                    (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)
                  0 ≤ J ∧ J ≤ C * β * arrival U *
                    Real.exp (-(2 * c - max 0 (2 * (B.innerRate + ε) + d - 2 * c) * β) * arrival U) ∧
                  |x.1 u v 0 - B.inner| ≤ (Y - B.inner) * Real.exp (-qR * (V - arrival U)) +
                    ((4 / B.inner) * (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) / qR ∧
                  (∫ t in arrival U..V, |intervalExtension hV (x.1 u) t 0 - B.inner|) ≤
                    ((Y - B.inner) + (4 / B.inner) * (β * arrival U) *
                      (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) / qR ∧
                  |K + B.innerRate| ≤ Lk * ((Y - B.inner) * Real.exp (-qR * (V - arrival U)) +
                    (1 + 4 / B.inner / qR) * (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) ∧
                  (∫ t in arrival U..V, |horizonK (intervalExtension hV (x.1 u) t 0)
                    (intervalExtension hV (m u) t) B.charge B.cosmological + B.innerRate|) ≤
                    Lk * ((Y - B.inner) / qR + (1 + 4 / B.inner / qR) * (β * arrival U) *
                      (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) ∧
                  let R := x.1 u v 2 - x.1 u (projIcc 0 V hV (arrival U)) 2 +
                    2 * B.innerRate * (V - arrival U)
                  |R| ≤ C / η * Real.exp (-η * arrival U) +
                    2 * (Lk * ((Y - B.inner) / qR + (1 + 4 / B.inner / qR) * (β * arrival U) *
                      (C * (1 + β * arrival U) * Real.exp (-η * arrival U)))) ∧
                  Real.exp (x.1 u v 2) = Real.exp (x.1 u (projIcc 0 V hV (arrival U)) 2) *
                    Real.exp (-2 * B.innerRate * (V - arrival U) + R) ∧
                  (0 < β → V = (1 + β) * arrival U →
                    let ηg := min (η / 2) (qR * β) / (1 + β)
                    0 < ηg ∧ |x.2.1 u v 2 + 2 * B.innerRate| ≤
                      (C + 2 * Lk * ((Y - B.inner) +
                        (1 + 4 / B.inner / qR) * (C * (1 + 2 * β / η)))) * Real.exp (-ηg * V) ∧
                      |x.2.1 u v 0| ≤ (LF * ((Y - B.inner) +
                        (1 + 4 / B.inner / qR) * (C * (1 + 2 * β / η)))) * Real.exp (-ηg * V))) ∧
              (∃ H : ℝ, ∃ hH : 0 < H, ∃ y : WaveState U (V + H),
                IsWaveIntegral hU.le (add_nonneg hV hH.le) B.charge B.cosmological
                  (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological (V + H) hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) y ∧
                waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp)
                  le_rfl (by linarith) y = x ∧ ∀ q v, 3 * B.inner / 8 ≤ y.1 q v 0) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have hrp := B.inner_pos.trans hrinit
  have hρ : 0 < 3 * B.inner / 4 := by linarith only [B.inner_pos]
  obtain ⟨δ, Δ, Y, Ue, He, C, η, qR, Lk, LF, j, D, Olo, Ohi, _Ly,
    hδ, hδr, hΔ, hΔr, hpot, hY, hYΔ, _hYcap, _hYclose, hUe, hUeδ,
    hHe, hC, hη, hqR, hLk, hLF, hj, hD, hOlo, hOhi, _hLy, _hLycap, hsolve⟩ :=
    B.exists_early_bounds hs hH hdH hdHR hA hApt hc0 hca hcs hε hεk hd hβ
      hℓ hJ hQ hp hcb hc hb hrc hrb hrinit hrd hrdec hOut B.event B.inner_lt_event
  obtain ⟨d₀, hd₀, _hd₀r, hd₀1, hstart⟩ :=
    exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0 hrp hφ hrd A hA
  let U₀ := min Ue d₀
  have hU₀ : 0 < U₀ := lt_min hUe hd₀
  have hUδ : U₀ ≤ δ := (min_le_left _ _).trans hUeδ
  have hU1 : U₀ ≤ 1 := (min_le_right _ _).trans hd₀1
  refine ⟨δ, Δ, Y, U₀, He, C, η, qR, Lk, LF, j, D, Olo, Ohi, hδ, hδr, hΔ, hΔr, hpot, hY, hYΔ, hU₀, hUδ, hU1,
    hHe, hC, hη, hqR, hLk, hLF, hj, hD, hOlo, hOhi, ?_⟩
  intro f hf hfn hpoint
  obtain ⟨arrival, hac, haa, hal, hpos, hscale, hmatch, hpre, _hchart, hhistory, hbound⟩ := hsolve f hf hfn hpoint
  have hsub : Ioc 0 U₀ ⊆ Ioc 0 Ue := Ioc_subset_Ioc le_rfl (min_le_left _ _)
  have hfloor (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x) (hUU : U ≤ U₀) (hwindow : V ≤ (1 + β) * arrival U)
      (q : Icc 0 U) (v : Icc 0 V) : 3 * B.inner / 4 ≤ x.1 q v 0 := by
    by_cases hv : (v : ℝ) ≤ arrival U
    · have hh := hpre hU.le hV hUR hfU hx U (hsub ⟨hU, hUU⟩) q q.property.2 v hv
      linarith only [hh, hY, B.inner_pos]
    · have hy := hx.horizon_prefix hU.le hV hUR hU.le v.property.1 le_rfl v.property.2 hc hi hrc hr0 hp hfU
      have hh := hbound U v hU v.property.1 hUR hfU hy (hUU.trans (min_le_left _ _))
        (not_le.1 hv).le (v.property.2.trans hwindow)
      have hr := hh.2.2.2.1
      have he := hy.horizon_overlap hU.le v.property.1 hUR hU.le hV hUR hc hi hrc hr0 hp hfU hfU hx
        (show U ∈ Icc 0 U from ⟨hU.le, le_rfl⟩) ⟨hU.le, le_rfl⟩
        (show (v : ℝ) ∈ Icc 0 (v : ℝ) from ⟨v.property.1, le_rfl⟩) v.property
      rw [he.1] at hr
      have hanti := hx.radial_strictAnti hx.choose rfl
        (incomingWave_constraint_data hU.le hUR hp hfU (horizonPhi h r 0)).1 v
        (fun w => (hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU w v).2.2.1)
      exact hr.trans (hanti.antitone (show q ≤ (⟨U, hU.le, le_rfl⟩ : Icc 0 U) from q.property.2))
  refine ⟨arrival, hac.mono hsub, haa.mono hsub, hal, fun u hu => hpos u (hsub hu),
    (fun u hu => hscale u (hsub hu)),
    (fun U V hU hV hUR hfU {x} hx hUU u hu v hv => by
      have hm := hmatch U V hU hV hUR hfU hx (hUU.trans (min_le_left _ _)) u hu v hv
      exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1⟩),
    (fun {_ _} hU hV hUR hfU {_} hx u hu => hpre hU hV hUR hfU hx u (hsub hu)),
    fun U V hU hV hUR hfU {x} hx hUU =>
      hhistory U V hU hV hUR hfU hx (hUU.trans (min_le_left _ _)), hfloor, ?_⟩
  intro U V hU hV hUR hfU hUU hwindow
  have hfnU := (scalar_prefix_norm_le (hUU.trans hUδ) hf).trans hfn
  obtain ⟨step, hstep, _hstep1, hext⟩ := exists_horizon_row_extension hV hrp hc hi hrc hr0 hφ hrd hρ hA
  let P := fun t : ℝ => ∃ ht : 0 ≤ t, ∃ x : WaveState U t,
    IsWaveIntegral hU.le ht B.charge B.cosmological
      (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological t hc hi hrc hr0)
      (incomingWaveVelocity hUR hp hfU) x
  have hbase : P 0 := by
    obtain ⟨x, hx, _⟩ := hstart hU.le le_rfl hUR (hUU.trans (min_le_right _ _)) hd₀.le hp hfU hfnU
    exact ⟨le_rfl, x, hx⟩
  have hnext (t w : ℝ) (_ht : 0 ≤ t) (hw : 0 ≤ w) (htw : t + w ≤ V) (hws : w ≤ step)
      (htP : P t) : P (t + w) := by
    obtain ⟨ht, x, hx⟩ := htP
    have htwnd : t ≤ (1 + β) * arrival U := (by linarith only [htw, hw] : t ≤ V).trans hwindow
    obtain ⟨y, hy, _hmatch, _hfloor⟩ := hext hU.le ht hw (hUU.trans hU1) hws htw hUR hp hfU hfnU hx
      (hfloor U t hU ht hUR hfU hx hUU htwnd)
    exact ⟨add_nonneg ht hw, y, hy⟩
  obtain ⟨_hV, x, hx⟩ := interval_subdivision_induction hV hstep hbase hnext
  obtain ⟨H, hH, hH1, hmore⟩ := exists_horizon_row_extension
    (show 0 ≤ V + 1 by linarith only [hV]) hrp hc hi hrc hr0 hφ hrd hρ hA
  obtain ⟨y, hy, hmatch, hyr⟩ := hmore hU.le hV hH.le (hUU.trans hU1) le_rfl
    (add_le_add le_rfl hH1) hUR hp hfU hfnU hx (hfloor U V hU hV hUR hfU hx hUU hwindow)
  refine ⟨x, ⟨hx, hfloor U V hU hV hUR hfU hx hUU hwindow,
    (fun he => hbound U V hU hV hUR hfU hx (hUU.trans (min_le_left _ _)) he hwindow),
    ⟨H, hH, y, hy, hmatch, fun q v => by
      simpa only [div_div, show (4 : ℝ) * 2 = 8 by norm_num] using hyr q v⟩⟩, ?_⟩
  intro y hy
  exact hy.choose.incoming_unique hU.le hV hUR hp hfU hx

end CauchyHorizon.Background
