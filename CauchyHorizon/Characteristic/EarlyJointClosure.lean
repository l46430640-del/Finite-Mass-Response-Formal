import CauchyHorizon.Characteristic.InnerParameters
import CauchyHorizon.Characteristic.BandRow
import CauchyHorizon.Characteristic.MatchingSpeed
import CauchyHorizon.Characteristic.EarlyGeometryClosure
import CauchyHorizon.Characteristic.EarlyFeedback
import CauchyHorizon.Characteristic.MatchingConformal
import CauchyHorizon.Analysis.ArrivalPower
import CauchyHorizon.Characteristic.RadialDamping

/-! One profile-independent choice gives simultaneous strict early-region improvements. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 2400000 in
theorem exists_early_joint_improvement (B : Background) {s H dH A Apt c ε d β : ℝ}
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
    (hOut : B.OutgoingEstimates h r s) (Ycap : ℝ) (hYcap : B.inner < Ycap) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Δ Y U₀ He C η qR Lk j D Olo Ohi Ly : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ 0 < Δ ∧ Δ ≤ B.inner / 4 ∧
      (∀ r ∈ Icc (B.inner - Δ) (B.inner + Δ), B.innerRate / 4 ≤ radialPotential r B.charge B.cosmological) ∧
      B.inner < Y ∧ Y ≤ B.inner + Δ / 2 ∧ Y ≤ Ycap ∧ 2 * Lk * (Y - B.inner) / qR ≤ 1 / 2 ∧
      0 < U₀ ∧ U₀ ≤ δ ∧
      0 < He ∧ 0 < C ∧ 0 < η ∧ 0 < qR ∧ 0 < Lk ∧ 0 < j ∧ 0 < D ∧ 0 < Olo ∧ 0 < Ohi ∧
      0 < Ly ∧ Ly ≤ B.innerRate * (B.inner / 2) / Real.exp 2 ∧
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
                -x.2.1 u v 0 / Real.exp (x.1 u v 2) ≤ Ohi * (u : ℝ) ∧
                x.1 u v 0 = Y ∧ -x.2.1 u v 0 ≤ Ly) ∧
          (∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
            (_hx : IsWaveIntegral hU hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x) (u : ℝ), u ∈ Ioc 0 U₀ →
            ∀ q : Icc 0 U, (q : ℝ) ≤ u → ∀ v : Icc 0 V, (v : ℝ) ≤ arrival u → Y ≤ x.1 q v 0) ∧
          (∀ {U V : ℝ} (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
            (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x), U ≤ U₀ →
            ∀ (u : Icc 0 U) (b : Icc 0 V), 0 < (u : ℝ) → arrival u ≤ b →
              ∃ (z : Icc 0 U) (hzu : z ≤ u) (T : C(Icc (z : ℝ) u, Icc 0 V)),
                0 < (z : ℝ) ∧
                let τ := fun t => T (projIcc (z : ℝ) u hzu t)
                let ν := radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                τ z = b ∧
                (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
                  (-ν (projIcc 0 U hU.le t) (τ t) / x.2.1 (projIcc 0 U hU.le t) (τ t) 0) t) ∧
                ∀ t ∈ Icc (z : ℝ) u, (τ t : ℝ) = arrival t ∧ τ t ≤ b) ∧
          (∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
            (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x), U ≤ U₀ →
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
            let K := fun w t => horizonK (x.1 w t 0)
              (massField B.charge B.cosmological x.1 x.2.1 ν hx.choose w t) B.charge B.cosmological
            (∀ w : Icc 0 U, 0 < (w : ℝ) → ∀ t : Icc 0 V,
              arrival w ≤ t → (t : ℝ) ≤ (1 + β) * arrival w →
                B.inner / 2 ≤ x.1 w t 0 ∧ |x.2.1 w t 1| ≤ He * Real.exp (-c * t) ∧
                2 / 3 ≤ -Real.exp (x.1 w t 2) / (4 * ν w t) ∧ |K w t + B.innerRate| ≤ ε) →
              ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V,
                0 < t → arrival t ≤ b → (b : ℝ) ≤ (1 + β) * arrival t →
                  |x.2.2 t b 1| ≤ C * |f t| + C * t ^ (-1 + c / B.outerRate)) ∧
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
            (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x), U ≤ U₀ → arrival U ≤ V → V ≤ (1 + β) * arrival U →
            let u : Icc 0 U := ⟨U, hU.le, le_rfl⟩
            let v : Icc 0 V := ⟨V, hV, le_rfl⟩
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
            let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
            let K := fun w t => horizonK (x.1 w t 0) (m w t) B.charge B.cosmological
            (V = arrival U → B.inner / 2 < x.1 u v 0 ∧
              Real.exp (c * V) * |x.2.1 u v 1| < He ∧
              2 / 3 < -Real.exp (x.1 u v 2) / (4 * ν u v) ∧
              |K u v + B.innerRate| < ε ∧ |x.2.1 u v 2 - 2 * K u v| < d) ∧
            ((∀ w : Icc 0 U, 0 < (w : ℝ) → ∀ t : Icc 0 V, arrival w ≤ t →
              B.inner / 2 ≤ x.1 w t 0 ∧ |x.2.1 w t 1| ≤ He * Real.exp (-c * t) ∧
              2 / 3 ≤ -Real.exp (x.1 w t 2) / (4 * ν w t) ∧
              |K w t + B.innerRate| ≤ ε ∧ |x.2.1 w t 2 - 2 * K w t| ≤ d) →
              Real.exp (c * V) * |x.2.1 u v 1| ≤ He / 2 ∧
              |x.1 u v 0 - B.inner| ≤ Δ / 2 ∧ |m u v - B.mass| ≤ Δ / 2 ∧
              3 * B.inner / 4 ≤ x.1 u v 0 ∧ |K u v + B.innerRate| ≤ ε / 2 ∧
              3 / 4 ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧ |x.2.1 u v 2 - 2 * K u v| ≤ d / 2 ∧
              (V = (1 + β) * arrival U → -ν u v ≤
                He * U ^ (-1 + (2 * (2 / 3) * (B.innerRate - ε) / B.outerRate) * β)) ∧
              (∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V, 0 < t → arrival t ≤ b →
                |x.2.2 t b 1| ≤ C * |f t| + C * t ^ (-1 + c / B.outerRate)) ∧
              |(-Real.exp (x.1 u v 2) / (4 * ν u v)) - 1| + |x.2.1 u v 2 - 2 * K u v| ≤
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
              |K u v + B.innerRate| ≤ Lk * ((Y - B.inner) * Real.exp (-qR * (V - arrival U)) +
                (1 + 4 / B.inner / qR) * (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) ∧
              (∫ t in arrival U..V, |horizonK (intervalExtension hV (x.1 u) t 0)
                (intervalExtension hV (m u) t) B.charge B.cosmological + B.innerRate|) ≤
                Lk * ((Y - B.inner) / qR + (1 + 4 / B.inner / qR) * (β * arrival U) *
                  (C * (1 + β * arrival U) * Real.exp (-η * arrival U)))) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨_Lh, _hLh, hHrad⟩ := B.horizon_radius_lambda_bounds hs hH hdH hdHR hb hrdec
  have hrinit0 := B.inner_pos.trans hrinit
  let ρ := B.inner / 2
  have hρ : 0 < ρ := half_pos B.inner_pos
  have hρR : ρ ≤ B.event + dH := by dsimp only [ρ]; linarith only [B.inner_lt_event, B.inner_pos, hdH]
  obtain ⟨Lk, hLk, hKlip⟩ := B.exists_inner_K_lipschitz
  obtain ⟨qR, hqR, hrestoring⟩ := B.exists_inner_radius_damping (by norm_num : (0 : ℝ) < 2 / 3)
  obtain ⟨Δ, hΔ, hΔr, hΔe, hpot, hmass⟩ :=
    B.exists_early_radius_mass_improvement (β := β) hε (by norm_num : (0 : ℝ) < 2 / 3) hc0
  obtain ⟨δ, R, hδ, hδr, hR, _hRr, hrows⟩ :=
    B.exists_band_row_charts hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨Ls, hLs, hsmall₀⟩ := exists_small_scalar_speed hρ
    (by positivity : 0 < 2 * (2 / 3) * (B.innerRate - ε) + c) (sub_pos.2 hℓ)
  let L := min Ls (B.innerRate * ρ / Real.exp 2)
  have hL : 0 < L := lt_min hLs (div_pos (mul_pos B.innerRate_pos hρ) (Real.exp_pos _))
  have hsmall : Real.exp 1 * L ^ 2 / (ρ ^ 2 * (2 * (B.innerRate - ε) - d - c) *
      (2 * (2 / 3) * (B.innerRate - ε) + c)) ≤ 1 / 4 := by
    apply le_trans ?_ hsmall₀
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hL.le hLs.le).2 (min_le_left _ _)) (Real.exp_pos _).le)
      (mul_nonneg (mul_nonneg (sq_nonneg ρ) (sub_pos.2 hℓ).le) (by positivity))
  let Rcap := min (min R (B.inner + Δ / 2)) (min Ycap (B.inner + qR / (4 * Lk)))
  have hRcap : B.inner < Rcap := lt_min (lt_min hR.1 (by linarith only [hΔ]))
    (lt_min hYcap (by have hh := div_pos hqR (mul_pos (by norm_num : (0 : ℝ) < 4) hLk); linarith only [hh]))
  obtain ⟨Y, hY, hspeed⟩ := B.exists_small_matching_speed (R := Rcap)
    hRcap (((min_le_left _ _).trans (min_le_left _ _)).trans hR.2.le) hL
  have hYR : Y ≤ R := hY.2.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hYΔ : Y ≤ B.inner + Δ / 2 := hY.2.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hYcap' : Y ≤ Ycap := hY.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hYclose : 2 * Lk * (Y - B.inner) / qR ≤ 1 / 2 := by
    have hh : Y ≤ B.inner + qR / (4 * Lk) :=
      hY.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hLk)).1
      (show Y - B.inner ≤ qR / (4 * Lk) by linarith only [hh])
    apply (div_le_iff₀ hqR).2
    nlinarith only [hh']
  have hY0 := B.inner_pos.trans hY.1
  obtain ⟨σ, j, D, n, N, Lband, E, l, Cerr, Tband,
    hσ, hσδ, hj, hD, hn, hN, hLband, hE, hl, hCerr, _hTband, hglobal⟩ := hrows Y hY.1 hYR
  let γ := min B.outerRate (2 * c)
  have hγ : 0 < γ := lt_min B.outerRate_pos (by positivity)
  obtain ⟨Tspeed, _hTspeed, hvel⟩ := hspeed Cerr γ hγ
  let q := 2 * (2 / 3) * (B.innerRate - ε)
  let Cν := N * D * j ^ (-(q / B.outerRate * β))
  let E₀ := max E Cν
  have hE₀ : 0 ≤ E₀ := hE.trans (le_max_left _ _)
  obtain ⟨He, Ts, hHe, hE₀He, hTs, hscalar⟩ := exists_early_scalar_improvement
    (a := B.outerRate) (k := B.innerRate) (ε := ε) (d := d) (κ₀ := 2 / 3) (ρ := ρ)
    (R := Y) (n := n) (N := N) (E := E₀) (D := D) (A := Apt) (H := Y * E) (L := L) (l := l) (β := β)
    hc hi hrc hr0 hrinit0 hφ hrd hp hc0.le hca hcb (by norm_num) hε.le hεk
    hρ hn hN.le hE₀ hD.le hApt (mul_nonneg hY0.le hE) hL.le hl hℓ hJ hsmall
  have hEHe : E < He := (le_max_left _ _).trans_lt hE₀He
  have hCνHe : Cν ≤ He := (le_max_right _ _).trans hE₀He.le
  let Ch := (N * He / ρ) * (1 / (B.outerRate - c) + 1 / (q + c)) * D ^ (1 - c / B.outerRate)
  obtain ⟨Tm, hTm, hmasslate⟩ := hmass He Cerr γ hHe.le hγ
  obtain ⟨Uc, Cc, hUc, _hUcr, hCc, hconf⟩ := B.exists_bounded_width_conformal_decay
    hs hH hdH hdHR hA hρ hρR hD.le hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  have hentrylim : Tendsto (fun t : ℝ => (Cerr + Cc) * Real.exp (-γ * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq, mul_zero] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hγ))).const_mul (Cerr + Cc)
  obtain ⟨Ti, hentryerr⟩ := eventually_atTop.1 (hentrylim.eventually_lt_const
    (lt_min (by norm_num : (0 : ℝ) < 1 / 8) (half_pos hd)))
  have hα : 0 < 1 + β := by linarith only [hβ]
  let ω := B.outerRate / (1 + β)
  let g := 2 * (B.innerRate + ε) * β / (1 + β)
  have hmargin : 0 < 2 * ω * (c / B.outerRate) - g := by
    have he : 2 * ω * (c / B.outerRate) - g = (2 * c - 2 * (B.innerRate + ε) * β) / (1 + β) := by
      dsimp only [ω, g]
      field_simp [B.outerRate_pos.ne', hα.ne']
    rw [he]
    exact div_pos hQ hα
  let η := min γ (min (2 * ω * (1 - 1 / p.toReal) - g) (2 * ω * (c / B.outerRate) - g))
  have hη : 0 < η := by
    have hcξ : c / B.outerRate ≤ 1 - 1 / p.toReal :=
      (div_le_iff₀ B.outerRate_pos).2 (by simpa only [mul_comm] using hcb)
    have hω : 0 < ω := div_pos B.outerRate_pos hα
    exact lt_min hγ (lt_min (hmargin.trans_le
      (sub_le_sub_right (mul_le_mul_of_nonneg_left hcξ (by positivity : 0 ≤ 2 * ω)) g)) hmargin)
  obtain ⟨Ug, Cg, Tk, hUg, _hUgr, hCg, hTk, hgeom⟩ := B.exists_early_geometric_feedback
    (D₀ := D) (D := D) (k := B.innerRate) (ε := ε) (κ₀ := 2 / 3) (β := β) (n := n) (N := N)
    (He := He) (Kmax := B.innerRate + ε) hs hH hdH hdHR hA hApt hρ hρR hD.le hD.le
    hc0 hca hcs (by norm_num) hε.le hεk hβ hn hN.le hHe.le (add_pos B.innerRate_pos hε).le
    hp hcb hmargin hc hb hrc hrb hrd hrdec hOut
  let Cj := Y * He ^ 2 / l
  let Cm := Y ^ 2 * He ^ 2 / (2 * (2 / 3))
  let Cmax := max (r 0 / ρ) (max Ch (max Cg (max Cj (max Cerr Cm))))
  let C := Cmax + 1
  have hmax : Cmax ≤ C := le_add_of_nonneg_right zero_le_one
  have hCd : r 0 / ρ ≤ C := (show r 0 / ρ ≤ Cmax by simp [Cmax]).trans hmax
  have hCh : Ch ≤ C := (show Ch ≤ Cmax by simp [Cmax]).trans hmax
  have hCgC : Cg ≤ C := (show Cg ≤ Cmax by simp [Cmax]).trans hmax
  have hCj : Cj ≤ C := (show Cj ≤ Cmax by simp [Cmax]).trans hmax
  have hCerrC : Cerr ≤ C := (show Cerr ≤ Cmax by simp [Cmax]).trans hmax
  have hCm : Cm ≤ C := (show Cm ≤ Cmax by simp [Cmax]).trans hmax
  have hC : 0 < C := (div_pos hrinit0 hρ).trans_le hCd
  have hlim : Tendsto (fun t : ℝ => Cg * Real.exp (-η * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq, mul_zero] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hη))).const_mul Cg
  obtain ⟨Te, hlate⟩ := eventually_atTop.1 (hlim.eventually_lt_const (half_pos hd))
  let T₀ := max Ts (max Tspeed (max Tm (max Tk (max Te (max Tband Ti)))))
  have hT0s : Ts ≤ T₀ := le_max_left _ _
  have hT0speed : Tspeed ≤ T₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hT0m : Tm ≤ T₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hT0k : Tk ≤ T₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hT0e : Te ≤ T₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hT0bi : max Tband Ti ≤ T₀ := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hT0b : Tband ≤ T₀ := (le_max_left _ _).trans hT0bi
  have hT0i : Ti ≤ T₀ := (le_max_right _ _).trans hT0bi
  let U₀ := min (σ / 2) (min (min Ug Uc) (j * Real.exp (-B.outerRate * T₀) / 2))
  have hU₀ : 0 < U₀ := by dsimp only [U₀]; positivity
  have hUσ : U₀ < σ := (min_le_left _ _).trans_lt (half_lt_self hσ)
  have hUg' : U₀ ≤ Ug := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hUc' : U₀ ≤ Uc := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hUt : U₀ ≤ j * Real.exp (-B.outerRate * T₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let Olo := min (2 * n) (l / (4 * N * D))
  let Ohi := max (4 * N * D) (Lband / (2 * n))
  have hOlo : 0 < Olo := lt_min (by positivity) (by positivity)
  have hOhi : 0 < Ohi := (show 0 < 4 * N * D by positivity).trans_le (le_max_left _ _)
  refine ⟨δ, Δ, Y, U₀, He, C, η, qR, Lk, j, D, Olo, Ohi, L,
    hδ, hδr, hΔ, hΔr, hpot, hY.1, hYΔ, hYcap', hYclose, hU₀, hUσ.le.trans hσδ,
    hHe, hC, hη, hqR, hLk, hj, hD, hOlo, hOhi, hL, min_le_right _ _, ?_⟩
  intro f hf hfn hpoint
  obtain ⟨arrival, hac, haa, hal, hscale, hpreall, _hidentify, hrow⟩ := hglobal p hp f hf hfn hcb
  have hsub : Ioc 0 U₀ ⊆ Ioo 0 σ := fun u hu => ⟨hu.1, hu.2.trans_lt hUσ⟩
  have hentrylate (u : ℝ) (hu : u ∈ Ioc 0 U₀) : T₀ ≤ arrival u := by
    by_contra hnot
    have he := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (not_le.1 hnot).le B.outerRate_pos.le)
    have hh := mul_le_mul_of_nonneg_right (hu.2.trans hUt) (Real.exp_pos (B.outerRate * T₀)).le
    have hex : Real.exp (-B.outerRate * T₀) * Real.exp (B.outerRate * T₀) = 1 := by
      rw [← Real.exp_add, show -B.outerRate * T₀ + B.outerRate * T₀ = 0 by ring, Real.exp_zero]
    have hh' : u * Real.exp (B.outerRate * T₀) ≤ j / 2 := by
      convert hh using 1 <;> first | rfl | (rw [show j * Real.exp (-B.outerRate * T₀) / 2 * Real.exp (B.outerRate * T₀) =
        j / 2 * (Real.exp (-B.outerRate * T₀) * Real.exp (B.outerRate * T₀)) by ring, hex, mul_one])
    have hs := (hscale u (hsub hu)).2.1
    have hh'' := mul_le_mul_of_nonneg_left he hu.1.le
    linarith only [hs, hh', hh'', hj]
  have hmatch (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x) (hUU : U ≤ U₀)
      (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 V) (hv : (v : ℝ) = arrival u) :
      Olo ≤ (u : ℝ) * Real.exp (x.1 u v 2) ∧
        (u : ℝ) * Real.exp (x.1 u v 2) ≤ Ohi ∧
        Olo * (u : ℝ) ≤ -x.2.1 u v 0 / Real.exp (x.1 u v 2) ∧
        -x.2.1 u v 0 / Real.exp (x.1 u v 2) ≤ Ohi * (u : ℝ) ∧
        x.1 u v 0 = Y ∧ -x.2.1 u v 0 ≤ L := by
    have hTv := (hentrylate u ⟨hu, u.property.2.trans hUU⟩).trans_eq hv.symm
    obtain ⟨z, hzu, T, _hz, _hTz, _hder, hdata⟩ := hrow hU.le hV hUR hfU hx u v hu
      (u.property.2.trans_lt (hUU.trans_lt hUσ)) (hT0b.trans hTv) hv.ge
    have hd := hdata u (right_mem_Icc.2 (show (z : ℝ) ≤ u from hzu))
    simp only [projIcc_of_mem hU.le u.property] at hd
    have hτv : T (projIcc (z : ℝ) u hzu u) = v :=
      Subtype.ext (hd.2.2.2.2.2.2.2.2.2.trans hv.symm)
    rw [hτv] at hd
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose u v
    have hg := hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU u v
    have hν : ν < 0 := hg.2.2.1
    have herr := hd.2.2.2.2.2.2.2.2.1
    have hmC : Cerr * Real.exp (-γ * (v : ℝ)) ≤ (Cerr + Cc) * Real.exp (-γ * v) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCc) (Real.exp_pos _).le
    have hκ : (1 / 2 : ℝ) ≤ -Real.exp (x.1 u v 2) / (4 * ν) := by
      have hh := (le_add_of_nonneg_right (abs_nonneg _)).trans herr |>.trans hmC
      have hh' := (abs_lt.1 (hh.trans_lt ((hentryerr v (hT0i.trans hTv)).trans_le (min_le_left _ _)))).1
      linarith only [hh']
    have hdneg : 4 * ν < 0 := mul_neg_of_pos_of_neg (by norm_num) hν
    have hlo : 2 * (-ν) ≤ Real.exp (x.1 u v 2) := by
      have hh := (le_div_iff_of_neg hdneg).1 hκ
      linarith only [hh]
    have hhi : Real.exp (x.1 u v 2) ≤ 4 * (-ν) := by
      have hh := (div_le_iff_of_neg hdneg).1 hg.2.2.2.2
      linarith only [hh]
    have hnlo : n ≤ (u : ℝ) * (-ν) := hd.2.2.2.2.2.1
    have hnhi : (u : ℝ) * (-ν) ≤ N * D := by
      calc
        _ ≤ (u : ℝ) * (N * Real.exp (B.outerRate * v)) :=
          mul_le_mul_of_nonneg_left ((neg_le_abs ν).trans (hd.2.2.2.2.2.2.2.1 u le_rfl v le_rfl).2.1) hu.le
        _ = N * ((u : ℝ) * Real.exp (B.outerRate * v)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hd.2.2.2.2.2.2.1 hN.le
    have hOmegaLo : 2 * n ≤ (u : ℝ) * Real.exp (x.1 u v 2) := by
      nlinarith only [hnlo, mul_le_mul_of_nonneg_left hlo hu.le]
    have hOmegaHi : (u : ℝ) * Real.exp (x.1 u v 2) ≤ 4 * N * D := by
      nlinarith only [hnhi, mul_le_mul_of_nonneg_left hhi hu.le]
    have hDlo : (l / (4 * N * D)) * (u : ℝ) ≤ -x.2.1 u v 0 / Real.exp (x.1 u v 2) := by
      apply (le_div_iff₀ (Real.exp_pos _)).2
      calc
        _ = (l / (4 * N * D)) * ((u : ℝ) * Real.exp (x.1 u v 2)) := by ring
        _ ≤ (l / (4 * N * D)) * (4 * N * D) := mul_le_mul_of_nonneg_left hOmegaHi (by positivity)
        _ = l := by field_simp
        _ ≤ _ := hd.2.2.2.1
    have hDhi : -x.2.1 u v 0 / Real.exp (x.1 u v 2) ≤ (Lband / (2 * n)) * (u : ℝ) := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      calc
        _ ≤ Lband := hd.2.2.2.2.1
        _ = (Lband / (2 * n)) * (2 * n) := by field_simp
        _ ≤ (Lband / (2 * n)) * ((u : ℝ) * Real.exp (x.1 u v 2)) :=
          mul_le_mul_of_nonneg_left hOmegaLo (by positivity)
        _ = _ := by ring
    exact ⟨(min_le_left _ _).trans hOmegaLo, hOmegaHi.trans (le_max_left _ _),
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hu.le).trans hDlo,
      hDhi.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hu.le), hd.2.2.1,
      (hvel hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU hx u v
        (hT0speed.trans hTv) hd.2.2.1 ((le_add_of_nonneg_left (abs_nonneg _)).trans herr)).2⟩
  have hhistory : ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x), U ≤ U₀ →
      let ν := radialNuField hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
      let K := fun w t => horizonK (x.1 w t 0)
        (massField B.charge B.cosmological x.1 x.2.1 ν hx.choose w t) B.charge B.cosmological
      (∀ w : Icc 0 U, 0 < (w : ℝ) → ∀ t : Icc 0 V,
        arrival w ≤ t → (t : ℝ) ≤ (1 + β) * arrival w →
          B.inner / 2 ≤ x.1 w t 0 ∧ |x.2.1 w t 1| ≤ He * Real.exp (-c * t) ∧
          2 / 3 ≤ -Real.exp (x.1 w t 2) / (4 * ν w t) ∧ |K w t + B.innerRate| ≤ ε) →
        ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V,
          0 < t → arrival t ≤ b → (b : ℝ) ≤ (1 + β) * arrival t →
            |x.2.2 t b 1| ≤ C * |f t| + C * t ^ (-1 + c / B.outerRate) := by
    intro U V hU hV hUR hfU x hx hUU
    dsimp only
    intro hpost
    filter_upwards [hx.early_scalar_history_power hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU
      hc0.le hca (by norm_num : (0 : ℝ) < 2 / 3) hε.le hεk hρ hN.le hHe.le hD.le,
      ae_restrict_mem measurableSet_Icc] with t ht htm
    intro b ht0 htb hwindow
    let w : Icc 0 U := ⟨t, htm⟩
    obtain ⟨z', hz'w, T', _hz', _hT'z, _hT'd, hdata'⟩ := hrow hU.le hV hUR hfU hx w b ht0
      (htm.2.trans_lt (hUU.trans_lt hUσ))
      (hT0b.trans ((hentrylate t ⟨ht0, htm.2.trans hUU⟩).trans htb)) htb
    let a' := T' (projIcc (z' : ℝ) w hz'w t)
    have hd' := hdata' t (right_mem_Icc.2 (show (z' : ℝ) ≤ t from hz'w))
    simp only [projIcc_of_mem hU.le htm] at hd'
    have hta : (a' : ℝ) = arrival t := hd'.2.2.2.2.2.2.2.2.2
    have hpast' (v : Icc 0 V) (hv : a' ≤ v) (hvb : v ≤ b) :=
      hpost w ht0 v (hta ▸ hv) ((show (v : ℝ) ≤ b from hvb).trans hwindow)
    have hh := ht a' b ht0 hd'.2.1 hd'.2.2.2.2.2.2.1
    simp only [projIcc_of_mem hU.le htm] at hh
    have hbnd := hh (by linarith only [hd'.2.2.2.1, hl]) (hpost w ht0 b htb hwindow).1
      (fun v hv => (hd'.2.2.2.2.2.2.2.1 w le_rfl v hv).2.1)
      (fun v hv => by
        by_cases hva : v ≤ a'
        · exact (hd'.2.2.2.2.2.2.2.1 w le_rfl v hva).2.2.trans
            (mul_le_mul_of_nonneg_right hEHe.le (Real.exp_pos _).le)
        · exact (hpast' v (not_le.1 hva).le hv).2.1)
      (fun v hv => (hpast' v hv.1 hv.2).2.2.1)
      (fun v hv => (hpast' v hv.1 hv.2).2.2.2)
    exact hbnd.trans (add_le_add (mul_le_mul_of_nonneg_right hCd (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hCh (Real.rpow_nonneg ht0.le _)))
  refine ⟨arrival, hac.mono hsub, haa.mono hsub, hal, fun u hu => (hscale u (hsub hu)).1,
    (fun u hu => (hscale u (hsub hu)).2), hmatch,
    fun {U V} hU hV hUR hfU {x} hx u hu q hq v hv => (hpreall hU hV hUR hfU hx u (hsub hu) q hq v hv).1,
    ?_, hhistory, ?_⟩
  · intro U V hU hV hUR hfU x hx hUU u b hu hab
    obtain ⟨z, hzu, T, hz, hTz, hder, hdata⟩ := hrow hU.le hV hUR hfU hx u b hu
      (u.property.2.trans_lt (hUU.trans_lt hUσ))
      (hT0b.trans ((hentrylate u ⟨hu, u.property.2.trans hUU⟩).trans hab)) hab
    exact ⟨z, hzu, T, hz, hTz, hder, fun t ht =>
      ⟨(hdata t ht).2.2.2.2.2.2.2.2.2, (hdata t ht).2.1⟩⟩
  intro U V hU hV hUR hfU x hx hUU hentry hwindow
  dsimp only
  let u : Icc 0 U := ⟨U, hU.le, le_rfl⟩
  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
  let K := fun w t => horizonK (x.1 w t 0) (m w t) B.charge B.cosmological
  have hTU := hentrylate U ⟨hU, hUU⟩
  have hTV := hTU.trans hentry
  obtain ⟨z, hzu, T, hz, hTz, hder, hdata⟩ := hrow hU.le hV hUR hfU hx u v hU
    (hUU.trans_lt hUσ) (hT0b.trans hTV) hentry
  let τ := fun t => T (projIcc (z : ℝ) U hzu t)
  have hdU := hdata U (right_mem_Icc.2 (show (z : ℝ) ≤ U from hzu))
  have hproju : projIcc 0 U hU.le U = u := projIcc_of_mem hU.le ⟨hU.le, le_rfl⟩
  rw [hproju] at hdU
  have hfnU := (scalar_prefix_norm_le (hUU.trans (hUσ.le.trans hσδ)) hf).trans hfn
  have hstart : V = arrival U → B.inner / 2 < x.1 u v 0 ∧
      Real.exp (c * V) * |x.2.1 u v 1| < He ∧
      2 / 3 < -Real.exp (x.1 u v 2) / (4 * ν u v) ∧
      |K u v + B.innerRate| < ε ∧ |x.2.1 u v 2 - 2 * K u v| < d := by
    intro heq
    have hτv : τ U = v := Subtype.ext (hdU.2.2.2.2.2.2.2.2.2.trans heq.symm)
    dsimp only at hdU
    dsimp only [τ] at hτv
    rw [hτv] at hdU
    have hpre := hdU.2.2.2.2.2.2.2.1
    have herr := hdU.2.2.2.2.2.2.2.2.1
    have herr' := hentryerr V (hT0i.trans hTV)
    have hmC : Cerr * Real.exp (-γ * V) ≤ (Cerr + Cc) * Real.exp (-γ * V) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCc) (Real.exp_pos _).le
    have hκ : 2 / 3 < -Real.exp (x.1 u v 2) / (4 * ν u v) := by
      have hh := (le_add_of_nonneg_right (abs_nonneg _)).trans herr |>.trans hmC
      have hh' := (abs_lt.1 (hh.trans_lt (herr'.trans_le (min_le_left _ _)))).1
      linarith only [hh']
    have hsc : Real.exp (c * V) * |x.2.1 u v 1| ≤ E := by
      have hh := mul_le_mul_of_nonneg_left (hpre u le_rfl v le_rfl).2.2 (Real.exp_pos (c * V)).le
      have hex : Real.exp (c * V) * Real.exp (-c * V) = 1 := by
        rw [← Real.exp_add, show c * V + -c * V = 0 by ring, Real.exp_zero]
      calc
        _ ≤ Real.exp (c * V) * (E * Real.exp (-c * V)) := hh
        _ = E := by rw [mul_left_comm, hex, mul_one]
    have hm := hmasslate Y hY.1 hYΔ hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU hx u v v
      le_rfl (hT0m.trans hTV) hdU.2.2.1 (by linarith only [hdU.2.2.2.1, hl])
      (by change V ≤ (1 + β) * V; nlinarith only [mul_nonneg hβ hV])
      (fun w hw => by
        have he := le_antisymm hw.2 hw.1
        subst w
        exact (hpre u le_rfl v le_rfl).2.2.trans
          (mul_le_mul_of_nonneg_right hEHe.le (Real.exp_pos _).le))
      ((le_add_of_nonneg_left (abs_nonneg _)).trans herr)
      (fun w hw => by have he := le_antisymm hw.2 hw.1; subst w; exact hκ.le)
    have hh := hconf U V hU.le hV hUR p hp f hfU x hx hfnU hcb (hUU.trans hUc')
      (fun w t => (show ρ ≤ Y by dsimp only [ρ]; linarith only [hY.1, B.inner_pos]).trans
        (hpre w w.property.2 t t.property.2).1) hdU.2.2.2.2.2.2.1 u
    have hcC : Cc * Real.exp (-γ * V) ≤ (Cerr + Cc) * Real.exp (-γ * V) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCerr) (Real.exp_pos _).le
    exact ⟨by rw [hdU.2.2.1]; linarith only [hY.1, B.inner_pos], hsc.trans_lt hEHe,
      hκ, hm.2.2.2.trans_lt (half_lt_self hε),
      hh.trans_lt ((hcC.trans_lt (herr'.trans_le (min_le_right _ _))).trans_le (half_le_self hd.le))⟩
  refine ⟨hstart, ?_⟩
  intro hpost
  have hhistory' : ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V,
      0 < t → arrival t ≤ b → |x.2.2 t b 1| ≤ C * |f t| + C * t ^ (-1 + c / B.outerRate) := by
    have hh := hhistory U V hU hV hUR hfU hx hUU (fun w hw t ht _hwin =>
      let hh := hpost w hw t ht
      ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩)
    filter_upwards [hh,
      ae_restrict_mem measurableSet_Icc] with t ht htm
    intro b ht0 htb
    exact ht b ht0 htb (b.property.2.trans (hwindow.trans (mul_le_mul_of_nonneg_left
      (haa.antitoneOn ⟨ht0, htm.2.trans_lt (hUU.trans_lt hUσ)⟩ ⟨hU, hUU.trans_lt hUσ⟩ htm.2) hα.le)))
  have hpos (t : ℝ) (ht : t ∈ Icc (z : ℝ) U) : 0 < t := hz.trans_le ht.1
  have hpast (t : ℝ) (ht : t ∈ Icc (z : ℝ) U) (w : Icc 0 V) (htw : τ t ≤ w) :=
    hpost (projIcc 0 U hU.le t) (by rw [projIcc_of_mem hU.le ⟨(hpos t ht).le, ht.2⟩]; exact hpos t ht) w
      (by rw [projIcc_of_mem hU.le ⟨(hpos t ht).le, ht.2⟩];
          exact (hdata t ht).2.2.2.2.2.2.2.2.2 ▸ htw)
  have hpointU := ae_mono (Measure.restrict_mono
    (Icc_subset_Icc le_rfl (hUU.trans (hUσ.le.trans hσδ))) le_rfl) hpoint
  have hdZ := hdata z (left_mem_Icc.2 (show (z : ℝ) ≤ U from hzu))
  simp only [projIcc_of_mem hU.le z.property, hTz] at hdZ
  have hpreZ := hdZ.2.2.2.2.2.2.2.1
  have hθ : Real.exp (c * v) * |x.1 z v 0 * x.2.1 z v 1| ≤ Y * E := by
    rw [hdZ.2.2.1, abs_mul, abs_of_pos hY0]
    have hh := mul_le_mul_of_nonneg_left (hpreZ z le_rfl v le_rfl).2.2
      (mul_pos (Real.exp_pos (c * v)) hY0).le
    have hex : Real.exp (c * v) * Real.exp (-c * v) = 1 := by
      rw [← Real.exp_add, show c * v + -c * v = 0 by ring, Real.exp_zero]
    calc
      _ ≤ Real.exp (c * v) * Y * (E * Real.exp (-c * v)) := by simpa only [mul_assoc] using hh
      _ = Y * E := by calc
        _ = (Y * E) * (Real.exp (c * v) * Real.exp (-c * v)) := by ring
        _ = _ := by rw [hex, mul_one]
  have hsc := hscalar U V hU.le hV hUR f hfU x hx hpointU z u hz hzu v T hTz hder
    (by intro w hw; simpa only [ρ, projIcc_of_mem hU.le w.property] using
      (hpast w ⟨hw.1, hw.2⟩ v (hdata w ⟨hw.1, hw.2⟩).2.1).1) (by
      intro t ht
      obtain ⟨hlo, htb, hrY, hll, _hLH, hnt, hDt, hpre, herr, hτ⟩ := hdata t ht
      have hLsmall := hvel hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU hx
        (projIcc 0 U hU.le t) (τ t) (hT0speed.trans (hTU.trans hlo)) hrY
        ((le_add_of_nonneg_left (abs_nonneg _)).trans herr)
      refine ⟨hT0s.trans (hTU.trans hlo), htb, hwindow.trans
        (mul_le_mul_of_nonneg_left hlo hα.le), hll, hLsmall.2, hrY.le, hnt, hDt,
        fun w hw => (hpre _ le_rfl w hw).2.1,
        fun w hw => (hpre _ le_rfl w hw).2.2.trans
          (mul_le_mul_of_nonneg_right (le_max_left E Cν) (Real.exp_pos _).le),
        fun w hw => (hpast t ht w hw.1).2.1, fun w hw => (hpast t ht w hw.1).2.2.1,
        fun w hw => (hpast t ht w hw.1).2.2.2.1, fun w hw => (hpast t ht w hw.1).2.2.2.2⟩) hθ
  have htrapU : x.2.1 u (τ U) 0 < 0 := by linarith only [hdU.2.2.2.1, hl]
  have hτ : (τ U : ℝ) = arrival U := hdU.2.2.2.2.2.2.2.2.2
  have hwindowU : (v : ℝ) ≤ (1 + β) * τ U :=
    hwindow.trans (mul_le_mul_of_nonneg_left hdU.1 hα.le)
  have hscalarU (w : Icc 0 V) (hw : w ∈ Icc (τ U) v) :
      |x.2.1 u w 1| ≤ He * Real.exp (-c * w) := by
    simpa only [hproju] using (hpast U (right_mem_Icc.2 hzu) w hw.1).2.1
  have hkappaU (w : Icc 0 V) (hw : w ∈ Icc (τ U) v) :
      2 / 3 ≤ -Real.exp (x.1 u w 2) / (4 * ν u w) := by
    simpa only [hproju] using (hpast U (right_mem_Icc.2 hzu) w hw.1).2.2.1
  have hKU (w : Icc 0 V) (hw : w ∈ Icc (τ U) v) : |K u w + B.innerRate| ≤ ε := by
    simpa only [hproju] using (hpast U (right_mem_Icc.2 hzu) w hw.1).2.2.2.1
  have hellU (w : Icc 0 V) (hw : w ∈ Icc (τ U) v) : |x.2.1 u w 2 - 2 * K u w| ≤ d := by
    simpa only [hproju] using (hpast U (right_mem_Icc.2 hzu) w hw.1).2.2.2.2
  have hm := hmasslate Y hY.1 hYΔ hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU hx u (τ U) v
    hdU.2.1 (hT0m.trans (hTU.trans hdU.1)) hdU.2.2.1 htrapU
    hwindowU hscalarU ((le_add_of_nonneg_left (abs_nonneg _)).trans hdU.2.2.2.2.2.2.2.2.1) hkappaU
  have hflux := hx.early_inner_flux_bound hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU
    (by norm_num : (0 : ℝ) < 2 / 3) hε.le hεk hHe.le hl u (τ U) v hdU.2.1
    hdU.2.2.2.1 hdU.2.2.1.le hwindowU hscalarU hkappaU hKU hellU
  have hflux0 := hflux.1
  have hfluxC := hflux.2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCj hβ) (τ U).property.1)
    (Real.exp_pos _).le)
  simp only [hτ] at hflux0 hfluxC
  have hmi := hx.trapped_mass_increment_bound hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU
    (by norm_num : (0 : ℝ) < 2 / 3) hHe.le hc0.le u (τ U) v hdU.2.1 htrapU
    hdU.2.2.1.le hscalarU hkappaU
  have hηγ : η ≤ γ := min_le_left _ _
  have hηc : η ≤ 2 * c := hηγ.trans (min_le_right _ _)
  have hexγ : Real.exp (-γ * (τ U : ℝ)) ≤ Real.exp (-η * (τ U : ℝ)) := by
    apply Real.exp_le_exp.2
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hηγ (τ U).property.1)
  have hex2c : Real.exp (-(2 * c) * (τ U : ℝ)) ≤ Real.exp (-η * (τ U : ℝ)) := by
    apply Real.exp_le_exp.2
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hηc (τ U).property.1)
  have hentryM : |m u (τ U) - B.mass| ≤ Cerr * Real.exp (-γ * (τ U : ℝ)) :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans hdU.2.2.2.2.2.2.2.2.1
  have hentryMC := hentryM.trans (mul_le_mul hCerrC hexγ (Real.exp_pos _).le hC.le)
  have hlen : (v : ℝ) - τ U ≤ β * (τ U : ℝ) := by nlinarith only [hwindowU]
  have hdm : |m u v - m u (τ U)| ≤ C * (β * (τ U : ℝ)) * Real.exp (-η * (τ U : ℝ)) := by
    rw [abs_of_nonneg hmi.1]
    exact hmi.2.trans (mul_le_mul
      (mul_le_mul hCm hlen (sub_nonneg.2 hdU.2.1) hC.le) hex2c (Real.exp_pos _).le
      (mul_nonneg hC.le (mul_nonneg hβ (τ U).property.1)))
  have hmassDecay : |m u v - B.mass| ≤ C * (1 + β * arrival U) * Real.exp (-η * arrival U) := by
    calc
      _ = |(m u v - m u (τ U)) + (m u (τ U) - B.mass)| := by congr 1; ring
      _ ≤ C * (β * (τ U : ℝ)) * Real.exp (-η * (τ U : ℝ)) + C * Real.exp (-η * (τ U : ℝ)) :=
        (abs_add_le _ _).trans (add_le_add hdm hentryMC)
      _ = _ := by rw [hτ]; ring
  let Gm := C * (1 + β * (τ U : ℝ)) * Real.exp (-η * (τ U : ℝ))
  have hGm : 0 ≤ Gm := mul_nonneg
    (mul_nonneg hC.le (add_nonneg zero_le_one (mul_nonneg hβ (τ U).property.1))) (Real.exp_pos _).le
  have hentryG : |m u (τ U) - B.mass| ≤ Gm := hentryMC.trans
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC.le
      (by have hh := mul_nonneg hβ (τ U).property.1; linarith only [hh])) (Real.exp_pos _).le)
  have hendG : |m u v - B.mass| ≤ Gm := by simpa only [Gm, hτ] using hmassDecay
  have hmassSegment (w : Icc 0 V) (hw : w ∈ Icc (τ U) v) : |m u w - B.mass| ≤ Gm := by
    have hlo := hx.mass_monotone hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU u hw.1
    have hhi := hx.mass_monotone hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU u hw.2
    exact abs_le.2 ⟨by linarith only [(abs_le.1 hentryG).1, hlo],
      by linarith only [(abs_le.1 hendG).2, hhi]⟩
  have hradSegment (w : Icc 0 V) (hw : w ∈ Icc (τ U) v) :
      x.1 u w 0 ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2) := by
    have hlo : B.inner / 2 ≤ x.1 u w 0 := by
      simpa only [hproju] using (hpast U (right_mem_Icc.2 hzu) w hw.1).1
    have hhi := (hx.outgoing_trapped_radius hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU
      u (τ U) w hw.1 htrapU).2
    rw [hdU.2.2.1] at hhi
    exact ⟨hlo, by linarith only [hhi, hYΔ, hΔe, B.inner_lt_event]⟩
  have hrest := hrestoring hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU hx u (τ U) v
    hdU.2.1 hradSegment (fun _ => Gm) continuousOn_const hkappaU hmassSegment
  have hradIntegral : (∫ t in arrival U..V, |intervalExtension hV (x.1 u) t 0 - B.inner|) ≤
      ((Y - B.inner) + (4 / B.inner) * (β * arrival U) *
        (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) / qR := by
    have hh := hrest.2
    rw [hdU.2.2.1, abs_of_pos (sub_pos.2 hY.1), intervalIntegral.integral_const, smul_eq_mul] at hh
    rw [hτ] at hh
    apply hh.trans
    apply (div_le_div_iff_of_pos_right hqR).2
    have hlenG := mul_le_mul_of_nonneg_right hlen hGm
    have hb := add_le_add (le_refl (Y - B.inner)) (mul_le_mul_of_nonneg_left hlenG
      (div_pos (by norm_num : (0 : ℝ) < 4) B.inner_pos).le)
    simpa only [Gm, hτ, mul_assoc] using hb
  have hkernel : (∫ t in (τ U : ℝ)..v, Real.exp (qR * (t - τ U))) =
      (Real.exp (qR * ((v : ℝ) - τ U)) - 1) / qR := by
    rw [intervalIntegral.integral_comp_sub_right (fun t => Real.exp (qR * t)),
      intervalIntegral.integral_comp_mul_left _ hqR.ne', integral_exp]
    simp only [sub_self, mul_zero, Real.exp_zero, smul_eq_mul]
    ring
  have hradPoint : |x.1 u v 0 - B.inner| ≤ (Y - B.inner) * Real.exp (-qR * (V - arrival U)) +
      ((4 / B.inner) * (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) / qR := by
    have hh := hrest.1 v (right_mem_Icc.2 hdU.2.1)
    rw [hdU.2.2.1, abs_of_pos (sub_pos.2 hY.1), intervalIntegral.integral_mul_const, hkernel] at hh
    have he : Real.exp (-qR * ((v : ℝ) - τ U)) * Real.exp (qR * ((v : ℝ) - τ U)) = 1 := by
      rw [← Real.exp_add, show -qR * ((v : ℝ) - τ U) + qR * ((v : ℝ) - τ U) = 0 by ring,
        Real.exp_zero]
    have hF : 0 ≤ (4 / B.inner * Gm) / qR :=
      div_nonneg (mul_nonneg (div_pos (by norm_num) B.inner_pos).le hGm) hqR.le
    have hb : Real.exp (-qR * ((v : ℝ) - τ U)) *
        (Y - B.inner + (Real.exp (qR * ((v : ℝ) - τ U)) - 1) / qR * (4 / B.inner * Gm)) ≤
        (Y - B.inner) * Real.exp (-qR * ((v : ℝ) - τ U)) + (4 / B.inner * Gm) / qR := by
      have heF := congrArg (fun z => z * ((4 / B.inner * Gm) / qR)) he
      simp only [div_eq_mul_inv] at hF heF ⊢
      nlinarith only [heF,
        mul_nonneg (Real.exp_pos (-qR * ((v : ℝ) - τ U))).le hF]
    simpa only [Gm, hτ] using hh.trans hb
  have hKpoint : |K u v + B.innerRate| ≤ Lk *
      ((Y - B.inner) * Real.exp (-qR * (V - arrival U)) +
        (1 + 4 / B.inner / qR) * (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) := by
    have hh := hKlip (x.1 u v 0) (hradSegment v (right_mem_Icc.2 hdU.2.1)) (m u v)
    exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add hradPoint hmassDecay) hLk.le).trans_eq (by ring))
  let KR := fun t => horizonK (intervalExtension hV (x.1 u) t 0)
    (intervalExtension hV (m u) t) B.charge B.cosmological + B.innerRate
  have hrne (t : ℝ) : intervalExtension hV (x.1 u) t 0 ≠ 0 := hx.choose u (projIcc 0 V hV t)
  have hKRc : Continuous KR :=
    (horizonK_continuous (by fun_prop) (by fun_prop) hrne B.charge B.cosmological).add continuous_const
  have hRRc : Continuous (fun t => |intervalExtension hV (x.1 u) t 0 - B.inner|) := by fun_prop
  have hKRbound (t : ℝ) (ht : t ∈ Icc (τ U : ℝ) v) :
      |KR t| ≤ Lk * (|intervalExtension hV (x.1 u) t 0 - B.inner| + Gm) := by
    have htV : t ∈ Icc 0 V := ⟨(τ U).property.1.trans ht.1, ht.2.trans v.property.2⟩
    let w : Icc 0 V := ⟨t, htV⟩
    have hh := (hKlip (x.1 u w 0) (hradSegment w ht) (m u w)).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hmassSegment w ht)) hLk.le)
    simpa only [KR, intervalExtension_apply, projIcc_of_mem hV htV] using hh
  have hKintegral : (∫ t in arrival U..V, |horizonK (intervalExtension hV (x.1 u) t 0)
      (intervalExtension hV (m u) t) B.charge B.cosmological + B.innerRate|) ≤
      Lk * ((Y - B.inner) / qR + (1 + 4 / B.inner / qR) * (β * arrival U) *
        (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) (show (τ U : ℝ) ≤ v from hdU.2.1)
      (hKRc.abs.intervalIntegrable _ _) (((hRRc.add continuous_const).const_mul Lk).intervalIntegrable _ _)
      hKRbound
    simp only [Pi.add_apply] at hh
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hRRc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at hh
    have hrI := hradIntegral
    rw [← hτ] at hrI
    have hb := hh.trans (mul_le_mul_of_nonneg_left
      (add_le_add hrI (mul_le_mul_of_nonneg_right hlen hGm)) hLk.le)
    rw [← hτ]
    apply hb.trans_eq
    rw [hτ]
    ring
  have hradlo : ∀ w : Icc 0 U, ρ ≤ x.1 w v 0 := by
    intro w
    by_cases hw : w ≤ z
    · exact (show ρ ≤ Y by dsimp only [ρ]; linarith only [hY.1, B.inner_pos]).trans (hpreZ w hw v le_rfl).1
    · simpa only [ρ, projIcc_of_mem hU.le w.property] using
        (hpast w ⟨(not_le.1 hw).le, w.property.2⟩ v (hdata w ⟨(not_le.1 hw).le, w.property.2⟩).2.1).1
  have hanti := hx.radial_strictAnti hx.choose rfl (incomingWave_constraint_data hU.le hUR hp hfU (horizonPhi h r 0)).1 v
    (fun w => (hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU w v).2.2.1)
  have hrmax (w : Icc 0 U) : x.1 w v 0 ≤ B.event + dH := by
    have hh := hanti.antitone (show (⟨0, le_rfl, hU.le⟩ : Icc 0 U) ≤ w from w.property.1)
    rw [(hx.horizon_traces hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU).2 v] at hh
    exact hh.trans (hHrad V hV).1.2
  have hwidth : U * Real.exp (ω * V) ≤ D := by
    have hv : V / (1 + β) ≤ arrival U := (div_le_iff₀ hα).2 (by simpa only [mul_comm] using hwindow)
    have he : ω * V ≤ B.outerRate * arrival U := by
      dsimp only [ω]
      simpa only [div_mul_eq_mul_div, mul_div_assoc] using mul_le_mul_of_nonneg_left hv B.outerRate_pos.le
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 he) hU.le).trans (hscale U ⟨hU, hUU.trans_lt hUσ⟩).2.2
  have hKmax : |K u v| ≤ B.innerRate + ε := by
    have hh := abs_add_le (K u v + B.innerRate) (-B.innerRate)
    simp only [add_neg_cancel_right, abs_neg, abs_of_pos B.innerRate_pos] at hh
    linarith only [hh, (hpost u hU v hentry).2.2.2.1]
  have hg := hgeom U V hU.le hV hUR f hfU x hx hfnU hpointU (hUU.trans hUg') z
    (fun w hw t => (show ρ ≤ Y by dsimp only [ρ]; linarith only [hY.1, B.inner_pos]).trans (hpreZ w hw t t.property.2).1)
    hdZ.2.2.2.2.2.2.1 (fun w => ⟨hradlo w, hrmax w⟩) hwidth hKmax (by
      intro t ht
      obtain ⟨hlo, htb, _hrY, hll, _hLH, hnt, hDt, hpre, _herr, _hτ⟩ := hdata t ⟨ht.1.le, ht.2⟩
      refine ⟨τ t, htb, hwindow.trans (mul_le_mul_of_nonneg_left hlo hα.le),
        by linarith only [hll, hl], hnt, hDt, fun w hw => (hpre _ le_rfl w hw).2.1, ?_,
        fun w hw => (hpast t ⟨ht.1.le, ht.2⟩ w hw.1).2.2.1,
        fun w hw => (hpast t ⟨ht.1.le, ht.2⟩ w hw.1).2.2.2.1⟩
      intro w _hw
      by_cases hwt : w ≤ τ t
      · exact (hpre _ le_rfl w hwt).2.2.trans (mul_le_mul_of_nonneg_right hEHe.le (Real.exp_pos _).le)
      · exact (hpast t ⟨ht.1.le, ht.2⟩ w (not_le.1 hwt).le).2.1)
  have herr : |x.2.1 u v 2 - 2 * K u v| ≤ d / 2 :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans (hg.2.1.trans (hlate V (hT0e.trans hTV)).le)
  refine ⟨hsc, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2, hg.2.2 (hT0k.trans hTV), herr, ?_, hhistory',
    hg.2.1.trans (mul_le_mul_of_nonneg_right hCgC (Real.exp_pos _).le), hmassDecay, hflux0, hfluxC,
    hradPoint, hradIntegral, hKpoint, hKintegral⟩
  intro hgamma
  have htransport := (hx.inner_segment_transport hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU
    (κ₀ := 2 / 3) (by norm_num) hε.le hεk u (τ U) v hdU.2.1 htrapU hkappaU hKU hellU).1.2
  have hdiff : (v : ℝ) - τ U = β * (τ U : ℝ) := by
    change V - (τ U : ℝ) = β * (τ U : ℝ)
    rw [hτ]
    nlinarith only [hgamma]
  have hnY := (neg_le_abs (ν u (τ U))).trans (hdU.2.2.2.2.2.2.2.1 u le_rfl (τ U) le_rfl).2.1
  have hscaleU := hscale U ⟨hU, hUU.trans_lt hUσ⟩
  calc
    -ν u v ≤ (-ν u (τ U)) * Real.exp (-q * (β * (τ U : ℝ))) := by
      simpa only [hdiff] using htransport
    _ ≤ N * Real.exp (B.outerRate * (τ U : ℝ)) * Real.exp (-q * (β * (τ U : ℝ))) :=
      mul_le_mul_of_nonneg_right hnY (Real.exp_pos _).le
    _ ≤ Cν * U ^ (-1 + q / B.outerRate * β) := arrival_decay_power B.outerRate_pos hU hj hD.le hN.le
      (by dsimp only [q]; positivity) hβ (by simpa only [hτ] using hscaleU.2.1) hdU.2.2.2.2.2.2.1
    _ ≤ He * U ^ (-1 + q / B.outerRate * β) :=
      mul_le_mul_of_nonneg_right hCνHe (Real.rpow_nonneg hU.le _)

end CauchyHorizon.Background
