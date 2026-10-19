import CauchyHorizon.Characteristic.EarlyClosure
import CauchyHorizon.Characteristic.PhysicalOverlapNu

/-! Exact early decay on actual solutions, with a uniformly small kernel coefficient. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_early_exact_geometry (B : Background) {s H dH A Apt c ε d β : ℝ}
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
    ∃ δ Y U₀ Ly j D Olo Ohi : ℝ,
      0 < δ ∧ δ ≤ r 0 / 4 ∧ B.inner < Y ∧ Y ≤ Ycap ∧
      0 < U₀ ∧ U₀ ≤ δ ∧ 0 < Ly ∧ 0 < j ∧ 0 < D ∧ 0 < Olo ∧ 0 < Ohi ∧
      (Real.exp 2 * Ly) * Ly * (2 * Real.exp 1) < B.innerRate ^ 2 * (B.inner / 2) ^ 2 ∧
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
              ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ a : Icc 0 V, (a : ℝ) = arrival u →
                Olo ≤ (u : ℝ) * Real.exp (x.1 u a 2) ∧ (u : ℝ) * Real.exp (x.1 u a 2) ≤ Ohi ∧
                Olo * (u : ℝ) ≤ -x.2.1 u a 0 / Real.exp (x.1 u a 2) ∧
                -x.2.1 u a 0 / Real.exp (x.1 u a 2) ≤ Ohi * (u : ℝ) ∧
                x.1 u a 0 = Y ∧ -x.2.1 u a 0 ≤ Ly) ∧
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
              (b : ℝ) ≤ (1 + β) * arrival u →
              ∃ (z : Icc 0 U) (hzu : z ≤ u) (T : C(Icc (z : ℝ) u, Icc 0 V)),
                0 < (z : ℝ) ∧
                let τ := fun t => T (projIcc (z : ℝ) u hzu t)
                let ν := radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                τ z = b ∧
                (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
                  (-ν (projIcc 0 U hU.le t) (τ t) / x.2.1 (projIcc 0 U hU.le t) (τ t) 0) t) ∧
                ∀ t ∈ Icc (z : ℝ) u,
                  let w := projIcc 0 U hU.le t
                  (τ t : ℝ) = arrival t ∧ τ t ≤ b ∧ x.1 w (τ t) 0 = Y ∧
                    ν w (τ t) < 0 ∧ -Ly ≤ x.2.1 w (τ t) 0 ∧ x.2.1 w (τ t) 0 < 0 ∧
                    Olo ≤ t * Real.exp (x.1 w (τ t) 2) ∧ arrival U ≤ (τ t : ℝ) ∧
                    ∀ v ∈ Icc (τ t) b, B.inner / 2 ≤ x.1 w v 0 ∧
                      |ν w v| ≤ (2 * Real.exp 1) * (-ν w (τ t)) *
                        Real.exp (-2 * B.innerRate * ((v : ℝ) - τ t)) ∧
                      |x.2.1 w v 0| ≤ (Real.exp 2 * Ly) *
                        Real.exp (-2 * B.innerRate * ((v : ℝ) - τ t))) ∧
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
            (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x), U ≤ U₀ →
            ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ b : Icc 0 V, (b : ℝ) ≤ (1 + β) * arrival u →
              B.inner / 2 ≤ x.1 u b 0 ∧
              (arrival u ≤ b →
                let a := projIcc 0 V hV (arrival u)
                let ν := radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                |ν u b| ≤ (2 * Real.exp 1) * (-ν u a) * Real.exp (-2 * B.innerRate * ((b : ℝ) - arrival u)) ∧
                |x.2.1 u b 0| ≤ (Real.exp 2 * Ly) * Real.exp (-2 * B.innerRate * ((b : ℝ) - arrival u)) ∧
                (∫ t in arrival u..(b : ℝ), intervalExtension hV (x.1 u) t 0 *
                  (intervalExtension hV (x.2.1 u) t 1) ^ 2 /
                    (-intervalExtension hV (x.2.1 u) t 0)) ≤ 1 / 16 ∧
                ∀ a' : Icc 0 V, arrival u ≤ a' → a' ≤ b →
                  |ν u b| ≤ (2 * Real.exp 2) * (-ν u a') * Real.exp (-2 * B.innerRate * ((b : ℝ) - a')) ∧
                  |x.2.1 u b 0| ≤ (Real.exp (2 + 1 / 16) * (-x.2.1 u a' 0)) *
                    Real.exp (-2 * B.innerRate * ((b : ℝ) - a'))) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, Δ, Y, Ue, He, C, η, qR, Lk, LF, j, D, Olo, Ohi, Ly,
    hδ, hδr, _hΔ, _hΔr, _hpot, hY, _hYΔ, hYcap', hYclose, hUe, hUeδ,
    _hHe, _hC, hη, _hqR, _hLk, _hLF, hj, hD, hOlo, hOhi, hLy, hLycap, hsolve⟩ :=
    B.exists_early_bounds hs hH hdH hdHR hA hApt hc0 hca hcs hε hεk hd hβ
      hℓ hJ hQ hp hcb hc hb hrc hrb hrinit hrd hrdec hOut Ycap hYcap
  let E : ℝ → ℝ := fun t => C / η * Real.exp (-η * t) +
    2 * Lk * (1 + 4 / B.inner / qR) * (β * t) * (C * (1 + β * t) * Real.exp (-η * t))
  have hE0 : Tendsto (fun t : ℝ => Real.exp (-η * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hη))
  have hE1 : Tendsto (fun t : ℝ => t * Real.exp (-η * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 η hη
  have hE2 : Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-η * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 η hη
  have hElim : Tendsto E atTop (𝓝 0) := by
    have hh := ((hE0.const_mul (C / η)).add
      (hE1.const_mul (2 * Lk * (1 + 4 / B.inner / qR) * β * C))).add
        (hE2.const_mul (2 * Lk * (1 + 4 / B.inner / qR) * β ^ 2 * C))
    simp only [mul_zero, add_zero] at hh
    convert hh using 1
    ext t
    dsimp only [E]
    ring
  have hJlim : Tendsto (fun t : ℝ => C * β * t *
      Real.exp (-(2 * c - max 0 (2 * (B.innerRate + ε) + d - 2 * c) * β) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_zero, mul_assoc] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 _ hJ).const_mul (C * β)
  obtain ⟨Te, hTe⟩ := eventually_atTop.1 (hElim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Tj, hTj⟩ := eventually_atTop.1 (hJlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 16))
  let T := max Te Tj
  let U₀ := min Ue (j * Real.exp (-B.outerRate * T) / 2)
  have hU₀ : 0 < U₀ := by dsimp only [U₀]; positivity
  have hUδ : U₀ ≤ δ := (min_le_left _ _).trans hUeδ
  have hfeedback : (Real.exp 2 * Ly) * Ly * (2 * Real.exp 1) <
      B.innerRate ^ 2 * (B.inner / 2) ^ 2 := by
    have hsmall := (le_div_iff₀ (Real.exp_pos 2)).1 hLycap
    have hsmall2 := mul_self_le_mul_self (by positivity : 0 ≤ Ly * Real.exp 2) hsmall
    have he1 : 2 < Real.exp 1 := by
      simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    have he : 2 * Real.exp 1 < Real.exp 2 := by
      calc
        _ < Real.exp 1 * Real.exp 1 := mul_lt_mul_of_pos_right he1 (Real.exp_pos 1)
        _ = _ := by rw [← Real.exp_add]; norm_num
    have he2 := mul_lt_mul_of_pos_left he (mul_pos (Real.exp_pos 2) (sq_pos_of_pos hLy))
    nlinarith only [hsmall2, he2]
  refine ⟨δ, Y, U₀, Ly, j, D, Olo, Ohi, hδ, hδr, hY, hYcap', hU₀, hUδ,
    hLy, hj, hD, hOlo, hOhi, hfeedback, ?_⟩
  intro f hf hfn hpoint
  obtain ⟨arrival, hac, haa, hal, hpos, hscale, hmatch, hpre, hchart, _hhistory, hbound⟩ := hsolve f hf hfn hpoint
  have hsub : Ioc 0 U₀ ⊆ Ioc 0 Ue := Ioc_subset_Ioc le_rfl (min_le_left _ _)
  have hentrylate (u : ℝ) (hu : u ∈ Ioc 0 U₀) : T ≤ arrival u := by
    by_contra hn
    have he := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (not_le.1 hn).le B.outerRate_pos.le)
    have hh := mul_le_mul_of_nonneg_right (hu.2.trans (min_le_right _ _)) (Real.exp_pos (B.outerRate * T)).le
    have hex : Real.exp (-B.outerRate * T) * Real.exp (B.outerRate * T) = 1 := by
      rw [← Real.exp_add, show -B.outerRate * T + B.outerRate * T = 0 by ring, Real.exp_zero]
    have hh' : u * Real.exp (B.outerRate * T) ≤ j / 2 := by
      calc
        _ ≤ j * Real.exp (-B.outerRate * T) / 2 * Real.exp (B.outerRate * T) := hh
        _ = j / 2 := by
          rw [show j * Real.exp (-B.outerRate * T) / 2 * Real.exp (B.outerRate * T) =
            j / 2 * (Real.exp (-B.outerRate * T) * Real.exp (B.outerRate * T)) by ring, hex, mul_one]
    have hj' := (hscale u (hsub hu)).1
    have hh'' := mul_le_mul_of_nonneg_left he hu.1.le
    linarith only [hj', hh', hh'', hj]
  suffices hgeometry : ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x), U ≤ U₀ →
      ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ b : Icc 0 V, (b : ℝ) ≤ (1 + β) * arrival u →
        B.inner / 2 ≤ x.1 u b 0 ∧
        (arrival u ≤ b →
          let a := projIcc 0 V hV (arrival u)
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
          |ν u b| ≤ (2 * Real.exp 1) * (-ν u a) * Real.exp (-2 * B.innerRate * ((b : ℝ) - arrival u)) ∧
          |x.2.1 u b 0| ≤ (Real.exp 2 * Ly) * Real.exp (-2 * B.innerRate * ((b : ℝ) - arrival u)) ∧
          (∫ t in arrival u..(b : ℝ), intervalExtension hV (x.1 u) t 0 *
            (intervalExtension hV (x.2.1 u) t 1) ^ 2 /
              (-intervalExtension hV (x.2.1 u) t 0)) ≤ 1 / 16 ∧
          ∀ a' : Icc 0 V, arrival u ≤ a' → a' ≤ b →
            |ν u b| ≤ (2 * Real.exp 2) * (-ν u a') * Real.exp (-2 * B.innerRate * ((b : ℝ) - a')) ∧
            |x.2.1 u b 0| ≤ (Real.exp (2 + 1 / 16) * (-x.2.1 u a' 0)) *
              Real.exp (-2 * B.innerRate * ((b : ℝ) - a'))) by
    refine ⟨arrival, hac.mono hsub, haa.mono hsub, hal, fun u hu => hpos u (hsub hu),
      (fun u hu => hscale u (hsub hu)),
      (fun U V hU hV hUR hfU {x} hx hUU => hmatch U V hU hV hUR hfU hx (hUU.trans (min_le_left _ _))),
      (fun {_ _} hU hV hUR hfU {x} hx u hu => hpre hU hV hUR hfU hx u (hsub hu)), ?_, hgeometry⟩
    intro U V hU hV hUR hfU x hx hUU u b hu hab hwindow
    obtain ⟨z, hzu, T, hz, hTz, hder, hdata⟩ :=
      hchart hU hV hUR hfU hx (hUU.trans (min_le_left _ _)) u b hu hab
    refine ⟨z, hzu, T, hz, hTz, hder, ?_⟩
    intro t ht
    have ht0 := hz.trans_le ht.1
    have htU : t ∈ Icc 0 U := ⟨ht0.le, ht.2.trans u.property.2⟩
    have hτ := (hdata t ht).1
    have hm := hmatch U V hU hV hUR hfU hx (hUU.trans (min_le_left _ _))
      ⟨t, htU⟩ ht0 (T (projIcc (z : ℝ) u hzu t)) hτ
    have htrap : x.2.1 ⟨t, htU⟩ (T (projIcc (z : ℝ) u hzu t)) 0 < 0 := by
      have hh := (mul_pos hOlo ht0).trans_le hm.2.2.1
      exact neg_pos.1 ((div_pos_iff.mp hh).resolve_right
        (by intro hn; exact (Real.exp_pos _).not_gt hn.2)).1
    dsimp only
    rw [projIcc_of_mem hU.le htU]
    have htE : t ∈ Ioc 0 Ue := hsub ⟨ht0, htU.2.trans hUU⟩
    refine ⟨hτ, (hdata t ht).2, hm.2.2.2.2.1,
      (hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU
        ⟨t, htU⟩ (T (projIcc (z : ℝ) u hzu t))).2.2.1,
      by linarith only [hm.2.2.2.2.2], htrap, hm.1,
      by rw [hτ]; exact haa.antitoneOn htE (hsub ⟨hU, hUU⟩) htU.2, ?_⟩
    intro v hv
    have htv : arrival t ≤ v := hτ.ge.trans hv.1
    have hvwin : (v : ℝ) ≤ (1 + β) * arrival t := (show (v : ℝ) ≤ b from hv.2).trans (hwindow.trans
      (mul_le_mul_of_nonneg_left
        (haa.antitoneOn htE (hsub ⟨hu, u.property.2.trans hUU⟩) ht.2) (by linarith only [hβ])))
    have hg := hgeometry U V hU hV hUR hfU hx hUU ⟨t, htU⟩ ht0 v hvwin
    exact ⟨hg.1, by simpa only [← hτ,
      projIcc_of_mem hV (T (projIcc (z : ℝ) u hzu t)).property] using
        (And.intro (hg.2 htv).1 (hg.2 htv).2.1)⟩
  intro U V hU hV hUR hfU x hx hUU u hu b hwindow
  have hu₀ : (u : ℝ) ∈ Ioc 0 U₀ := ⟨hu, u.property.2.trans hUU⟩
  have ha0 := (hpos u (hsub hu₀)).le
  have hgeom (b : Icc 0 V) (hwindow : (b : ℝ) ≤ (1 + β) * arrival u)
      (hab : arrival u ≤ b) : B.inner / 2 ≤ x.1 u b 0 ∧
      (let a := projIcc 0 V hV (arrival u)
       let ν := radialNuField hV B.charge B.cosmological
         (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
       |ν u b| ≤ (2 * Real.exp 1) * (-ν u a) * Real.exp (-2 * B.innerRate * ((b : ℝ) - arrival u)) ∧
       |x.2.1 u b 0| ≤ (Real.exp 2 * Ly) * Real.exp (-2 * B.innerRate * ((b : ℝ) - arrival u)) ∧
       (∫ t in arrival u..(b : ℝ), intervalExtension hV (x.1 u) t 0 *
         (intervalExtension hV (x.2.1 u) t 1) ^ 2 /
           (-intervalExtension hV (x.2.1 u) t 0)) ≤ 1 / 16 ∧
       3 / 4 ≤ -Real.exp (x.1 u b 2) / (4 * ν u b) ∧
       |x.1 u b 2 - x.1 u a 2 + 2 * B.innerRate * ((b : ℝ) - arrival u)| ≤ 1) := by
    let hfq := hfU.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
    let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (b : ℝ))
      le_rfl (by linarith [u.property.2]) le_rfl (by linarith [b.property.2]) x
    have hy := hx.horizon_prefix hU.le hV hUR hu.le b.property.1 u.property.2 b.property.2 hc hi hrc hr0 hp hfU
    have hqb := hbound u b hu b.property.1 (u.property.2.trans_lt hUR) hfq hy
      (hu₀.2.trans (min_le_left _ _)) hab hwindow
    dsimp only at hqb
    obtain ⟨_hscalar, _hrerr, _hmerr, hrlo, _hK, hkappa, _hell, _hgamma, _hrough,
      _hgeomerr, _hmass, _hJ0, hJbound, _hrad, _hradint, _hKbound, _hKint, hRbound, _heq, _hdec⟩ := hqb
    let q : Icc 0 (u : ℝ) := ⟨u, hu.le, le_rfl⟩
    let v : Icc 0 (b : ℝ) := ⟨b, b.property.1, le_rfl⟩
    let a : Icc 0 (b : ℝ) := ⟨arrival u, ha0, hab⟩
    have hproj : projIcc 0 (b : ℝ) b.property.1 (arrival u) = a := projIcc_of_mem _ a.property
    have hm := hmatch u b hu b.property.1 (u.property.2.trans_lt hUR) hfq hy
      (hu₀.2.trans (min_le_left _ _)) q hu a rfl
    have hl : y.2.1 q a 0 < 0 := by
      have hh := (mul_pos hOlo hu).trans_le hm.2.2.1
      exact neg_pos.1 ((div_pos_iff.mp hh).resolve_right (by intro hn; exact (Real.exp_pos _).not_gt hn.2)).1
    have hR1 : |y.1 q v 2 - y.1 q a 2 + 2 * B.innerRate * ((b : ℝ) - arrival u)| ≤ 1 := by
      rw [hproj] at hRbound
      have ht := (hTe (arrival u) ((le_max_left _ _).trans (hentrylate u hu₀))).le
      dsimp only [E] at ht
      calc
        _ ≤ _ := hRbound
        _ = 2 * Lk * (Y - B.inner) / qR + E (arrival u) := by dsimp only [E]; ring
        _ ≤ 1 := by dsimp only [E]; linarith only [hYclose, ht]
    have hJ1 := hJbound.trans (hTj (arrival u) ((le_max_right _ _).trans (hentrylate u hu₀))).le
    have htransport := hy.inner_exact_transport hu.le b.property.1 (u.property.2.trans_lt hUR)
      hc hi hrc hr0 hφ hrd hp hfq q a v hab hl hkappa hR1 (hJ1.trans (by norm_num))
    have hbmatch := hy.horizon_overlap hu.le b.property.1 (u.property.2.trans_lt hUR)
      hU.le hV hUR hc hi hrc hr0 hp hfq hfU hx q.property u.property v.property b.property
    have hbn := hy.horizon_overlap_nu hu.le b.property.1 (u.property.2.trans_lt hUR)
      hU.le hV hUR hc hi hrc hr0 hp hfq hfU hx q.property u.property v.property b.property
    have han := hy.horizon_overlap_nu hu.le b.property.1 (u.property.2.trans_lt hUR)
      hU.le hV hUR hc hi hrc hr0 hp hfq hfU hx q.property u.property a.property ⟨ha0, hab.trans b.property.2⟩
    have hamatch := hy.horizon_overlap hu.le b.property.1 (u.property.2.trans_lt hUR)
      hU.le hV hUR hc hi hrc hr0 hp hfq hfU hx q.property u.property a.property ⟨ha0, hab.trans b.property.2⟩
    rw [hbmatch.1] at hrlo
    rw [hbn, han, hbmatch.2] at htransport
    rw [hbmatch.1, hbn] at hkappa
    rw [hbmatch.1, hamatch.1] at hR1
    refine ⟨by linarith only [hrlo, B.inner_pos], ?_, ?_, ?_, hkappa, ?_⟩
    · simpa only [projIcc_of_mem hV (show arrival u ∈ Icc 0 V from ⟨ha0, hab.trans b.property.2⟩)] using htransport.1
    · exact htransport.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm.2.2.2.2.2 (Real.exp_pos 2).le) (Real.exp_pos _).le)
    · calc
        _ = ∫ t in arrival u..(b : ℝ), intervalExtension b.property.1 (y.1 q) t 0 *
            (intervalExtension b.property.1 (y.2.1 q) t 1) ^ 2 /
              (-intervalExtension b.property.1 (y.2.1 q) t 0) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hab] at ht
          have htb : t ∈ Icc (0 : ℝ) b := ⟨ha0.trans ht.1, ht.2⟩
          have htV : t ∈ Icc 0 V := ⟨htb.1, ht.2.trans b.property.2⟩
          have hh := hy.horizon_overlap hu.le b.property.1 (u.property.2.trans_lt hUR)
            hU.le hV hUR hc hi hrc hr0 hp hfq hfU hx q.property u.property htb htV
          simp only [intervalExtension_apply, projIcc_of_mem b.property.1 htb, projIcc_of_mem hV htV]
          rw [hh.1, hh.2]
        _ ≤ _ := hJ1
    · simpa only [projIcc_of_mem hV (show arrival u ∈ Icc 0 V from ⟨ha0, hab.trans b.property.2⟩)] using hR1
  constructor
  · by_cases hab : arrival u ≤ b
    · exact (hgeom b hwindow hab).1
    · have hh := hpre hU.le hV hUR hfU hx u (hsub hu₀) u le_rfl b (not_le.1 hab).le
      linarith only [hh, hY, B.inner_pos]
  · intro hab
    obtain ⟨_hr, hν, hlam, hJb, hκ, hRb⟩ := hgeom b hwindow hab
    refine ⟨hν, hlam, hJb, ?_⟩
    intro a' ha' ha'b
    have hRa := (hgeom a' ((show (a' : ℝ) ≤ b from ha'b).trans hwindow) ha').2.2.2.2.2
    let a : Icc 0 V := ⟨arrival u, ha0, hab.trans b.property.2⟩
    have hm := hmatch U V hU hV hUR hfU hx (hUU.trans (min_le_left _ _)) u hu a rfl
    have hl : x.2.1 u a 0 < 0 := by
      have hh := (mul_pos hOlo hu).trans_le hm.2.2.1
      exact neg_pos.1 ((div_pos_iff.mp hh).resolve_right (by intro hn; exact (Real.exp_pos _).not_gt hn.2)).1
    have hproj : projIcc 0 V hV (arrival u) = a := projIcc_of_mem _ a.property
    rw [hproj] at hRa hRb
    have hh := hx.inner_exact_transport_restart hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU
      u a a' b ha' ha'b hl hκ hRa hRb hJb
    simpa only [mul_one] using hh

end CauchyHorizon.Background
