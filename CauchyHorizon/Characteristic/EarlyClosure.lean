import CauchyHorizon.Characteristic.EarlyJointClosure
import CauchyHorizon.Analysis.EnteredBootstrap
import CauchyHorizon.Reduced.ConformalRemainder
import CauchyHorizon.Characteristic.GammaConformal
import CauchyHorizon.Characteristic.InnerFunction

/-! Remove the early bootstrap on every existing physical rectangle in the early window. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 600000 in
theorem exists_early_bounds (B : Background) {s H dH A Apt c ε d β : ℝ}
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
    ∃ δ Δ Y U₀ He C η qR Lk LF j D Olo Ohi Ly : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ 0 < Δ ∧ Δ ≤ B.inner / 4 ∧
      (∀ r ∈ Icc (B.inner - Δ) (B.inner + Δ), B.innerRate / 4 ≤ radialPotential r B.charge B.cosmological) ∧
      B.inner < Y ∧ Y ≤ B.inner + Δ / 2 ∧ Y ≤ Ycap ∧ 2 * Lk * (Y - B.inner) / qR ≤ 1 / 2 ∧
      0 < U₀ ∧ U₀ ≤ δ ∧
      0 < He ∧ 0 < C ∧ 0 < η ∧ 0 < qR ∧ 0 < Lk ∧ 0 < LF ∧ 0 < j ∧ 0 < D ∧ 0 < Olo ∧ 0 < Ohi ∧
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
            (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V},
            IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x → U ≤ U₀ →
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
                    (1 + 4 / B.inner / qR) * (C * (1 + 2 * β / η)))) * Real.exp (-ηg * V)) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, Δ, Y, U₀, He, C, η, qR, Lk, j, D, Olo, Ohi, Ly,
    hδ, hδr, hΔ, hΔr, hpot, hY, hYΔ, hYcap', hYclose, hU₀, hUδ,
    hHe, hC, hη, hqR, hLk, hj, hD, hOlo, hOhi, hLy, hLycap, hsolve⟩ :=
    B.exists_early_joint_improvement hs hH hdH hdHR hA hApt hc0 hca hcs hε hεk hd hβ
      hℓ hJ hQ hp hcb hc hb hrc hrb hrinit hrd hrdec hOut Ycap hYcap
  obtain ⟨LF, hLF, hFbound⟩ := B.exists_inner_F_bound
  refine ⟨δ, Δ, Y, U₀, He, C, η, qR, Lk, LF, j, D, Olo, Ohi, Ly,
    hδ, hδr, hΔ, hΔr, hpot, hY, hYΔ, hYcap', hYclose, hU₀, hUδ,
    hHe, hC, hη, hqR, hLk, hLF, hj, hD, hOlo, hOhi, hLy, hLycap, ?_⟩
  intro f hf hfn hpoint
  obtain ⟨arrival, hac, haa, hal, hpos, hscale, hmatch, hpre, hchart, hhistory, hbound⟩ := hsolve f hf hfn hpoint
  have hclosed (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x)
      (hUU : U ≤ U₀) (hentry : arrival U ≤ V) (hwindow : V ≤ (1 + β) * arrival U) := by
    apply (hbound U V hU hV hUR hfU hx hUU hentry hwindow).2
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
    let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
    let K := fun w t => horizonK (x.1 w t 0) (m w t) B.charge B.cosmological
    let κ := fun w t => -Real.exp (x.1 w t 2) / (4 * ν w t)
    let G := fun w t => max (B.inner / 2 - x.1 w t 0)
      (max (Real.exp (c * (t : ℝ)) * |x.2.1 w t 1| - He)
        (max (2 / 3 - κ w t) (max (|K w t + B.innerRate| - ε) (|x.2.1 w t 2 - 2 * K w t| - d))))
    have hdecode (w : Icc 0 U) (t : Icc 0 V) (hg : G w t ≤ 0) :
        B.inner / 2 ≤ x.1 w t 0 ∧ |x.2.1 w t 1| ≤ He * Real.exp (-c * t) ∧
        2 / 3 ≤ κ w t ∧ |K w t + B.innerRate| ≤ ε ∧ |x.2.1 w t 2 - 2 * K w t| ≤ d := by
      simp only [G, max_le_iff, sub_nonpos] at hg
      refine ⟨hg.1, ?_, hg.2.2⟩
      have hh : |x.2.1 w t 1| ≤ He / Real.exp (c * t) :=
        (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hg.2.1)
      simpa only [neg_mul, Real.exp_neg, div_eq_mul_inv] using hh
    have hsub (w : Icc 0 U) (hw : 0 < (w : ℝ)) : (w : ℝ) ∈ Ioc 0 U₀ := ⟨hw, w.property.2.trans hUU⟩
    have hα : 0 ≤ 1 + β := by linarith only [hβ]
    have hlocal (w : Icc 0 U) (hw : 0 < (w : ℝ)) (t : Icc 0 V) (het : arrival w ≤ t) :
        ((t : ℝ) = arrival w → G w t < 0) ∧
        ((∀ q : Icc 0 U, 0 < (q : ℝ) → q ≤ w → ∀ v : Icc 0 V,
          v ≤ t → arrival q ≤ v → G q v ≤ 0) → G w t < 0) := by
      let hfW := hfU.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl w.property.2) le_rfl)
      let y := waveTranslate (a := 0) (U := (w : ℝ)) (b := 0) (V := (t : ℝ)) le_rfl
        (by simpa only [zero_add] using w.property.2) le_rfl (by simpa only [zero_add] using t.property.2) x
      have hy := hx.horizon_prefix hU.le hV hUR hw.le t.property.1 w.property.2 t.property.2 hc hi hrc hr0 hp hfU
      let νy := radialNuField t.property.1 B.charge B.cosmological
        (incomingWaveCurve hw.le (w.property.2.trans_lt hUR) hp hfW (horizonPhi h r 0)) y.1 hy.choose
      have hye (q : Icc 0 (w : ℝ)) (v : Icc 0 (t : ℝ)) :
          y.1 q v = x.1 ⟨q, q.property.1, q.property.2.trans w.property.2⟩
            ⟨v, v.property.1, v.property.2.trans t.property.2⟩ :=
        (hy.horizon_overlap hw.le t.property.1 (w.property.2.trans_lt hUR) hU.le hV hUR hc hi hrc hr0
          hp hfW hfU hx q.property ⟨q.property.1, q.property.2.trans w.property.2⟩
          v.property ⟨v.property.1, v.property.2.trans t.property.2⟩).1
      have hwe (q : Icc 0 (w : ℝ)) (v : Icc 0 (t : ℝ)) :
          y.2.1 q v = x.2.1 ⟨q, q.property.1, q.property.2.trans w.property.2⟩
            ⟨v, v.property.1, v.property.2.trans t.property.2⟩ :=
        (hy.horizon_overlap hw.le t.property.1 (w.property.2.trans_lt hUR) hU.le hV hUR hc hi hrc hr0
          hp hfW hfU hx q.property ⟨q.property.1, q.property.2.trans w.property.2⟩
          v.property ⟨v.property.1, v.property.2.trans t.property.2⟩).2
      have hne (q : Icc 0 (w : ℝ)) (v : Icc 0 (t : ℝ)) :
          νy q v = ν ⟨q, q.property.1, q.property.2.trans w.property.2⟩
            ⟨v, v.property.1, v.property.2.trans t.property.2⟩ :=
        hy.horizon_overlap_nu hw.le t.property.1 (w.property.2.trans_lt hUR) hU.le hV hUR hc hi hrc hr0
          hp hfW hfU hx q.property ⟨q.property.1, q.property.2.trans w.property.2⟩
          v.property ⟨v.property.1, v.property.2.trans t.property.2⟩
      have htw : (t : ℝ) ≤ (1 + β) * arrival w := t.property.2.trans
        (hwindow.trans (mul_le_mul_of_nonneg_left (haa.antitoneOn ⟨hw, w.property.2.trans hUU⟩
          ⟨hU, hUU⟩ w.property.2) hα))
      have hh := hbound w t hw t.property.1 (w.property.2.trans_lt hUR) hfW hy
        (w.property.2.trans hUU) het htw
      dsimp only [y, νy] at hye hwe hne
      constructor
      · intro heq
        have hh' := hh.1 heq
        simp only [massField_apply, hye, hwe, hne] at hh'
        simpa only [G, κ, K, m, massField_apply, max_lt_iff, sub_neg] using hh'
      · intro hpre
        have hb' : ∀ q : Icc 0 (w : ℝ), 0 < (q : ℝ) → ∀ v : Icc 0 (t : ℝ), arrival q ≤ v →
            B.inner / 2 ≤ y.1 q v 0 ∧ |y.2.1 q v 1| ≤ He * Real.exp (-c * v) ∧
            2 / 3 ≤ -Real.exp (y.1 q v 2) / (4 * νy q v) ∧
            |horizonK (y.1 q v 0) (massField B.charge B.cosmological y.1 y.2.1 νy hy.choose q v)
              B.charge B.cosmological + B.innerRate| ≤ ε ∧
            |y.2.1 q v 2 - 2 * horizonK (y.1 q v 0)
              (massField B.charge B.cosmological y.1 y.2.1 νy hy.choose q v) B.charge B.cosmological| ≤ d := by
          intro q hq v hv
          have hd := hdecode ⟨q, q.property.1, q.property.2.trans w.property.2⟩
            ⟨v, v.property.1, v.property.2.trans t.property.2⟩ (hpre _ hq q.property.2 _ v.property.2 hv)
          simpa only [κ, K, m, massField_apply, y, νy, hye, hwe, hne] using hd
        have hi' := hh.2 hb'
        simp only [massField_apply, hye, hwe, hne] at hi'
        simp only [G, κ, K, m, massField_apply, max_lt_iff, sub_neg]
        exact ⟨by linarith only [hi'.2.2.2.1, B.inner_pos], hi'.1.trans_lt (half_lt_self hHe),
          lt_of_lt_of_le (by norm_num : (2 / 3 : ℝ) < 3 / 4) hi'.2.2.2.2.2.1,
          hi'.2.2.2.2.1.trans_lt (half_lt_self hε), hi'.2.2.2.2.2.2.1.trans_lt (half_lt_self hd)⟩
    have hnear : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 U :=
      (show ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u from self_mem_nhdsWithin).and
        ((eventually_lt_nhds hU).filter_mono nhdsWithin_le_nhds)
    obtain ⟨z, hz, hzV⟩ := (hnear.and (hal.eventually (eventually_gt_atTop V))).exists
    let embed : Icc z U → Icc 0 U := fun w => ⟨w, hz.1.le.trans w.property.1, w.property.2⟩
    have hembed : Continuous embed := continuous_subtype_val.subtype_mk _
    let entry := fun w : Icc z U => arrival w
    have hec : Continuous entry := (hac.mono (show Icc z U ⊆ Ioc 0 U₀ from
      fun w hw => ⟨hz.1.trans_le hw.1, hw.2.trans hUU⟩)).domRestrict
    have he0 (w : Icc z U) : 0 ≤ entry w := (hpos w ⟨hz.1.trans_le w.property.1, w.property.2.trans hUU⟩).le
    let F := fun q : ℝ × Icc z U => G (embed q.2) (projIcc 0 V hV q.1)
    have hνc := ν.uncurry.continuous
    have hmc := m.uncurry.continuous
    have hxc := x.1.uncurry.continuous
    have hwc := x.2.1.uncurry.continuous
    have hRc : Continuous (fun q : Icc 0 U × Icc 0 V => x.1 q.1 q.2 0) :=
      (continuous_apply (0 : Fin 3)).comp hxc
    have hEc : Continuous (fun q : Icc 0 U × Icc 0 V => x.1 q.1 q.2 2) :=
      (continuous_apply (2 : Fin 3)).comp hxc
    have hSc : Continuous (fun q : Icc 0 U × Icc 0 V => x.2.1 q.1 q.2 1) :=
      (continuous_apply (1 : Fin 3)).comp hwc
    have hLc : Continuous (fun q : Icc 0 U × Icc 0 V => x.2.1 q.1 q.2 2) :=
      (continuous_apply (2 : Fin 3)).comp hwc
    have hKc : Continuous (fun q : Icc 0 U × Icc 0 V => K q.1 q.2) := by
      dsimp only [K]
      unfold horizonK
      exact ((hmc.div (hRc.pow 2) (fun q => pow_ne_zero _ (hx.choose q.1 q.2))).sub
        (continuous_const.div (hRc.pow 3) (fun q => pow_ne_zero _ (hx.choose q.1 q.2)))).sub
        ((hRc.const_mul B.cosmological).div_const 3)
    have hκc : Continuous (fun q : Icc 0 U × Icc 0 V => κ q.1 q.2) := by
      apply (Real.continuous_exp.comp hEc).neg.div (hνc.const_mul 4)
      intro q
      exact mul_ne_zero (by norm_num) (hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU q.1 q.2).2.2.1.ne
    have hGc : Continuous (fun q : Icc 0 U × Icc 0 V => G q.1 q.2) := by
      have hExp : Continuous (fun q : Icc 0 U × Icc 0 V => Real.exp (c * (q.2 : ℝ))) :=
        Real.continuous_exp.comp ((continuous_subtype_val.comp continuous_snd).const_mul c)
      exact (continuous_const.sub hRc).max (((hExp.mul hSc.abs).sub continuous_const).max
        ((continuous_const.sub hκc).max (((hKc.add continuous_const).abs.sub continuous_const).max
          ((hLc.sub (hKc.const_mul 2)).abs.sub continuous_const))))
    have hFc : Continuous F := hGc.comp (hembed.comp continuous_snd |>.prodMk
      ((show Continuous (projIcc 0 V hV) from continuous_projIcc).comp continuous_fst))
    have hstrict := continuous_entered_bootstrap hFc hec he0
      (fun w hw => by
        have hE : entry w ∈ Icc 0 V := ⟨he0 w, hw⟩
        have hh := (hlocal (embed w) (hz.1.trans_le w.property.1) ⟨entry w, hE⟩ le_rfl).1 rfl
        simpa only [F, projIcc_of_mem hV hE] using hh)
      (fun t ht hpre w hwt => by
        have hh := (hlocal (embed w) (hz.1.trans_le w.property.1) ⟨t, ht⟩ hwt).2 (by
          intro q hq _hqw v hvt hev
          have hzq : z ≤ (q : ℝ) := by
            by_contra hnot
            have ha := haa ⟨hq, q.property.2.trans hUU⟩ ⟨hz.1, hz.2.le.trans hUU⟩ (not_le.1 hnot)
            exact (hzV.trans ha).not_ge (hev.trans v.property.2)
          have hh := hpre v ⟨v.property.1, hvt⟩ ⟨q, hzq, q.property.2⟩ hev
          simpa only [F, embed, projIcc_of_mem hV v.property] using hh)
        simpa only [F, projIcc_of_mem hV ht] using hh)
    intro w hw t het
    have hzw : z ≤ (w : ℝ) := by
      by_contra hnot
      have ha := haa (hsub w hw) ⟨hz.1, hz.2.le.trans hUU⟩ (not_le.1 hnot)
      exact (hzV.trans ha).not_ge (het.trans t.property.2)
    have hh := hstrict t t.property ⟨w, hzw, w.property.2⟩ het
    have hg : G w t ≤ 0 := by simpa only [F, embed, projIcc_of_mem hV t.property] using hh.le
    exact hdecode w t hg
  have hfull (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x)
      (hUU : U ≤ U₀) (hentry : arrival U ≤ V) (hwindow : V ≤ (1 + β) * arrival U) := by
    have hbase := hclosed U V hU hV hUR hfU hx hUU hentry hwindow
    let u : Icc 0 U := ⟨U, hU.le, le_rfl⟩
    let v : Icc 0 V := ⟨V, hV, le_rfl⟩
    let a := projIcc 0 V hV (arrival U)
    have hT : arrival U ∈ Icc 0 V := ⟨(hpos U ⟨hU, hUU⟩).le, hentry⟩
    have ha : (a : ℝ) = arrival U := by simp only [a, projIcc_of_mem hV hT]
    have hav : a ≤ v := by change (a : ℝ) ≤ V; rw [ha]; exact hentry
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
    let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
    let K := fun t => horizonK (intervalExtension hV (x.1 u) t 0)
      (intervalExtension hV (m u) t) B.charge B.cosmological
    have hrne (t : ℝ) : intervalExtension hV (x.1 u) t 0 ≠ 0 := hx.choose u (projIcc 0 V hV t)
    have hKc : Continuous K := horizonK_continuous (by fun_prop) (by fun_prop) hrne B.charge B.cosmological
    have herr (t : Icc 0 V) (ht : t ∈ Icc a v) :
        |x.2.1 u t 2 - 2 * K t| ≤ C * Real.exp (-η * t) := by
      have hentryt : arrival U ≤ t := by rw [← ha]; exact ht.1
      have hy := hx.horizon_prefix hU.le hV hUR hU.le t.property.1 le_rfl t.property.2 hc hi hrc hr0 hp hfU
      have hh := hclosed U t hU t.property.1 hUR hfU hy hUU hentryt (t.property.2.trans hwindow)
      have he := hy.horizon_overlap hU.le t.property.1 hUR hU.le hV hUR hc hi hrc hr0 hp hfU hfU hx
        (show U ∈ Icc 0 U from ⟨hU.le, le_rfl⟩) (show U ∈ Icc 0 U from ⟨hU.le, le_rfl⟩)
        (show (t : ℝ) ∈ Icc 0 (t : ℝ) from ⟨t.property.1, le_rfl⟩) t.property
      have hn := hy.horizon_overlap_nu hU.le t.property.1 hUR hU.le hV hUR hc hi hrc hr0 hp hfU hfU hx
        (show U ∈ Icc 0 U from ⟨hU.le, le_rfl⟩) (show U ∈ Icc 0 U from ⟨hU.le, le_rfl⟩)
        (show (t : ℝ) ∈ Icc 0 (t : ℝ) from ⟨t.property.1, le_rfl⟩) t.property
      have hg := hh.2.2.2.2.2.2.2.2.2.1
      simp only [massField_apply, he.1, he.2, hn] at hg
      have hh' := (le_add_of_nonneg_left (abs_nonneg _)).trans hg
      simpa only [K, m, ν, u, intervalExtension_apply, projIcc_of_mem hV t.property,
        massField_apply] using hh'
    have hKI : (∫ t in (a : ℝ)..v, |K t + B.innerRate|) ≤
        Lk * ((Y - B.inner) / qR + (1 + 4 / B.inner / qR) * (β * arrival U) *
          (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) := by
      obtain ⟨_hs, _hr, _hm, _hf, _hK, _hk, _he, _hn, _hh, _hg, _hmd, _hj0, _hj, _hrd, _hri, _hkd, hki⟩ := hbase
      simpa only [ha] using hki
    have hrem := hx.conformal_remainder_bound u a v hav hC.le hη hKc herr hKI
    simp only [ha] at hrem
    have hgamma (hb : 0 < β) (hgam : V = (1 + β) * arrival U) :
        let ηg := min (η / 2) (qR * β) / (1 + β)
        0 < ηg ∧ |x.2.1 u v 2 + 2 * B.innerRate| ≤
          (C + 2 * Lk * ((Y - B.inner) +
            (1 + 4 / B.inner / qR) * (C * (1 + 2 * β / η)))) * Real.exp (-ηg * V) ∧
          |x.2.1 u v 0| ≤ (LF * ((Y - B.inner) +
            (1 + 4 / B.inner / qR) * (C * (1 + 2 * β / η)))) * Real.exp (-ηg * V) := by
      have hpartial := (le_add_of_nonneg_left (abs_nonneg _)).trans hbase.2.2.2.2.2.2.2.2.2.1
      have hk := hbase.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have htime : (1 + β) * arrival U - arrival U = β * arrival U := by ring
      have hh := gamma_conformal_bound hβ hη hqR hC.le
        (show 0 ≤ 1 + 4 / B.inner / qR by have hi0 := B.inner_pos; positivity)
        hLk.le (sub_nonneg.2 hY.le) hT.1
        (by simpa only [hgam] using hpartial) (by simpa only [hgam, htime] using hk)
      have hg := hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU
      have hrange : x.1 u v 0 ∈ Icc (B.inner / 2) (2 * B.inner) := by
        have hr := abs_le.1 hbase.2.1
        constructor <;> linarith only [hr.1, hr.2, hΔr, B.inner_pos]
      have hv := hFbound (x.1 u v 0) hrange (m u v) (-Real.exp (x.1 u v 2) / (4 * ν u v))
        ⟨(hg u v).2.2.2.1.le, (hg u v).2.2.2.2⟩
      rw [← massField_lambda_eq_kappa (e := B.charge) (Λ := B.cosmological)
        x.1 x.2.1 ν hx.choose (fun w t => (hg w t).2.2.1.ne) u v] at hv
      have hrp := hbase.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hmp := hbase.2.2.2.2.2.2.2.2.2.2.1
      have hvp : |x.2.1 u v 0| ≤ LF * ((Y - B.inner) * Real.exp (-qR * (V - arrival U)) +
          (1 + 4 / B.inner / qR) * (C * (1 + β * arrival U) * Real.exp (-η * arrival U))) :=
        hv.trans ((mul_le_mul_of_nonneg_left (add_le_add hrp hmp) hLF.le).trans_eq (by ring))
      have henv := gamma_decay_envelope hβ hη hqR hC.le
        (show 0 ≤ 1 + 4 / B.inner / qR by have hi0 := B.inner_pos; positivity)
        hLF.le (sub_nonneg.2 hY.le) hT.1
      refine ⟨hh.1 hb, by simpa only [← hgam] using hh.2, ?_⟩
      exact hvp.trans (by simpa only [hgam, htime] using henv.2.2)
    exact And.intro hbase (And.intro hrem hgamma)
  refine ⟨arrival, hac, haa, hal, hpos, hscale, hmatch, hpre, hchart, ?_,
    fun U V hU hV hUR hfU {x} hx hUU he hw => by
      simpa only [and_assoc] using hfull U V hU hV hUR hfU hx hUU he hw⟩
  intro U V hU hV hUR hfU x hx hUU
  apply hhistory U V hU hV hUR hfU hx hUU
  intro w hw t het hwindow
  let hfW := hfU.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl w.property.2) le_rfl)
  have hy := hx.horizon_prefix hU.le hV hUR hw.le t.property.1 w.property.2 t.property.2 hc hi hrc hr0 hp hfU
  have hh := hclosed w t hw t.property.1 (w.property.2.trans_lt hUR) hfW hy
    (w.property.2.trans hUU) het hwindow
  have he := hy.horizon_overlap hw.le t.property.1 (w.property.2.trans_lt hUR) hU.le hV hUR
    hc hi hrc hr0 hp hfW hfU hx (show (w : ℝ) ∈ Icc 0 (w : ℝ) from ⟨hw.le, le_rfl⟩) w.property
    (show (t : ℝ) ∈ Icc 0 (t : ℝ) from ⟨t.property.1, le_rfl⟩) t.property
  have hn := hy.horizon_overlap_nu hw.le t.property.1 (w.property.2.trans_lt hUR) hU.le hV hUR
    hc hi hrc hr0 hp hfW hfU hx (show (w : ℝ) ∈ Icc 0 (w : ℝ) from ⟨hw.le, le_rfl⟩) w.property
    (show (t : ℝ) ∈ Icc 0 (t : ℝ) from ⟨t.property.1, le_rfl⟩) t.property
  simp only [massField_apply, he.1, he.2, hn] at hh
  refine ⟨by linarith only [hh.2.2.2.1, B.inner_pos], ?_,
    (by norm_num : (2 / 3 : ℝ) ≤ 3 / 4).trans hh.2.2.2.2.2.1,
    hh.2.2.2.2.1.trans (half_le_self hε.le)⟩
  have hsc := hh.1.trans (half_le_self hHe.le)
  have hb : |x.2.1 w t 1| ≤ He / Real.exp (c * t) :=
    (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hsc)
  simpa only [neg_mul, Real.exp_neg, div_eq_mul_inv] using hb

end CauchyHorizon.Background
