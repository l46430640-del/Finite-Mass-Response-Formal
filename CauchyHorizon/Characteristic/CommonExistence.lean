import CauchyHorizon.Characteristic.EarlyExistence
import CauchyHorizon.Characteristic.LateRadiusClosure
import CauchyHorizon.Characteristic.LateScalar
import CauchyHorizon.Characteristic.LambdaDamping

/-! One profile-independent width supports actual physical solutions for every finite time. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_common_wave (B : Background) {s H dH A Apt c ε d β : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hApt : 0 ≤ Apt) (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    (hε : 0 < ε) (hεk : ε < B.innerRate) (hd : 0 < d) (hβ : 0 < β)
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
    let dν := (2 * (2 / 3) * (B.innerRate - ε) / B.outerRate) * β
    ∃ δ Δ Y U₀ N C L τ j D R₀ Olo Ohi : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ 0 < Δ ∧ Δ ≤ B.inner / 4 ∧
      B.inner < Y ∧
      0 < U₀ ∧ U₀ ≤ δ ∧ U₀ ≤ 1 ∧ 0 < N ∧ 0 < C ∧ 0 < L ∧ 0 < τ ∧ 0 < j ∧ 0 < D ∧ 0 < dν ∧
      2 * N * U₀ ^ dν / dν < Δ / 2 ∧ 0 < R₀ ∧ 0 < Olo ∧ 0 < Ohi ∧
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
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f p (volume.restrict (Icc 0 U))), U ≤ U₀ →
            ∃! x : WaveState U V, ∃ hx : IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x,
              (∀ q v, 3 * B.inner / 4 ≤ x.1 q v 0) ∧
              (∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ v : Icc 0 V, (1 + β) * arrival q ≤ v →
                B.inner - Δ < x.1 q v 0 ∧ x.1 q v 0 ≤ B.inner + Δ / 2 ∧
                -radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose q v ≤
                  2 * N * (q : ℝ) ^ (-1 + dν)) ∧
              (∀ q : Icc 0 U, 0 < (q : ℝ) → (1 + β) * arrival q ≤ V →
                let γ := (1 + β) * arrival q
                let v := projIcc 0 V hV γ
                |x.2.1 q v 1| ≤ N / 2 * Real.exp (-c * γ) ∧
                  |x.2.1 q v 2 + 2 * B.innerRate| ≤ L * Real.exp (-τ * γ) ∧
                  |x.2.1 q v 0| ≤ L * Real.exp (-τ * γ) ∧
                  |x.1 q v 2 - x.1 q (projIcc 0 V hV (arrival q)) 2 +
                    2 * B.innerRate * (γ - arrival q)| ≤ R₀) ∧
              (∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V,
                0 < t → arrival t ≤ b → (b : ℝ) ≤ (1 + β) * arrival t →
                  |x.2.2 t b 1| ≤ C * |f t| + C * t ^ (-1 + c / B.outerRate)) ∧
              (∀ cL HL : ℝ, 0 < cL → 0 ≤ HL →
                (∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ v : Icc 0 V, (1 + β) * arrival q ≤ v →
                  |x.2.1 q v 1| ≤ HL * Real.exp (-cL * v)) →
                ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V, 0 < t → (1 + β) * arrival t ≤ b →
                  |x.2.2 t b 1| ≤ 2 * C * |f t| + 2 * C * t ^ (-1 + c / B.outerRate) +
                    (2 * N * HL / ((3 * B.inner / 4) * cL)) * t ^ (-1 + dν) *
                      Real.exp (-cL * ((1 + β) * arrival t)) ∧
                  (∀ dL : ℝ, 0 < dL → dL ≤ dν → dL + cL * (1 + β) / B.outerRate ≤ c / B.outerRate →
                    |x.2.2 t b 1| ≤ 2 * C * |f t| +
                      (2 * C + (2 * N * HL / ((3 * B.inner / 4) * cL)) *
                        j ^ (-(cL * (1 + β) / B.outerRate))) *
                        t ^ (-1 + dL + cL * (1 + β) / B.outerRate))) ∧
              (∀ qRate cL HL : ℝ, 0 < cL → 0 ≤ HL → 2 * cL < qRate →
                (∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ v : Icc 0 V, (1 + β) * arrival q ≤ v →
                  |x.2.1 q v 1| ≤ HL * Real.exp (-cL * v)) →
                (∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ v : Icc 0 V, (1 + β) * arrival q ≤ v →
                  x.2.1 q v 2 ≤ -qRate) →
                let σ := qRate * (1 + β) / B.outerRate
                ∀ z u : Icc 0 U, 0 < (z : ℝ) → z ≤ u → ∀ v : Icc 0 V, (1 + β) * arrival z = v →
                  |x.2.1 u v 0| ≤ L * (D / j) ^ σ * ((z : ℝ) ^ σ * (u : ℝ) ^ (-σ)) +
                    ((3 * B.inner / 2) * HL ^ 2 / (qRate - 2 * cL)) * Real.exp (-(2 * cL) * v)) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let dν := (2 * (2 / 3) * (B.innerRate - ε) / B.outerRate) * β
  have hdν : 0 < dν := by dsimp only [dν]; positivity [sub_pos.2 hεk, B.outerRate_pos]
  have hα : 0 < 1 + β := by linarith only [hβ]
  obtain ⟨δ, Δ, Y, Ue, N, C, η, qR, Lk, LF, j, D, Olo, Ohi, hδ, hδr, hΔ, hΔr, hpot, hY, _hYΔ,
    hUe, hUeδ, hUe1, hN, hC, hη, hqR, hLk, _hLF, hj, hD, hOlo, hOhi, hsolve⟩ :=
    B.exists_early_wave hs hH hdH hdHR hA hApt hc0 hca hcs hε hεk hd hβ.le
      hℓ hJ hQ hp hcb hc hb hrc hrb hrinit hrd hrdec hOut
  have hwidth : ∀ᶠ u : ℝ in 𝓝 0, 2 * N * u ^ dν / dν < Δ / 2 :=
    (((Real.continuous_rpow_const hdν.le).const_mul (2 * N)).div_const dν).continuousAt.tendsto.eventually_lt_const
      (by simpa only [Real.zero_rpow hdν.ne', mul_zero, zero_div] using half_pos hΔ)
  obtain ⟨U₀, hU₀, hU₀e, hsmall⟩ := ((eventually_lt_nhds hUe).and hwidth).exists_gt
  have hUδ : U₀ ≤ δ := hU₀e.le.trans hUeδ
  have hU1 : U₀ ≤ 1 := hU₀e.le.trans hUe1
  let Z := (Y - B.inner) + (1 + 4 / B.inner / qR) * (C * (1 + 2 * β / η))
  let L := max 1 (max (C + 2 * Lk * Z) (LF * Z))
  let τ := min (η / 2) (qR * β) / (1 + β)
  have hL : 0 < L := zero_lt_one.trans_le (le_max_left _ _)
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  let R₀ := C / η + 2 * (Lk * ((Y - B.inner) / qR + (1 + 4 / B.inner / qR) *
    (C * ((2 * β / η) * (1 + 2 * β / η)))))
  have hR₀ : 0 < R₀ := by dsimp only [R₀]; positivity [sub_pos.2 hY, B.inner_pos]
  refine ⟨δ, Δ, Y, U₀, N, C, L, τ, j, D, R₀, Olo, Ohi, hδ, hδr, hΔ, hΔr, hY, hU₀, hUδ, hU1,
    hN, hC, hL, hτ, hj, hD, hdν, hsmall, hR₀, hOlo, hOhi, ?_⟩
  intro f hf hfn hpoint
  obtain ⟨arrival, hac, haa, hal, hpos, hscale, hmatch, hpre, hhistory, hearlyfloor, hex⟩ := hsolve f hf hfn hpoint
  have hsub : Ioc 0 U₀ ⊆ Ioc 0 Ue := Ioc_subset_Ioc le_rfl hU₀e.le
  have hgamma (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x) (hUU : U ≤ U₀) :
      ∀ q : Icc 0 U, 0 < (q : ℝ) → (1 + β) * arrival q ≤ V →
        let γ := (1 + β) * arrival q
        let v := projIcc 0 V hV γ
        |x.1 q v 0 - B.inner| ≤ Δ / 2 ∧
        -radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose q v ≤
          N * (q : ℝ) ^ (-1 + dν) ∧
        |x.2.1 q v 1| ≤ N / 2 * Real.exp (-c * γ) ∧
        |x.2.1 q v 2 + 2 * B.innerRate| ≤ L * Real.exp (-τ * γ) ∧
        |x.2.1 q v 0| ≤ L * Real.exp (-τ * γ) ∧
        |x.1 q v 2 - x.1 q (projIcc 0 V hV (arrival q)) 2 +
          2 * B.innerRate * (γ - arrival q)| ≤ R₀ := by
    intro q hq hqV
    have hqe : (q : ℝ) ≤ Ue := q.property.2.trans (hUU.trans hU₀e.le)
    have hT := hpos q ⟨hq, hqe⟩
    have hG : 0 ≤ (1 + β) * arrival q := mul_nonneg hα.le hT.le
    have he : arrival q ≤ (1 + β) * arrival q := by nlinarith only [hβ, hT]
    let hfq := hfU.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl q.property.2) le_rfl)
    obtain ⟨y, ⟨hy, _hyr, hye, _hmore⟩, _huniq⟩ :=
      hex q ((1 + β) * arrival q) hq hG (q.property.2.trans_lt hUR) hfq hqe le_rfl
    obtain ⟨hsc, hr, _hm, _hr, _hK, _hk, _hE, hn, _hh, _hl, _hmd, _hJ0, _hJ,
      _hrp, _hri, _hKp, _hKi, hrem, _hfactor, hg⟩ := hye he
    have hn := hn rfl
    have hg := hg hβ rfl
    have heq := hy.horizon_overlap hq.le hG (q.property.2.trans_lt hUR) hU.le hV hUR
      hc hi hrc hr0 hp hfq hfU hx (show (q : ℝ) ∈ Icc 0 (q : ℝ) from ⟨hq.le, le_rfl⟩)
      q.property (show (1 + β) * arrival q ∈ Icc 0 ((1 + β) * arrival q) from ⟨hG, le_rfl⟩)
      ⟨hG, hqV⟩
    have hneq := hy.horizon_overlap_nu hq.le hG (q.property.2.trans_lt hUR) hU.le hV hUR
      hc hi hrc hr0 hp hfq hfU hx (show (q : ℝ) ∈ Icc 0 (q : ℝ) from ⟨hq.le, le_rfl⟩)
      q.property (show (1 + β) * arrival q ∈ Icc 0 ((1 + β) * arrival q) from ⟨hG, le_rfl⟩)
      ⟨hG, hqV⟩
    rw [heq.1] at hr
    rw [hneq] at hn
    rw [heq.2] at hsc
    have hsc' : |x.2.1 q ⟨(1 + β) * arrival q, hG, hqV⟩ 1| ≤ N / 2 * Real.exp (-c * ((1 + β) * arrival q)) := by
      have hh : |x.2.1 q ⟨(1 + β) * arrival q, hG, hqV⟩ 1| ≤
          (N / 2) / Real.exp (c * ((1 + β) * arrival q)) :=
        (le_div_iff₀ (Real.exp_pos (c * ((1 + β) * arrival q)))).2
        (by simpa only [mul_comm] using hsc)
      simpa only [neg_mul, Real.exp_neg, div_eq_mul_inv] using hh
    have hconf := hg.2.1
    have hlam := hg.2.2
    rw [heq.2] at hconf hlam
    have hconf' := hconf.trans (mul_le_mul_of_nonneg_right
      (show C + 2 * Lk * Z ≤ L from (le_max_left _ _).trans (le_max_right _ _)) (Real.exp_pos _).le)
    have hlam' := hlam.trans (mul_le_mul_of_nonneg_right
      (show LF * Z ≤ L from (le_max_right _ _).trans (le_max_right _ _)) (Real.exp_pos _).le)
    have heqEntry := (hy.horizon_overlap hq.le hG (q.property.2.trans_lt hUR) hU.le hV hUR
      hc hi hrc hr0 hp hfq hfU hx (show (q : ℝ) ∈ Icc 0 (q : ℝ) from ⟨hq.le, le_rfl⟩)
      q.property (show arrival q ∈ Icc 0 ((1 + β) * arrival q) from ⟨hT.le, he⟩)
      ⟨hT.le, he.trans hqV⟩).1
    rw [projIcc_of_mem hG ⟨hT.le, he⟩, heq.1, heqEntry] at hrem
    have hpoly := mul_le_mul_of_nonneg_left (quadratic_mul_exp_bound hη hβ.le hT.le) hC.le
    have hpoly' : (β * arrival q) * (C * (1 + β * arrival q) * Real.exp (-η * arrival q)) ≤
        C * ((2 * β / η) * (1 + 2 * β / η)) := hpoly.trans_eq' (by ring)
    have hexp : Real.exp (-η * arrival q) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith only [hη, hT])
    have hweighted := mul_le_mul_of_nonneg_left hpoly'
      (show 0 ≤ 1 + 4 / B.inner / qR by positivity [B.inner_pos])
    rw [← mul_assoc] at hweighted
    have hrest := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl ((Y - B.inner) / qR)) hweighted) hLk.le) (by norm_num : (0 : ℝ) ≤ 2)
    have hrem' := hrem.trans (add_le_add
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (div_nonneg hC.le hη.le))
      hrest)
    simpa only [projIcc_of_mem hV (show (1 + β) * arrival q ∈ Icc 0 V from ⟨hG, hqV⟩)] using
      And.intro hr (And.intro hn (And.intro hsc' (And.intro hconf' (And.intro hlam'
        (by simpa only [projIcc_of_mem hV ⟨hT.le, he.trans hqV⟩] using hrem')))))
  have hlate (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x) (hUU : U ≤ U₀) :
      ∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ v : Icc 0 V, (1 + β) * arrival q ≤ v →
        B.inner - Δ < x.1 q v 0 ∧ x.1 q v 0 ≤ B.inner + Δ / 2 ∧
        -radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose q v ≤
          2 * N * (q : ℝ) ^ (-1 + dν) := by
    have hdom : Ioc 0 U ⊆ Ioc 0 Ue := Ioc_subset_Ioc le_rfl (hUU.trans hU₀e.le)
    have hsm : 2 * N * U ^ dν / dν < Δ / 2 :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hU.le hUU hdν.le)
          (by positivity : 0 ≤ 2 * N)) hdν.le).trans_lt hsmall
    exact hx.late_radius_closed B hU hV hUR hp hfU hΔ hΔr hN.le hdν hpot hsm
      ((hac.mono hdom).const_mul (1 + β))
      (fun a ha b hb hab => mul_lt_mul_of_pos_left (haa (hdom ha) (hdom hb) hab) hα)
      (hal.const_mul_atTop hα) (fun q hq => mul_nonneg hα.le (hpos q (hdom hq)).le)
      (fun q v => (hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU q v).2.2.1)
      (fun q hq hqV => ⟨(hgamma U V hU hV hUR hfU hx hUU q hq hqV).1,
        (hgamma U V hU hV hUR hfU hx hUU q hq hqV).2.1⟩)
  have hfloor (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hfU : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hfU) x) (hUU : U ≤ U₀)
      (q : Icc 0 U) (v : Icc 0 V) : 3 * B.inner / 4 ≤ x.1 q v 0 := by
    by_cases hv : (v : ℝ) ≤ (1 + β) * arrival U
    · have hy := hx.horizon_prefix hU.le hV hUR hU.le v.property.1 le_rfl v.property.2 hc hi hrc hr0 hp hfU
      have hh := hearlyfloor U v hU v.property.1 hUR hfU hy (hUU.trans hU₀e.le) hv
        q ⟨v, v.property.1, le_rfl⟩
      have he := (hy.horizon_overlap hU.le v.property.1 hUR hU.le hV hUR hc hi hrc hr0 hp hfU hfU hx
        q.property q.property (show (v : ℝ) ∈ Icc 0 (v : ℝ) from ⟨v.property.1, le_rfl⟩) v.property).1
      rwa [he] at hh
    · have hh := (hlate U V hU hV hUR hfU hx hUU ⟨U, hU.le, le_rfl⟩ hU v (not_le.1 hv).le).1
      have ha := (hx.radial_strictAnti hx.choose rfl
        (incomingWave_constraint_data hU.le hUR hp hfU (horizonPhi h r 0)).1 v
        (fun w => (hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU w v).2.2.1)).antitone
        (show q ≤ (⟨U, hU.le, le_rfl⟩ : Icc 0 U) from q.property.2)
      linarith only [hh, ha, hΔr]
  refine ⟨arrival, hac.mono hsub, haa.mono hsub, hal, fun u hu => hpos u (hsub hu),
    (fun u hu => hscale u (hsub hu)),
    (fun U V hU hV hUR hfU {x} hx hUU => hmatch U V hU hV hUR hfU hx (hUU.trans hU₀e.le)),
    (fun {_ _} hU hV hUR hfU {_} hx u hu => hpre hU hV hUR hfU hx u (hsub hu)), ?_⟩
  intro U V hU hV hUR hfU hUU
  have hfnU := (scalar_prefix_norm_le (hUU.trans hUδ) hf).trans hfn
  have hρ : 0 < 3 * B.inner / 4 := by positivity [B.inner_pos]
  obtain ⟨step, hstep, _hstep1, hext⟩ :=
    exists_horizon_row_extension hV (B.inner_pos.trans hrinit) hc hi hrc hr0 hφ hrd hρ hA
  let P := fun t : ℝ => ∃ ht : 0 ≤ t, ∃ x : WaveState U t,
    IsWaveIntegral hU.le ht B.charge B.cosmological
      (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological t hc hi hrc hr0)
      (incomingWaveVelocity hUR hp hfU) x
  have hbase : P 0 := by
    obtain ⟨x, ⟨hx, _⟩, _⟩ := hex U 0 hU le_rfl hUR hfU (hUU.trans hU₀e.le)
      (mul_nonneg hα.le (hpos U ⟨hU, hUU.trans hU₀e.le⟩).le)
    exact ⟨le_rfl, x, hx⟩
  have hnext (t w : ℝ) (_ht : 0 ≤ t) (hw : 0 ≤ w) (htw : t + w ≤ V) (hws : w ≤ step)
      (htP : P t) : P (t + w) := by
    obtain ⟨ht, x, hx⟩ := htP
    obtain ⟨y, hy, _hmatch, _hfloor⟩ := hext hU.le ht hw (hUU.trans hU1) hws htw hUR hp hfU hfnU hx
      (hfloor U t hU ht hUR hfU hx hUU)
    exact ⟨add_nonneg ht hw, y, hy⟩
  obtain ⟨_hV, x, hx⟩ := interval_subdivision_induction hV hstep hbase hnext
  have hpre := hhistory U V hU hV hUR hfU hx (hUU.trans hU₀e.le)
  refine ⟨x, ⟨hx, hfloor U V hU hV hUR hfU hx hUU, hlate U V hU hV hUR hfU hx hUU,
    (fun q hq hqV => (hgamma U V hU hV hUR hfU hx hUU q hq hqV).2.2), hpre, ?_, ?_⟩, ?_⟩
  · intro cL HL hcL hHL hscalar
    filter_upwards [hpre, hx.scalar_segment_bound hU.le hV hUR hp hfU
      (R := 3 * B.inner / 2) hρ hcL hHL, ae_restrict_mem measurableSet_Icc] with t ht hs htm
    intro b ht0 htb
    let q : Icc 0 U := ⟨t, htm⟩
    have hT := hpos t ⟨ht0, htm.2.trans (hUU.trans hU₀e.le)⟩
    have hG : 0 ≤ (1 + β) * arrival t := mul_nonneg hα.le hT.le
    have hgm : (1 + β) * arrival t ∈ Icc 0 V := ⟨hG, htb.trans b.property.2⟩
    let a : Icc 0 V := ⟨(1 + β) * arrival t, hgm⟩
    have hentry : arrival t ≤ a := by dsimp only [a]; nlinarith only [hβ, hT]
    have htrace := ht a ht0 hentry le_rfl
    have hrγ := (hgamma U V hU hV hUR hfU hx hUU q ht0 hgm.2).1
    simp only [q, projIcc_of_mem hV hgm] at hrγ
    have hrhi : x.1 q a 0 ≤ 3 * B.inner / 2 := by
      have hh := (abs_le.1 hrγ).2
      linarith only [hh, hΔr, B.inner_pos]
    have hh := hs a b htb (2 * N * t ^ (-1 + dν))
      (mul_nonneg (by positivity) (Real.rpow_nonneg htm.1 _))
    simp only [projIcc_of_mem hU.le htm] at hh
    have hb := hh (hfloor U V hU hV hUR hfU hx hUU q b) hrhi
      (fun v hv => by
        rw [abs_of_neg (hx.interior_gauge hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU q v).2.2.1]
        exact (hlate U V hU hV hUR hfU hx hUU q ht0 v hv.1).2.2)
      (fun v hv => hscalar q ht0 v hv.1)
    have hratio : (3 * B.inner / 2) / (3 * B.inner / 4) = 2 := by
      field_simp [B.inner_pos.ne']
      ring
    rw [hratio] at hb
    have hbnd : |x.2.2 t b 1| ≤ 2 * C * |f t| + 2 * C * t ^ (-1 + c / B.outerRate) +
        (2 * N * HL / ((3 * B.inner / 4) * cL)) * t ^ (-1 + dν) *
          Real.exp (-cL * ((1 + β) * arrival t)) :=
      (hb.trans (add_le_add (mul_le_mul_of_nonneg_left htrace (by norm_num : (0 : ℝ) ≤ 2))
        le_rfl)).trans_eq (by dsimp only [a]; ring)
    refine ⟨hbnd, ?_⟩
    intro dL _hdL hdn hgap
    exact hbnd.trans (arrival_scalar_power B.outerRate_pos ht0 (htm.2.trans (hUU.trans hU1)) hj
      hC.le (by positivity) hcL.le hα.le hdn hgap
      (hscale t ⟨ht0, htm.2.trans (hUU.trans hU₀e.le)⟩).1)
  · intro qRate cL HL hcL hHL hqc hscalar hell σ z u hz hzu v hγz
    have hq : 0 < qRate := (by positivity : 0 < 2 * cL).trans hqc
    have hu : 0 < (u : ℝ) := hz.trans_le hzu
    have hze : (z : ℝ) ∈ Ioc 0 Ue := ⟨hz, z.property.2.trans (hUU.trans hU₀e.le)⟩
    have hue : (u : ℝ) ∈ Ioc 0 Ue := ⟨hu, u.property.2.trans (hUU.trans hU₀e.le)⟩
    have hγu : (1 + β) * arrival u ≤ v :=
      (mul_le_mul_of_nonneg_left (haa.antitoneOn hze hue hzu) hα.le).trans_eq hγz
    have hG : 0 ≤ (1 + β) * arrival u := mul_nonneg hα.le (hpos u hue).le
    have hgm : (1 + β) * arrival u ∈ Icc 0 V := ⟨hG, hγu.trans v.property.2⟩
    let a : Icc 0 V := ⟨(1 + β) * arrival u, hgm⟩
    have hl0 := (hgamma U V hU hV hUR hfU hx hUU u hu hgm.2).2.2.2.2.1
    simp only [projIcc_of_mem hV hgm] at hl0
    have he0 : Real.exp (-τ * ((1 + β) * arrival u)) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hτ.le) hG)
    have hlam0 : |x.2.1 u a 0| ≤ L :=
      hl0.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he0 hL.le)
    have hb := hx.lambda_damping_exp hU.le hV hUR hc hi hrc hr0 hφ hrd hp hfU
      hcL hqc hHL u a v hγu (R := 3 * B.inner / 2) (by
        intro w hw
        have hr := (hlate U V hU hV hUR hfU hx hUU u hu w hw.1).2.1
        linarith only [hr, hΔr, B.inner_pos])
      (fun w hw => hscalar u hu w hw.1) (fun w hw => hell u hu w hw.1)
    have hk := arrival_damping_kernel B.outerRate_pos hα.le hq.le hz hu hj
      (hscale z hze).1 (hscale u hue).2
    rw [hγz] at hk
    exact (hb.trans (add_le_add (mul_le_mul hk hlam0 (abs_nonneg _) (by positivity)) le_rfl)).trans_eq
      (by ring)
  · intro y hy
    exact hy.choose.incoming_unique hU.le hV hUR hp hfU hx

end CauchyHorizon.Background
