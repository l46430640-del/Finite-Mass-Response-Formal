import CauchyHorizon.Characteristic.OuterTrapping
import CauchyHorizon.Reduced.RadialArrival

/-! A fixed radius is reached uniquely, with uniform scale and derivative bounds. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

theorem exists_outer_level_prefix_family (B : Background) {s H dH c A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s) (hA : 0 ≤ A) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ₀ α β η : ℝ, 0 < δ₀ ∧ δ₀ ≤ r 0 / 4 ∧ 0 < α ∧ 0 < β ∧ 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ Y T j J n₀ N₀ τ L : ℝ,
      Y = B.event - α * δ ∧ j = β * δ ∧ J = 3 * δ / 16 ∧ η ≤ τ / N₀ ∧ Y ∈ Ioo B.inner B.event ∧
      0 ≤ T ∧ 0 < j ∧ 0 < J ∧ J < δ / 2 ∧ 0 < n₀ ∧ 0 < N₀ ∧ 0 < τ ∧ 0 ≤ L ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) → U * Real.exp (B.outerRate * V) ≤ δ →
        ∃! x : WaveState U V, ∃ hx :
          IsWaveIntegral hU hV B.charge B.cosmological (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x,
          ∀ (v : Icc 0 V), T ≤ (v : ℝ) → δ / 2 ≤ U * Real.exp (B.outerRate * v) →
            (∃! u : Icc 0 U, x.1 u v 0 = Y) ∧
            ∀ (u : Icc 0 U), x.1 u v 0 = Y →
              let ν := radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
              0 < (u : ℝ) ∧ (u : ℝ) < U ∧
                j ≤ u * Real.exp (B.outerRate * v) ∧ u * Real.exp (B.outerRate * v) ≤ J ∧
                n₀ ≤ u * (-ν u v) ∧ u * (-ν u v) ≤ N₀ ∧
                τ ≤ -x.2.1 u v 0 ∧ -x.2.1 u v 0 ≤ L ∧
                ((v : ℝ) ∈ Ioo 0 V → ∃ ψ : ℝ → ℝ,
                  ψ v = u ∧ HasDerivAt ψ (-x.2.1 u v 0 / ν u v) v ∧
                  (-ν u v) * (-deriv ψ v) = -x.2.1 u v 0 ∧
                  τ / N₀ ≤ -deriv ψ v / u ∧ -deriv ψ v / u ≤ L / n₀ ∧
                  ∀ᶠ t in 𝓝 (v : ℝ), ψ t ∈ Ioo 0 U ∧ t ∈ Ioo 0 V ∧
                    intervalExtension hV (intervalExtension hU x.1 (ψ t)) t 0 = Y) := by
  obtain ⟨δ₀, n, N, L, q, K, T₀, hδ₀, hδ₀r, hn, hN, hL, hq, _hK, hT₀, hsolve⟩ :=
    B.exists_outer_flux_prefix hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  let Δ := min δ₀ (4 * (B.event - B.inner) / n)
  have hΔ : 0 < Δ := lt_min hδ₀ (by positivity [B.inner_lt_event])
  refine ⟨Δ, n / 8, n / (16 * N), q * n / (6 * B.event * N ^ 2), hΔ,
    (min_le_left _ _).trans hδ₀r, by positivity, by positivity, by positivity [B.event_pos], ?_⟩
  intro δ hδ hδΔ
  have hδδ : δ ≤ δ₀ := hδΔ.trans (min_le_left _ _)
  let d := n * δ / 8
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdδ : d ≤ n * δ / 8 := le_rfl
  have hdR : d ≤ (B.event - B.inner) / 2 := by
    have hh := (le_div_iff₀ hn).1 (hδΔ.trans (min_le_right _ _))
    dsimp only [d]
    nlinarith only [hh]
  let Y := B.event - d
  have hY : Y ∈ Ioo B.inner B.event := by
    dsimp only [Y]
    exact ⟨by linarith only [hdR, B.inner_lt_event], by linarith only [hd]⟩
  have hYp : 0 < Y := B.inner_pos.trans hY.1
  let j := d / (2 * N)
  let J := 3 * d / (2 * n)
  let τ := q * j / (2 * Y)
  have hj : 0 < j := by dsimp only [j]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hJδ : J < δ / 2 := by
    dsimp only [J]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * n)).2
    nlinarith only [hdδ, mul_pos hn hδ]
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hJeq : J = 3 * δ / 16 := by dsimp only [J, d]; field_simp; norm_num
  have hspeed : q * n / (6 * B.event * N ^ 2) ≤ τ / (N * J) := by
    have heq : τ / (N * J) = q * n / (6 * Y * N ^ 2) := by
      dsimp only [τ, j, J, d]
      field_simp [hn.ne', hN.ne', hδ.ne', hYp.ne']
      ring
    rw [heq]
    exact div_le_div_of_nonneg_left (mul_pos hq hn).le (by positivity)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY.2.le (by norm_num)) (sq_nonneg N))
  have he : Tendsto (fun t : ℝ => max dH K * Real.exp (-(2 * s) * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith only [hs] : -(2 * s) < 0))).const_mul (max dH K)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (he.eventually_lt_const
    (lt_min (half_pos hd) (by positivity : 0 < q * j / 2)))
  refine ⟨Y, max T₀ T₁, j, J, n * j, N * J, τ, L,
    by dsimp only [Y, d]; ring, by dsimp only [j, d]; ring, hJeq, hspeed, hY,
    hT₀.trans (le_max_left _ _), hj, hJ, hJδ, mul_pos hn hj, mul_pos hN hJ, hτ, hL, ?_⟩
  intro U V hU hV hUR p hp f hf hfn hcb hw
  obtain ⟨x, ⟨hx, hg⟩, _⟩ := hsolve U V hU hV hUR p hp f hf hfn hcb (hw.trans hδδ)
  refine ⟨x, ⟨hx, ?_⟩, fun y hy => hy.1.incoming_unique hU hV hUR hp hf hx⟩
  intro v hv hwide
  have ht := (hT₁ v ((le_max_right _ _).trans hv)).le
  have htailr := (hrdec v v.property.1).trans
    ((mul_le_mul_of_nonneg_right (le_max_left dH K) (Real.exp_pos _).le).trans (ht.trans (min_le_left _ _)))
  have htailK := (mul_le_mul_of_nonneg_right (le_max_right dH K) (Real.exp_pos (-(2 * s) * v)).le).trans
    (ht.trans (min_le_right _ _))
  have htail := abs_le.1 htailr
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have htr := (hx.horizon_traces hU hV hUR hc (horizon_mass_integrable hs hH hc hb)
    hrc (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne') hφ hrd hp hf).2 v
  have hleft : Y < x.1 ⟨0, le_rfl, hU⟩ v 0 := by
    rw [htr]
    change Y < r v
    dsimp only [Y]
    linarith only [htail.1, hd]
  have hright : x.1 ⟨U, hU, le_rfl⟩ v 0 < Y := by
    have hgap := (hg ⟨U, hU, le_rfl⟩ v).2.2.2.2.2.1
    have hscale := mul_le_mul_of_nonneg_left hwide hn.le
    dsimp only [Y]
    nlinarith only [hgap, hscale, hdδ, htail.2, hd]
  have hanti := hx.radial_strictAnti hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 v (fun u => by
      have hh := (hg u v).1
      have hp : 0 < n * Real.exp (B.outerRate * v) := mul_pos hn (Real.exp_pos _)
      linarith only [hh, hp])
  constructor
  · have hcR : Continuous (fun t => intervalExtension hU x.1 t v 0) := by fun_prop
    have hm : Y ∈ Icc (intervalExtension hU x.1 U v 0) (intervalExtension hU x.1 0 v 0) := by
      simpa only [intervalExtension_apply, projIcc_of_mem hU (show U ∈ Icc 0 U from ⟨hU, le_rfl⟩),
        projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩)] using ⟨hright.le, hleft.le⟩
    obtain ⟨u, hu, heq⟩ := intermediate_value_Icc' hU hcR.continuousOn hm
    have heq' : x.1 ⟨u, hu⟩ v 0 = Y := by
      simpa only [intervalExtension_apply, projIcc_of_mem hU hu] using heq
    exact ⟨⟨u, hu⟩, heq', fun w hw => hanti.injective (hw.trans heq'.symm)⟩
  · intro u hu
    obtain ⟨hnu, hNu, hlam, _hrp, _hrhi, hgap, hGap, hflux⟩ := hg u v
    rw [hu] at hgap hGap hflux
    have hjbound : j ≤ u * Real.exp (B.outerRate * v) := by
      dsimp only [j]
      apply (div_le_iff₀ (by positivity : 0 < 2 * N)).2
      dsimp only [Y] at hGap
      nlinarith only [hGap, htail.1]
    have hJbound : u * Real.exp (B.outerRate * v) ≤ J := by
      dsimp only [J]
      apply (le_div_iff₀ (by positivity : 0 < 2 * n)).2
      dsimp only [Y] at hgap
      nlinarith only [hgap, htail.2]
    have hup : 0 < (u : ℝ) := (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 (hj.trans_le hjbound)
    have huU : (u : ℝ) < U := (mul_lt_mul_iff_left₀ (Real.exp_pos _)).1
      (hJbound.trans_lt (hJδ.trans_le hwide))
    have hnscale := mul_le_mul_of_nonneg_left hnu u.property.1
    have hNscale := mul_le_mul_of_nonneg_left hNu u.property.1
    have hnj := mul_le_mul_of_nonneg_left hjbound hn.le
    have hNJ := mul_le_mul_of_nonneg_left hJbound hN.le
    have hfl := hflux ((le_max_left _ _).trans hv)
    have hqj := mul_le_mul_of_nonneg_left hjbound hq.le
    have hprod : Y * x.2.1 u v 0 ≤ -(q * j / 2) := by nlinarith only [hfl, htailK, hqj]
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    have hn₀ : n * j ≤ u * (-ν u v) := by nlinarith only [hnscale, hnj]
    have hN₀ : u * (-ν u v) ≤ N * J := by nlinarith only [hNscale, hNJ]
    have hτbound : τ ≤ -x.2.1 u v 0 := by
      dsimp only [τ]
      apply (div_le_iff₀ (by positivity : 0 < 2 * Y)).2
      nlinarith only [hprod]
    have hLbound : -x.2.1 u v 0 ≤ L := (neg_le_abs _).trans hlam
    refine ⟨hup, huU, hjbound, hJbound, hn₀, hN₀, hτbound, hLbound, ?_⟩
    intro hvint
    have hνneg : ν u v < 0 := by
      have hh : 0 < n * Real.exp (B.outerRate * v) := mul_pos hn (Real.exp_pos _)
      linarith only [hnu, hh]
    obtain ⟨ψ, hψ, hdψ, hgraph⟩ := hx.exists_radial_level_chart hx.choose rfl
      (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 u v ⟨hup, huU⟩ hvint hνneg.ne
    have hdψ := hdψ.hasDerivAt
    change HasDerivAt ψ (-x.2.1 u v 0 / ν u v) v at hdψ
    have hden : 0 < (u : ℝ) * (-ν u v) := mul_pos hup (neg_pos.2 hνneg)
    have hspeed : -deriv ψ v / u = -x.2.1 u v 0 / ((u : ℝ) * (-ν u v)) := by
      rw [hdψ.deriv]
      field_simp [hup.ne', hνneg.ne]
    refine ⟨ψ, hψ, hdψ, ?_, ?_, ?_, ?_⟩
    · change (-ν u v) * (-deriv ψ v) = -x.2.1 u v 0
      rw [hdψ.deriv]
      field_simp [hνneg.ne]
    · rw [hspeed]
      apply (div_le_div_iff₀ (mul_pos hN hJ) hden).2
      nlinarith only [mul_le_mul_of_nonneg_left hN₀ hτ.le,
        mul_le_mul_of_nonneg_right hτbound (mul_pos hN hJ).le]
    · rw [hspeed]
      apply (div_le_div_iff₀ hden (mul_pos hn hj)).2
      nlinarith only [mul_le_mul_of_nonneg_right hLbound (mul_pos hn hj).le,
        mul_le_mul_of_nonneg_left hn₀ hL]
    · simpa only [hu] using hgraph

theorem exists_outer_level_prefix_le (B : Background) {s H dH c A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s) (hA : 0 ≤ A)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y T j J n₀ N₀ τ L : ℝ, 0 < δ ∧ δ ≤ Δ ∧ δ ≤ r 0 / 4 ∧ Y ∈ Ioo B.inner B.event ∧
      0 ≤ T ∧ 0 < j ∧ 0 < J ∧ J < δ / 2 ∧ 0 < n₀ ∧ 0 < N₀ ∧ 0 < τ ∧ 0 ≤ L ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) → U * Real.exp (B.outerRate * V) ≤ δ →
        ∃! x : WaveState U V, ∃ hx :
          IsWaveIntegral hU hV B.charge B.cosmological (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x,
          ∀ (v : Icc 0 V), T ≤ (v : ℝ) → δ / 2 ≤ U * Real.exp (B.outerRate * v) →
            (∃! u : Icc 0 U, x.1 u v 0 = Y) ∧
            ∀ (u : Icc 0 U), x.1 u v 0 = Y →
              let ν := radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
              0 < (u : ℝ) ∧ (u : ℝ) < U ∧
                j ≤ u * Real.exp (B.outerRate * v) ∧ u * Real.exp (B.outerRate * v) ≤ J ∧
                n₀ ≤ u * (-ν u v) ∧ u * (-ν u v) ≤ N₀ ∧
                τ ≤ -x.2.1 u v 0 ∧ -x.2.1 u v 0 ≤ L ∧
                ((v : ℝ) ∈ Ioo 0 V → ∃ ψ : ℝ → ℝ,
                  ψ v = u ∧ HasDerivAt ψ (-x.2.1 u v 0 / ν u v) v ∧
                  (-ν u v) * (-deriv ψ v) = -x.2.1 u v 0 ∧
                  τ / N₀ ≤ -deriv ψ v / u ∧ -deriv ψ v / u ≤ L / n₀ ∧
                  ∀ᶠ t in 𝓝 (v : ℝ), ψ t ∈ Ioo 0 U ∧ t ∈ Ioo 0 V ∧
                    intervalExtension hV (intervalExtension hU x.1 (ψ t)) t 0 = Y) := by
  obtain ⟨δ₀, α, β, η, hδ₀, hδ₀r, _hα, _hβ, _hη, hfamily⟩ :=
    B.exists_outer_level_prefix_family hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  let δ := min δ₀ Δ
  have hδ : 0 < δ := lt_min hδ₀ hΔ
  have hδδ : δ ≤ δ₀ := min_le_left _ _
  obtain ⟨Y, T, j, J, n₀, N₀, τ, L, _hYeq, _hjeq, _hJeq, _hspeed, hY, hrest⟩ :=
    hfamily δ hδ hδδ
  exact ⟨δ, Y, T, j, J, n₀, N₀, τ, L, hδ, min_le_right _ _, hδδ.trans hδ₀r, hY, hrest⟩


theorem exists_outer_level_prefix (B : Background) {s H dH c A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s) (hA : 0 ≤ A) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y T j J n₀ N₀ τ L : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ Y ∈ Ioo B.inner B.event ∧
      0 ≤ T ∧ 0 < j ∧ 0 < J ∧ J < δ / 2 ∧ 0 < n₀ ∧ 0 < N₀ ∧ 0 < τ ∧ 0 ≤ L ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) → U * Real.exp (B.outerRate * V) ≤ δ →
        ∃! x : WaveState U V, ∃ hx :
          IsWaveIntegral hU hV B.charge B.cosmological (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x,
          ∀ (v : Icc 0 V), T ≤ (v : ℝ) → δ / 2 ≤ U * Real.exp (B.outerRate * v) →
            (∃! u : Icc 0 U, x.1 u v 0 = Y) ∧
            ∀ (u : Icc 0 U), x.1 u v 0 = Y →
              let ν := radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
              0 < (u : ℝ) ∧ (u : ℝ) < U ∧
                j ≤ u * Real.exp (B.outerRate * v) ∧ u * Real.exp (B.outerRate * v) ≤ J ∧
                n₀ ≤ u * (-ν u v) ∧ u * (-ν u v) ≤ N₀ ∧
                τ ≤ -x.2.1 u v 0 ∧ -x.2.1 u v 0 ≤ L ∧
                ((v : ℝ) ∈ Ioo 0 V → ∃ ψ : ℝ → ℝ,
                  ψ v = u ∧ HasDerivAt ψ (-x.2.1 u v 0 / ν u v) v ∧
                  (-ν u v) * (-deriv ψ v) = -x.2.1 u v 0 ∧
                  τ / N₀ ≤ -deriv ψ v / u ∧ -deriv ψ v / u ≤ L / n₀ ∧
                  ∀ᶠ t in 𝓝 (v : ℝ), ψ t ∈ Ioo 0 U ∧ t ∈ Ioo 0 V ∧
                    intervalExtension hV (intervalExtension hU x.1 (ψ t)) t 0 = Y) := by
  obtain ⟨δ, Y, T, j, J, n, N, τ, L, hδ, _hcap, hδr, hY, hrest⟩ :=
    B.exists_outer_level_prefix_le hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
      1 zero_lt_one
  exact ⟨δ, Y, T, j, J, n, N, τ, L, hδ, hδr, hY, hrest⟩

end CauchyHorizon.Background
