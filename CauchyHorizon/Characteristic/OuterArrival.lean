import CauchyHorizon.Characteristic.OuterLevel
import CauchyHorizon.Characteristic.PhysicalOverlap
import CauchyHorizon.Analysis.ArrivalInverse

/-! One late-time arrival function from compatible physical outer rectangles. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

theorem exists_outer_arrival_family (B : Background) {s H dH c A : ℝ}
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
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ Y T j J b C ε : ℝ,
      Y = B.event - α * δ ∧ j = β * δ ∧ J = 3 * δ / 16 ∧ η ≤ b ∧ Y ∈ Ioo B.inner B.event ∧
      0 ≤ T ∧ 0 < j ∧ 0 < J ∧ J < δ / 2 ∧ 0 < b ∧ 0 ≤ C ∧ 0 < ε ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (_hf : MemLp f p (volume.restrict (Icc 0 δ))),
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) →
        ∃ g inv : ℝ → ℝ, ContinuousOn g (Ioi T) ∧ StrictAntiOn g (Ioi T) ∧ Tendsto g atTop (𝓝 0) ∧
          ContinuousOn inv (Ioo 0 ε) ∧ Tendsto inv (𝓝[>] (0 : ℝ)) atTop ∧
          (∀ u ∈ Ioo 0 ε, T + 1 < inv u ∧ g (inv u) = u ∧ HasDerivAt inv (deriv g (inv u))⁻¹ u) ∧
          (∀ t ∈ Ioi (T + 1), inv (g t) = t) ∧
          ∀ t ∈ Ioi T, 0 < g t ∧ j ≤ g t * Real.exp (B.outerRate * t) ∧
            g t * Real.exp (B.outerRate * t) ≤ J ∧ b ≤ -deriv g t / g t ∧ -deriv g t / g t ≤ C ∧
            ∃ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
              (hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x) (u : Icc 0 U) (v : Icc 0 V),
              (u : ℝ) = g t ∧ (v : ℝ) = t ∧ (u : ℝ) ∈ Ioo 0 U ∧ (v : ℝ) ∈ Ioo 0 V ∧
                x.1 u v 0 = Y ∧ U * Real.exp (B.outerRate * V) = δ ∧
                let ν := radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                HasDerivAt g (-x.2.1 u v 0 / ν u v) t ∧
                  (-ν u v) * (-deriv g t) = -x.2.1 u v 0 := by
  classical
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ₀, α, β, η, hδ₀, hδ₀r, hα, hβ, hη, hfamily⟩ :=
    B.exists_outer_level_prefix_family hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  refine ⟨δ₀, α, β, η, hδ₀, hδ₀r, hα, hβ, hη, ?_⟩
  intro δ hδ hδδ
  have hδr : δ ≤ r 0 / 4 := hδδ.trans hδ₀r
  obtain ⟨Y, T, j, J, n₀, N₀, τ, L, hYeq, hjeq, hJeq, hηspeed,
    hY, hT, hj, hJ, hJδ, hn₀, hN₀, hτ, hL, hsolve⟩ := hfamily δ hδ hδδ
  let ε := j * Real.exp (-B.outerRate * (T + 1)) / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  refine ⟨Y, T, j, J, τ / N₀, L / n₀, ε, hYeq, hjeq, hJeq, hηspeed, hY, hT, hj, hJ, hJδ,
    div_pos hτ hN₀, div_nonneg hL hn₀.le, hε, ?_⟩
  intro p hp f hf hfn hcb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let γ := Real.log (4 / 3 : ℝ) / a
  have hγ : 0 < γ := div_pos (Real.log_pos (by norm_num)) ha
  let V := fun t : Ioi T => (t : ℝ) + γ
  let U := fun t : Ioi T => δ * Real.exp (-a * V t)
  have ht0 (t : Ioi T) : 0 < (t : ℝ) := hT.trans_lt t.property
  have hV (t : Ioi T) : 0 ≤ V t := (add_pos (ht0 t) hγ).le
  have htV (t : Ioi T) : (t : ℝ) < V t := lt_add_of_pos_right _ hγ
  have hU (t : Ioi T) : 0 ≤ U t := mul_nonneg hδ.le (Real.exp_pos _).le
  have hUδ (t : Ioi T) : U t ≤ δ := mul_le_of_le_one_right hδ.le
    (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 ha.le) (hV t)))
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  have hUR (t : Ioi T) : U t < r 0 := (hUδ t).trans_lt (hδr.trans_lt (by linarith only [hrp]))
  have hw (t : Ioi T) : U t * Real.exp (a * V t) = δ := by
    dsimp only [U]
    rw [mul_assoc, ← Real.exp_add, show -a * V t + a * V t = 0 by ring, Real.exp_zero, mul_one]
  have hmid (t : Ioi T) : U t * Real.exp (a * t) = 3 * δ / 4 := by
    have he : -a * V t + a * t = -Real.log (4 / 3 : ℝ) := by
      dsimp only [V, γ]
      field_simp
      ring
    dsimp only [U]
    rw [mul_assoc, ← Real.exp_add, he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    ring
  let hfU (t : Ioi T) := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (hUδ t)) le_rfl)
  choose X hX using fun t : Ioi T => (hsolve (U t) (V t) (hU t) (hV t) (hUR t) p hp f (hfU t)
    ((scalar_prefix_norm_le (hUδ t) hf).trans hfn) hcb (hw t).le).exists
  choose hx hg using hX
  let tv (t : Ioi T) : Icc 0 (V t) := ⟨t, (ht0 t).le, (htV t).le⟩
  have hrow (t : Ioi T) : δ / 2 ≤ U t * Real.exp (B.outerRate * tv t) := by
    change δ / 2 ≤ U t * Real.exp (a * t)
    rw [hmid t]
    linarith only [hδ]
  choose z hz hzu using fun t : Ioi T => (hg t (tv t) t.property.le (hrow t)).1
  have hbnd (t : Ioi T) := (hg t (tv t) t.property.le (hrow t)).2 (z t) (hz t)
  let g := fun t : ℝ => if ht : T < t then (z ⟨t, ht⟩ : ℝ) else 0
  have hgval (t : Ioi T) : g t = z t := by
    dsimp only [g]
    rw [dif_pos (show T < (t : ℝ) from t.property)]
  have hD (t : Ioi T) :
      let ν := radialNuField (hV t) B.charge B.cosmological
        (incomingWaveCurve (hU t) (hUR t) hp (hfU t) (horizonPhi h r 0)) (X t).1 (hx t).choose
      HasDerivAt g (-(X t).2.1 (z t) (tv t) 0 / ν (z t) (tv t)) t ∧
        (-ν (z t) (tv t)) * (-deriv g t) = -(X t).2.1 (z t) (tv t) 0 ∧
        τ / N₀ ≤ -deriv g t / g t ∧ -deriv g t / g t ≤ L / n₀ := by
    obtain ⟨_hzpos, _hzU, _hzj, _hzJ, _hzn, _hzN, _hzt, _hzL, hchart⟩ := hbnd t
    obtain ⟨ψ, _hψ, hdψ, hJac, hlow, hhigh, hgraph⟩ := hchart ⟨ht0 t, htV t⟩
    have hwindow : ∀ᶠ w in 𝓝 (t : ℝ), T < w ∧ w ∈ Ioo 0 (V t) ∧ J < U t * Real.exp (a * w) := by
      have htime : ∀ᶠ w in 𝓝 (t : ℝ), w ∈ Ioi T := Ioi_mem_nhds t.property
      have hinside : ∀ᶠ w in 𝓝 (t : ℝ), w ∈ Ioo 0 (V t) := Ioo_mem_nhds (ht0 t) (htV t)
      have he : Continuous (fun w : ℝ => U t * Real.exp (a * w)) := by fun_prop
      have hspace := (he.continuousAt (x := (t : ℝ))).tendsto.eventually_const_lt (show J < U t * Real.exp (a * t) by
        rw [hmid t]; linarith only [hJδ, hδ])
      exact htime.and (hinside.and hspace)
    have heq : g =ᶠ[𝓝 (t : ℝ)] ψ := by
      filter_upwards [hwindow, hgraph] with w hw hgraphw
      let tw : Ioi T := ⟨w, hw.1⟩
      have hzw : (z tw : ℝ) < U t := (mul_lt_mul_iff_left₀ (Real.exp_pos (a * w))).1
        ((hbnd tw).2.2.2.1.trans_lt hw.2.2)
      have huz : (z tw : ℝ) ∈ Icc 0 (U t) := ⟨(z tw).property.1, hzw.le⟩
      have hvw : w ∈ Icc 0 (V t) := ⟨hw.2.1.1.le, hw.2.1.2.le⟩
      have ho := (hx tw).horizon_overlap (hU tw) (hV tw) (hUR tw) (hU t) (hV t) (hUR t)
        hc hi hrc hr0 hp (hfU tw) (hfU t) (hx t) (z tw).property huz (tv tw).property hvw
      have hrad : (X t).1 ⟨z tw, huz⟩ ⟨w, hvw⟩ 0 = Y := (congrArg (fun q : WaveVector => q 0) ho.1).symm.trans (hz tw)
      have hψmem : ψ w ∈ Icc 0 (U t) := ⟨hgraphw.1.1.le, hgraphw.1.2.le⟩
      have hrψ : (X t).1 ⟨ψ w, hψmem⟩ ⟨w, hvw⟩ 0 = Y := by
        simpa only [intervalExtension_apply, projIcc_of_mem (hU t) hψmem,
          projIcc_of_mem (hV t) hvw] using hgraphw.2.2
      have hanti := (hx t).radial_strictAnti (hx t).choose rfl
        (incomingWave_constraint_data (hU t) (hUR t) hp (hfU t) (horizonPhi h r 0)).1 ⟨w, hvw⟩
        (fun u => ((hx t).interior_gauge (hU t) (hV t) (hUR t) hc hi hrc hr0 hφ hrd hp (hfU t) u ⟨w, hvw⟩).2.2.1)
      have he := congrArg Subtype.val (hanti.injective (hrad.trans hrψ.symm))
      exact (hgval tw).trans he
    have hdg := hdψ.congr_of_eventuallyEq heq
    have hder : deriv g t = deriv ψ t := hdg.deriv.trans hdψ.deriv.symm
    refine ⟨hdg, ?_, ?_, ?_⟩
    · simpa only [hder] using hJac
    · simpa only [hder, hgval t] using hlow
    · simpa only [hder, hgval t] using hhigh
  have hcont : ContinuousOn g (Ioi T) := fun t ht => (hD ⟨t, ht⟩).1.continuousAt.continuousWithinAt
  have hdiff : ∀ t ∈ Ioi T, DifferentiableAt ℝ g t ∧ deriv g t < 0 := by
    intro t ht
    refine ⟨(hD ⟨t, ht⟩).1.differentiableAt, ?_⟩
    have hpos : 0 < g t := by rw [hgval ⟨t, ht⟩]; exact (hbnd ⟨t, ht⟩).1
    have hspeed : 0 < -deriv g t / g t := (div_pos hτ hN₀).trans_le (hD ⟨t, ht⟩).2.2.1
    have hneg := (div_pos_iff_of_pos_right hpos).1 hspeed
    linarith only [hneg]
  have hanti : StrictAntiOn g (Ioi T) := strictAntiOn_of_deriv_neg (convex_Ioi _) hcont
    (fun t ht => (hdiff t (by simpa only [interior_Ioi] using ht)).2)
  have hlim : Tendsto g atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => J * Real.exp (-a * t)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha))).const_mul J
    apply squeeze_zero' _ _ he
    · filter_upwards [eventually_gt_atTop T] with t ht
      rw [hgval ⟨t, ht⟩]
      exact (hbnd ⟨t, ht⟩).1.le
    · filter_upwards [eventually_gt_atTop T] with t ht
      have hh := mul_le_mul_of_nonneg_right (hbnd ⟨t, ht⟩).2.2.2.1 (Real.exp_pos (-a * t)).le
      have hex : Real.exp (a * t) * Real.exp (-a * t) = 1 := by
        rw [← Real.exp_add, show a * t + -a * t = 0 by ring, Real.exp_zero]
      rw [mul_assoc, hex, mul_one] at hh
      simpa only [hgval ⟨t, ht⟩] using hh
  have hpos : ∀ t ∈ Ioi T, 0 < g t := by
    intro t ht
    rw [hgval ⟨t, ht⟩]
    exact (hbnd ⟨t, ht⟩).1
  have ht₀ : T < T + 1 := by linarith
  obtain ⟨inv, hcinv, hlinv, hright, hleft⟩ := exists_arrival_inverse hcont hanti hlim hpos hdiff ht₀
  have hεg : ε < g (T + 1) := by
    have hh := mul_le_mul_of_nonneg_right (hbnd ⟨T + 1, ht₀⟩).2.2.1 (Real.exp_pos (-a * (T + 1))).le
    have hex : Real.exp (a * (T + 1)) * Real.exp (-a * (T + 1)) = 1 := by
      rw [← Real.exp_add, show a * (T + 1) + -a * (T + 1) = 0 by ring, Real.exp_zero]
    change j * Real.exp (-a * (T + 1)) ≤ (z ⟨T + 1, ht₀⟩ : ℝ) * Real.exp (a * (T + 1)) * Real.exp (-a * (T + 1)) at hh
    rw [mul_assoc, hex, mul_one, ← hgval ⟨T + 1, ht₀⟩] at hh
    have hp : 0 < j * Real.exp (-a * (T + 1)) := mul_pos hj (Real.exp_pos _)
    dsimp only [ε]
    linarith only [hh, hp]
  have hsub : Ioo 0 ε ⊆ Ioo 0 (g (T + 1)) := Ioo_subset_Ioo le_rfl hεg.le
  refine ⟨g, inv, hcont, hanti, hlim, hcinv.mono hsub, hlinv,
    fun u hu => hright u (hsub hu), hleft, ?_⟩
  intro t ht
  let tt : Ioi T := ⟨t, ht⟩
  obtain ⟨hzpos, hzU, hzj, hzJ, _hzn, _hzN, _hzt, _hzL, _hchart⟩ := hbnd tt
  have hgt : g t = z tt := hgval tt
  refine ⟨by simpa only [hgt] using hzpos, by simpa only [hgt] using hzj,
    by simpa only [hgt] using hzJ, (hD tt).2.2.1, (hD tt).2.2.2,
    U tt, V tt, hU tt, hV tt, hUR tt, hfU tt, X tt, hx tt, z tt, tv tt,
    hgt.symm, rfl, ⟨hzpos, hzU⟩, ⟨ht0 tt, htV tt⟩, hz tt, hw tt, (hD tt).1, (hD tt).2.1⟩

theorem exists_outer_arrival_le (B : Background) {s H dH c A : ℝ}
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
    ∃ δ Y T j J b C ε : ℝ, 0 < δ ∧ δ ≤ Δ ∧ δ ≤ r 0 / 4 ∧ Y ∈ Ioo B.inner B.event ∧
      0 ≤ T ∧ 0 < j ∧ 0 < J ∧ J < δ / 2 ∧ 0 < b ∧ 0 ≤ C ∧ 0 < ε ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (_hf : MemLp f p (volume.restrict (Icc 0 δ))),
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) →
        ∃ g inv : ℝ → ℝ, ContinuousOn g (Ioi T) ∧ StrictAntiOn g (Ioi T) ∧ Tendsto g atTop (𝓝 0) ∧
          ContinuousOn inv (Ioo 0 ε) ∧ Tendsto inv (𝓝[>] (0 : ℝ)) atTop ∧
          (∀ u ∈ Ioo 0 ε, T + 1 < inv u ∧ g (inv u) = u ∧ HasDerivAt inv (deriv g (inv u))⁻¹ u) ∧
          (∀ t ∈ Ioi (T + 1), inv (g t) = t) ∧
          ∀ t ∈ Ioi T, 0 < g t ∧ j ≤ g t * Real.exp (B.outerRate * t) ∧
            g t * Real.exp (B.outerRate * t) ≤ J ∧ b ≤ -deriv g t / g t ∧ -deriv g t / g t ≤ C ∧
            ∃ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
              (hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x) (u : Icc 0 U) (v : Icc 0 V),
              (u : ℝ) = g t ∧ (v : ℝ) = t ∧ (u : ℝ) ∈ Ioo 0 U ∧ (v : ℝ) ∈ Ioo 0 V ∧
                x.1 u v 0 = Y ∧ U * Real.exp (B.outerRate * V) = δ ∧
                let ν := radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                HasDerivAt g (-x.2.1 u v 0 / ν u v) t ∧
                  (-ν u v) * (-deriv g t) = -x.2.1 u v 0 := by
  obtain ⟨δ₀, α, β, η, hδ₀, hδ₀r, _hα, _hβ, _hη, hfamily⟩ :=
    B.exists_outer_arrival_family hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  let δ := min δ₀ Δ
  have hδ : 0 < δ := lt_min hδ₀ hΔ
  have hδδ : δ ≤ δ₀ := min_le_left _ _
  obtain ⟨Y, T, j, J, b, C, ε, _hYeq, _hjeq, _hJeq, _hspeed, hY, hrest⟩ :=
    hfamily δ hδ hδδ
  exact ⟨δ, Y, T, j, J, b, C, ε, hδ, min_le_right _ _, hδδ.trans hδ₀r, hY, hrest⟩


theorem exists_outer_arrival (B : Background) {s H dH c A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s) (hA : 0 ≤ A) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y T j J b C ε : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ Y ∈ Ioo B.inner B.event ∧
      0 ≤ T ∧ 0 < j ∧ 0 < J ∧ J < δ / 2 ∧ 0 < b ∧ 0 ≤ C ∧ 0 < ε ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (_hf : MemLp f p (volume.restrict (Icc 0 δ))),
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) →
        ∃ g inv : ℝ → ℝ, ContinuousOn g (Ioi T) ∧ StrictAntiOn g (Ioi T) ∧ Tendsto g atTop (𝓝 0) ∧
          ContinuousOn inv (Ioo 0 ε) ∧ Tendsto inv (𝓝[>] (0 : ℝ)) atTop ∧
          (∀ u ∈ Ioo 0 ε, T + 1 < inv u ∧ g (inv u) = u ∧ HasDerivAt inv (deriv g (inv u))⁻¹ u) ∧
          (∀ t ∈ Ioi (T + 1), inv (g t) = t) ∧
          ∀ t ∈ Ioi T, 0 < g t ∧ j ≤ g t * Real.exp (B.outerRate * t) ∧
            g t * Real.exp (B.outerRate * t) ≤ J ∧ b ≤ -deriv g t / g t ∧ -deriv g t / g t ≤ C ∧
            ∃ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
              (hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x) (u : Icc 0 U) (v : Icc 0 V),
              (u : ℝ) = g t ∧ (v : ℝ) = t ∧ (u : ℝ) ∈ Ioo 0 U ∧ (v : ℝ) ∈ Ioo 0 V ∧
                x.1 u v 0 = Y ∧ U * Real.exp (B.outerRate * V) = δ ∧
                let ν := radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                HasDerivAt g (-x.2.1 u v 0 / ν u v) t ∧
                  (-ν u v) * (-deriv g t) = -x.2.1 u v 0 := by
  obtain ⟨δ, Y, T, j, J, b, C, ε, hδ, _hcap, hδr, hY, hrest⟩ :=
    B.exists_outer_arrival_le hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
      1 zero_lt_one
  exact ⟨δ, Y, T, j, J, b, C, ε, hδ, hδr, hY, hrest⟩

end CauchyHorizon.Background
