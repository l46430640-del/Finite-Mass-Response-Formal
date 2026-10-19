import CauchyHorizon.Characteristic.BandCharts
import CauchyHorizon.Characteristic.TrappedLevel
import CauchyHorizon.Characteristic.MatchingFeedback
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Hom.Set

/-! The actual radius arrival time obtained by identifying the local physical charts. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_band_arrival (B : Background) {s H dH A c : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧ R < r 0 ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ ε j D b C K n N L E τ σ Cerr : ℝ,
        0 < ε ∧ ε ≤ δ ∧ 0 < j ∧ 0 < D ∧ 0 < b ∧ 0 ≤ C ∧ 0 < K ∧
        0 < n ∧ 0 < N ∧ 0 ≤ L ∧ 0 ≤ E ∧ 0 < τ ∧
        0 < σ ∧ σ < ε / 2 ∧ 0 ≤ Cerr ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A → c ≤ B.outerRate * (1 - 1 / p.toReal) →
          ∃ arrival g : ℝ → ℝ, ContinuousOn arrival (Ioo 0 ε) ∧ StrictAntiOn arrival (Ioo 0 ε) ∧
            Tendsto arrival (𝓝[>] (0 : ℝ)) atTop ∧
            arrival (ε / 2) < K ∧ arrival σ < K ∧
            ContinuousOn g (Ioi (arrival (ε / 2))) ∧ StrictAntiOn g (Ioi (arrival (ε / 2))) ∧
            Tendsto g atTop (𝓝 0) ∧
            (∀ t ∈ Ioi (arrival (ε / 2)), g t ∈ Ioo 0 (ε / 2) ∧ arrival (g t) = t ∧
              HasStrictDerivAt g (deriv arrival (g t))⁻¹ t ∧
              j ≤ g t * Real.exp (B.outerRate * t) ∧ g t * Real.exp (B.outerRate * t) ≤ D ∧
              b ≤ -deriv g t / g t ∧ -deriv g t / g t ≤ C) ∧
            (∀ U ∈ Ioo 0 (ε / 2), g (arrival U) = U) ∧
            ∀ (U : ℝ) (hU : U ∈ Ioo 0 ε), ∃ hT : 0 < arrival U,
              j ≤ U * Real.exp (B.outerRate * arrival U) ∧
              U * Real.exp (B.outerRate * arrival U) ≤ D ∧
              b ≤ -(deriv arrival U)⁻¹ / U ∧ -(deriv arrival U)⁻¹ / U ≤ C ∧
              ∃ W V : ℝ, ∃ hW : 0 ≤ W, ∃ hV : 0 ≤ V, ∃ hWR : W < r 0,
              ∃ hfW : MemLp f p (volume.restrict (Icc 0 W)), ∃ z : WaveState W V,
              ∃ hz : IsWaveIntegral hW hV B.charge B.cosmological
                (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hWR hp hfW) z,
              ∃ hUW : U < W, ∃ hTV : arrival U < V,
              let u : Icc 0 W := ⟨U, hU.1.le, hUW.le⟩
              let v : Icc 0 V := ⟨arrival U, hT.le, hTV.le⟩
              let ν := radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose
              W ≤ ε ∧ (∀ u v, Y / 2 ≤ z.1 u v 0) ∧ z.1 u v 0 = Y ∧ z.2.1 u v 0 < 0 ∧
              n * j ≤ U * (-ν u v) ∧ U * (-ν u v) ≤ N * D ∧
              τ ≤ -z.2.1 u v 0 ∧ |z.2.1 u v 0| ≤ L ∧
              (3 / 4 : ℝ) ≤ -Real.exp (z.1 u v 2) / (4 * ν u v) ∧ |z.2.1 u v 1| ≤ E * Real.exp (-c * arrival U) ∧
              (∀ w ≤ u, ∀ t ≤ v, Y ≤ z.1 w t 0 ∧ |ν w t| ≤ N * Real.exp (B.outerRate * t) ∧
                |z.2.1 w t 1| ≤ E * Real.exp (-c * t)) ∧
              HasStrictDerivAt arrival (-ν u v / z.2.1 u v 0) U ∧
              (-ν u v) * (-(deriv arrival U)⁻¹) = -z.2.1 u v 0 ∧
              (U < ε / 2 → HasStrictDerivAt g (-z.2.1 u v 0 / ν u v) (arrival U) ∧
                (-ν u v) * (-deriv g (arrival U)) = -z.2.1 u v 0) ∧
              (U ≤ σ → |(-Real.exp (z.1 u v 2) / (4 * ν u v)) - 1| +
                |massField B.charge B.cosmological z.1 z.2.1 ν hz.choose u v - B.mass| ≤
                  Cerr * Real.exp (-(min B.outerRate (2 * c)) * arrival U)) := by
  classical
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, hδr, hR, hRr, hcharts⟩ :=
    B.exists_band_charts hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, hRr, ?_⟩
  intro Y hY hYR
  obtain ⟨ε, j, D, n, N, L, E, τ, hε, hεδ, hj, hD, hn, hN, hL, hE, hτ, hsolve⟩ := hcharts Y hY hYR
  have hY0 := B.inner_pos.trans hY
  have hYR' : Y / 2 ≤ B.event + dH := by linarith only [hY0, hYR, hR.2, hdH]
  obtain ⟨U₁, Cerr, hU₁, _hU₁r, hCerr, hfeedback⟩ := B.exists_bounded_width_feedback_decay
    hs hH hdH hdHR hA (half_pos hY0) hYR' hD.le hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  let σ := min (ε / 4) U₁
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hσε : σ < ε / 2 := (min_le_left _ _).trans_lt (by linarith only [hε])
  have hσmem : σ ∈ Ioo 0 ε := ⟨hσ, hσε.trans (half_lt_self hε)⟩
  let K := max 0 (Real.log (D / σ) / B.outerRate) + 1
  have hK : 0 < K := by dsimp only [K]; linarith only [le_max_left 0 (Real.log (D / σ) / B.outerRate)]
  refine ⟨ε, j, D, τ / (N * D), L / (n * j), K, n, N, L, E, τ, σ, Cerr,
    hε, hεδ, hj, hD, div_pos hτ (mul_pos hN hD), div_nonneg hL (mul_pos hn hj).le,
    hK, hn, hN, hL, hE, hτ, hσ, hσε, hCerr, ?_⟩
  intro p hp f hf hfn hcb
  choose T hT hjT hDT W V hW hV hWR hfW X hx hUW hTV hg using
    fun u : Ioo 0 ε => hsolve p hp f hf hfn hcb u u.property.1 u.property.2
  let uu (u : Ioo 0 ε) : Icc 0 (W u) := ⟨u, u.property.1.le, (hUW u).le⟩
  let vv (u : Ioo 0 ε) : Icc 0 (V u) := ⟨T u, (hT u).le, (hTV u).le⟩
  let ν (u : Ioo 0 ε) := radialNuField (hV u) B.charge B.cosmological
    (incomingWaveCurve (hW u) (hWR u) hp (hfW u) (horizonPhi h r 0)) (X u).1 (hx u).choose
  choose hWε hfloor hhit hnlo hnhi hlam hLabs hk hscalar hpre ψ hψ hdψ hjac hlow hhigh hgraph using hg
  have hlneg (u : Ioo 0 ε) : (X u).2.1 (uu u) (vv u) 0 < 0 := by
    have hh := hτ.trans_le (hlam u)
    linarith only [hh]
  have hνneg (u : Ioo 0 ε) : ν u (uu u) (vv u) < 0 :=
    ((hx u).interior_gauge (hW u) (hV u) (hWR u) hc hi hrc hr0 hφ hrd hp (hfW u) (uu u) (vv u)).2.2.1
  let arrival := fun u : ℝ => if hu : u ∈ Ioo 0 ε then T ⟨u, hu⟩ else 0
  have haval (u : Ioo 0 ε) : arrival u = T u := by
    dsimp only [arrival]
    rw [dif_pos u.property]
  have hder (u : Ioo 0 ε) : HasStrictDerivAt arrival
      (-(X u).2.1 (uu u) (vv u) 0 / ν u (uu u) (vv u))⁻¹ u := by
    have hψcont := (hdψ u).hasDerivAt.continuousAt
    have hwindow : ∀ᶠ t in 𝓝 (T u), ψ u t ∈ Ioo 0 ε := by
      apply hψcont.tendsto
      rw [hψ u]
      exact Ioo_mem_nhds u.property.1 u.property.2
    let vel : ℝ → ℝ := fun t => intervalExtension (hV u) (intervalExtension (hW u) (X u).2.1 (ψ u t)) t 0
    have hcvel : ContinuousAt vel (T u) := by dsimp only [vel]; fun_prop
    have hvneg : vel (T u) < 0 := by
      simpa only [vel, hψ u, intervalExtension_apply,
        projIcc_of_mem (hW u) (show (u : ℝ) ∈ Icc 0 (W u) from (uu u).property),
        projIcc_of_mem (hV u) (show T u ∈ Icc 0 (V u) from (vv u).property)] using hlneg u
    have hvnear := hcvel.eventually (Iio_mem_nhds hvneg)
    have hleft : ∀ᶠ t in 𝓝 (T u), arrival (ψ u t) = t := by
      filter_upwards [hwindow, hgraph u, hvnear] with t ht hgt hlt
      let w : Ioo 0 ε := ⟨ψ u t, ht⟩
      have huw : ψ u t ∈ Icc 0 (W u) := ⟨hgt.1.1.le, hgt.1.2.le⟩
      have hvt : t ∈ Icc 0 (V u) := ⟨hgt.2.1.1.le, hgt.2.1.2.le⟩
      have hrt : (X u).1 ⟨ψ u t, huw⟩ ⟨t, hvt⟩ 0 = Y := by
        simpa only [intervalExtension_apply, projIcc_of_mem (hW u) huw, projIcc_of_mem (hV u) hvt] using hgt.2.2
      have hlt' : (X u).2.1 ⟨ψ u t, huw⟩ ⟨t, hvt⟩ 0 < 0 := by
        simpa only [vel, intervalExtension_apply, projIcc_of_mem (hW u) huw, projIcc_of_mem (hV u) hvt] using hlt
      have he := (hx w).trapped_level_time_unique (hW w) (hV w) (hWR w) (hW u) (hV u) (hWR u)
        hc hi hrc hr0 hφ hrd hp (hfW w) (hfW u) (hx u) (uu w).property huw (vv w).property hvt
        (hhit w) hrt (hlneg w) hlt'
      exact (haval w).trans he
    have hdn : -(X u).2.1 (uu u) (vv u) 0 / ν u (uu u) (vv u) ≠ 0 :=
      div_ne_zero (neg_ne_zero.2 (hlneg u).ne) (hνneg u).ne
    simpa only [hψ u] using (hdψ u).to_local_left_inverse hdn hleft
  have hderinv (u : Ioo 0 ε) : (deriv arrival u)⁻¹ = deriv (ψ u) (T u) := by
    rw [(hder u).hasDerivAt.deriv, inv_inv, (hdψ u).hasDerivAt.deriv]
  have hcont : ContinuousOn arrival (Ioo 0 ε) := fun u hu => (hder ⟨u, hu⟩).hasDerivAt.continuousAt.continuousWithinAt
  have hderneg (u : Ioo 0 ε) : deriv arrival u < 0 := by
    rw [(hder u).hasDerivAt.deriv]
    exact inv_neg''.2 (div_neg_of_pos_of_neg (neg_pos.2 (hlneg u)) (hνneg u))
  have hanti : StrictAntiOn arrival (Ioo 0 ε) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) hcont
    intro u hu
    rw [interior_Ioo] at hu
    exact hderneg ⟨u, hu⟩
  have hlim : Tendsto arrival (𝓝[>] (0 : ℝ)) atTop := by
    apply tendsto_atTop.2
    intro K
    have hsmall : ∀ᶠ u in 𝓝[>] (0 : ℝ), u < min ε (j * Real.exp (-B.outerRate * K)) :=
      (eventually_lt_nhds (lt_min hε (mul_pos hj (Real.exp_pos _)))).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with u hu hus
    have hum : u ∈ Ioo 0 ε := ⟨hu, (lt_min_iff.1 hus).1⟩
    by_contra hnot
    have he := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (not_le.1 hnot).le B.outerRate_pos.le)
    have hscale : j ≤ u * Real.exp (B.outerRate * arrival u) := by rw [haval ⟨u, hum⟩]; exact hjT ⟨u, hum⟩
    have hh := mul_lt_mul_of_pos_right (lt_min_iff.1 hus).2 (Real.exp_pos (B.outerRate * K))
    have hex : Real.exp (-B.outerRate * K) * Real.exp (B.outerRate * K) = 1 := by
      rw [← Real.exp_add, show -B.outerRate * K + B.outerRate * K = 0 by ring, Real.exp_zero]
    rw [mul_assoc, hex, mul_one] at hh
    exact (not_lt_of_ge (hscale.trans (mul_le_mul_of_nonneg_left he hu.le))) hh
  let e₀ := ε / 2
  have he₀ : e₀ ∈ Ioo 0 ε := ⟨half_pos hε, half_lt_self hε⟩
  have htimeσ : arrival σ < K := by
    have hh := hDT ⟨σ, hσmem⟩
    rw [← haval ⟨σ, hσmem⟩] at hh
    have he : Real.exp (B.outerRate * arrival σ) ≤ D / σ :=
      (le_div_iff₀ hσ).2 (by simpa only [mul_comm] using hh)
    have hlog := (Real.le_log_iff_exp_le (div_pos hD hσ)).2 he
    have har : arrival σ ≤ Real.log (D / σ) / B.outerRate :=
      (le_div_iff₀ B.outerRate_pos).2 (by simpa only [mul_comm] using hlog)
    dsimp only [K]
    linarith only [har, le_max_right 0 (Real.log (D / σ) / B.outerRate)]
  have htime : arrival e₀ < K := (hanti hσmem he₀ hσε).trans htimeσ
  have hsub : Ioo 0 e₀ ⊆ Ioo 0 ε := Ioo_subset_Ioo le_rfl he₀.2.le
  let F : (Ioo 0 e₀)ᵒᵈ → Ioi (arrival e₀) := fun u =>
    ⟨arrival u.val, hanti (hsub u.property) he₀ u.property.2⟩
  have hmono : StrictMono F := fun u w huw => hanti (hsub w.property) (hsub u.property) huw
  have hsurj : Function.Surjective F := by
    intro t
    have hnear : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 e₀ :=
      (show ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u from self_mem_nhdsWithin).and
        ((eventually_lt_nhds he₀.1).filter_mono nhdsWithin_le_nhds)
    obtain ⟨l, hl, hlt⟩ := (hnear.and (hlim.eventually (eventually_gt_atTop (t : ℝ)))).exists
    have hcseg := hcont.mono (show Icc l e₀ ⊆ Ioo 0 ε from
      fun _ hu => ⟨hl.1.trans_le hu.1, hu.2.trans_lt he₀.2⟩)
    obtain ⟨u, hu, he⟩ := intermediate_value_Icc' hl.2.le hcseg
      (show (t : ℝ) ∈ Icc (arrival e₀) (arrival l) from ⟨t.property.le, hlt.le⟩)
    have hue : u < e₀ := by
      apply lt_of_le_of_ne hu.2
      intro heq
      rw [heq] at he
      exact (ne_of_lt t.property) he
    exact ⟨⟨u, hl.1.trans_le hu.1, hue⟩, Subtype.ext he⟩
  let iso : (Ioo 0 e₀)ᵒᵈ ≃o Ioi (arrival e₀) := hmono.orderIsoOfSurjective F hsurj
  let g := fun t : ℝ => if ht : arrival e₀ < t then (iso.symm ⟨t, ht⟩).val else e₀
  have hgval (t : Ioi (arrival e₀)) : g t = (iso.symm t).val := by
    dsimp only [g]
    rw [dif_pos (show arrival e₀ < (t : ℝ) from t.property)]
  have hgmem (t : ℝ) (ht : arrival e₀ < t) : g t ∈ Ioo 0 e₀ := by
    rw [hgval ⟨t, ht⟩]
    exact (iso.symm ⟨t, ht⟩).property
  have hright (t : ℝ) (ht : arrival e₀ < t) : arrival (g t) = t := by
    rw [hgval ⟨t, ht⟩]
    exact congrArg Subtype.val (iso.apply_symm_apply ⟨t, ht⟩)
  have hleft (u : ℝ) (hu : u ∈ Ioo 0 e₀) : g (arrival u) = u :=
    hanti.injOn (hsub (hgmem _ (hanti (hsub hu) he₀ hu.2))) (hsub hu)
      (hright _ (hanti (hsub hu) he₀ hu.2))
  have hgc : ContinuousOn g (Ioi (arrival e₀)) := continuousOn_iff_continuous_domRestrict.2
    ((continuous_subtype_val.comp iso.symm.continuous).congr (fun t => (hgval t).symm))
  have hga : StrictAntiOn g (Ioi (arrival e₀)) := by
    intro t ht w hw htw
    rw [hgval ⟨w, hw⟩, hgval ⟨t, ht⟩]
    exact iso.symm.strictMono htw
  have hgd (t : ℝ) (ht : arrival e₀ < t) : HasStrictDerivAt g (deriv arrival (g t))⁻¹ t := by
    let u : Ioo 0 ε := ⟨g t, hsub (hgmem t ht)⟩
    have hd : HasStrictDerivAt arrival (deriv arrival (g t)) (g t) := by
      rw [(hder u).hasDerivAt.deriv]
      exact hder u
    have hloc : ∀ᶠ w in 𝓝 (g t), g (arrival w) = w := by
      filter_upwards [isOpen_Ioo.mem_nhds (hgmem t ht)] with w hw
      exact hleft w hw
    simpa only [hright t ht] using hd.to_local_left_inverse (hderneg u).ne hloc
  have hgb (t : ℝ) (ht : arrival e₀ < t) :
      j ≤ g t * Real.exp (B.outerRate * t) ∧ g t * Real.exp (B.outerRate * t) ≤ D ∧
      τ / (N * D) ≤ -deriv g t / g t ∧ -deriv g t / g t ≤ L / (n * j) := by
    let u : Ioo 0 ε := ⟨g t, hsub (hgmem t ht)⟩
    have htT : T u = t := (haval u).symm.trans (hright t ht)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hh := hjT u
      change j ≤ g t * Real.exp (B.outerRate * T u) at hh
      simpa only [htT] using hh
    · have hh := hDT u
      change g t * Real.exp (B.outerRate * T u) ≤ D at hh
      simpa only [htT] using hh
    · rw [(hgd t ht).hasDerivAt.deriv, hderinv u]; exact hlow u
    · rw [(hgd t ht).hasDerivAt.deriv, hderinv u]; exact hhigh u
  have hglim : Tendsto g atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => D * Real.exp (-B.outerRate * t)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos B.outerRate_pos))).const_mul D
    apply squeeze_zero' _ _ he
    · filter_upwards [eventually_gt_atTop (arrival e₀)] with t ht
      exact (hgmem t ht).1.le
    · filter_upwards [eventually_gt_atTop (arrival e₀)] with t ht
      have hh := mul_le_mul_of_nonneg_right (hgb t ht).2.1 (Real.exp_pos (-B.outerRate * t)).le
      have hex : Real.exp (B.outerRate * t) * Real.exp (-B.outerRate * t) = 1 := by
        rw [← Real.exp_add, show B.outerRate * t + -B.outerRate * t = 0 by ring, Real.exp_zero]
      simpa only [mul_assoc, hex, mul_one] using hh
  refine ⟨arrival, g, hcont, hanti, hlim, htime, htimeσ, hgc, hga, hglim,
    fun t ht => ⟨hgmem t ht, hright t ht, hgd t ht, hgb t ht⟩, hleft, ?_⟩
  intro U hU
  let u : Ioo 0 ε := ⟨U, hU⟩
  have hvU : 0 < arrival U := by rw [haval u]; exact hT u
  refine ⟨hvU, by rw [haval u]; exact hjT u, by rw [haval u]; exact hDT u,
    ?_, ?_, W u, V u, hW u, hV u, hWR u, hfW u, X u, hx u, hUW u, ?_, ?_⟩
  · rw [hderinv u]; exact hlow u
  · rw [hderinv u]; exact hhigh u
  · rw [haval u]; exact hTV u
  · have havU : arrival U = T u := haval u
    simp only [havU]
    refine ⟨hWε u, hfloor u, hhit u, hlneg u, hnlo u, hnhi u, hlam u, hLabs u, hk u, hscalar u, hpre u, ?_, ?_, ?_, ?_⟩
    · change HasStrictDerivAt arrival (-ν u (uu u) (vv u) / (X u).2.1 (uu u) (vv u) 0) U
      simpa only [inv_div, inv_neg, div_neg, neg_div] using hder u
    · rw [hderinv u]
      exact hjac u
    · intro hUe
      have htu : arrival e₀ < T u := by
        rw [← havU]
        exact hanti hU he₀ hUe
      have hgu : g (T u) = U := by rw [← havU]; exact hleft U ⟨hU.1, hUe⟩
      have hd := hgd (T u) htu
      rw [hgu, hderinv u, (hdψ u).hasDerivAt.deriv] at hd
      refine ⟨hd, ?_⟩
      rw [hd.hasDerivAt.deriv.trans (hdψ u).hasDerivAt.deriv.symm]
      exact hjac u
    · intro hUσ
      have hUR : U < r 0 := (hUW u).trans (hWR u)
      let hfU := (hfW u).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (hUW u).le) le_rfl)
      let z := waveTranslate (a := 0) (U := U) (b := 0) (V := T u)
        le_rfl (by simpa using (hUW u).le) le_rfl (by simpa using (hTV u).le) (X u)
      have hz : IsWaveIntegral hU.1.le (hT u).le B.charge B.cosmological
          (incomingWaveCurve hU.1.le hUR hp hfU (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological (T u) hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hfU) z :=
        (hx u).horizon_prefix (hW u) (hV u) (hWR u) hU.1.le (hT u).le (hUW u).le (hTV u).le hc hi hrc hr0 hp (hfW u)
      have hfUnorm := (scalar_prefix_norm_le (hU.2.le.trans hεδ) hf).trans hfn
      have hfl : ∀ a b, Y / 2 ≤ z.1 a b 0 := fun a b => hfloor u _ _
      let a : Icc 0 U := ⟨U, hU.1.le, le_rfl⟩
      let t : Icc 0 (T u) := ⟨T u, (hT u).le, le_rfl⟩
      have hh := hfeedback U (T u) hU.1.le (hT u).le hUR p hp f hfU z hz hfUnorm hcb
        (hUσ.trans (min_le_right _ _)) hfl (hDT u) a
      have he := hz.horizon_overlap hU.1.le (hT u).le hUR (hW u) (hV u) (hWR u) hc hi hrc hr0 hp hfU (hfW u)
        (hx u) a.property (uu u).property t.property (vv u).property
      have hne := hz.horizon_overlap_nu hU.1.le (hT u).le hUR (hW u) (hV u) (hWR u) hc hi hrc hr0 hp hfU (hfW u)
        (hx u) a.property (uu u).property t.property (vv u).property
      simp only [massField_apply] at hh ⊢
      rw [he.1, he.2, hne] at hh
      exact hh

end CauchyHorizon.Background
