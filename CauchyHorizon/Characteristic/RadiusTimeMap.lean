import CauchyHorizon.Analysis.ArrivalTimeMap
import CauchyHorizon.Characteristic.ArrivalPhase

/-! The actual time map from an outer radius to an inner comparison radius. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_radius_time_map (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Z ≤ R →
        ∃ T : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ, 0 < T ∧ (∀ ε, T ≤ τ ε) ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ),
            MemLp f p (volume.restrict (Icc 0 δ)) →
            (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∃ gY gZ ψ : ℝ → ℝ, ContinuousOn ψ (Ici T) ∧
              (∀ t ∈ Ici T, t < ψ t ∧ 0 < gZ t ∧ gY (ψ t) = gZ t ∧
                DifferentiableAt ℝ ψ t ∧
                |ψ t - t| ≤ (|Real.log (B.z Y) - Real.log (B.z Z)| + 2) / B.outerRate ∧
                gZ t * Real.exp (B.outerRate * t) ≤ Real.exp 1 * B.z Z / cν) ∧
              (∀ (ε : Ioi (0 : ℝ)) (t : ℝ), τ ε ≤ t →
                |ψ t - t - (Real.log (B.z Y) - Real.log (B.z Z)) / B.outerRate| +
                  |deriv ψ t - 1| < ε) ∧
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
                (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x),
                ∀ t ∈ Ici T, gZ t ≤ U → ψ t ≤ V →
                  let u := projIcc 0 U hU (gZ t)
                  let v₀ := projIcc 0 V hV t
                  let v₁ := projIcc 0 V hV (ψ t)
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                  x.1 u v₀ 0 = Z ∧ x.1 u v₁ 0 = Y ∧
                    HasDerivAt ψ ((x.2.1 u v₀ 0 / ((u : ℝ) * ν u v₀)) /
                      (x.2.1 u v₁ 0 / ((u : ℝ) * ν u v₁))) t ∧
                    Real.exp (-1) * (-B.F Y) / B.outerRate ≤ (u : ℝ) * (-ν u v₁) ∧
                    (u : ℝ) * (-ν u v₁) ≤ Real.exp 1 * (-B.F Y) / B.outerRate ∧
                    0 < -x.2.1 u v₁ 0 ∧ -x.2.1 u v₁ 0 ≤ 2 * Real.exp 1 * (-B.F Y) := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  let a := B.outerRate
  let cν := Real.exp (∫ t in Ioi 0,
    2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - a)
  have ha : 0 < a := B.outerRate_pos
  have hcν : 0 < cν := Real.exp_pos _
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, hδr, hR, _hRr, hnorm⟩ := B.exists_arrival_phase_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hδr, hR, ?_⟩
  intro Y Z hY hYZ hZR
  have hYb : Y ∈ Ioo B.inner B.event := ⟨hY, hYZ.trans_le hZR |>.trans hR.2⟩
  have hZb : Z ∈ Ioo B.inner B.event := ⟨hY.trans hYZ, hZR.trans_lt hR.2⟩
  have hzanti : StrictAntiOn B.z (Ioo B.inner B.event) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
      (fun q hq => (B.z_hasDerivAt hq).continuousAt.continuousWithinAt)
    intro q hq
    rw [interior_Ioo] at hq
    rw [(B.z_hasDerivAt hq).deriv]
    exact mul_neg_of_neg_of_pos (div_neg_of_pos_of_neg B.outerRate_pos (B.F_neg hq)) (B.z_pos hq)
  let dY := Real.log (B.z Y) - Real.log cν
  let dZ := Real.log (B.z Z) - Real.log cν
  have hdd : dY - dZ = Real.log (B.z Y) - Real.log (B.z Z) := by dsimp only [dY, dZ]; ring
  let Δ := (dY - dZ) / a
  have hΔ : 0 < Δ := div_pos (by
    rw [hdd]
    exact sub_pos.2 (Real.log_lt_log (B.z_pos hZb) (hzanti hYb hZb hYZ))) ha
  obtain ⟨TY, τY, hTY, hτY, hsolveY⟩ := hnorm Y hY (hYZ.le.trans hZR)
  obtain ⟨TZ, τZ, hTZ, hτZ, hsolveZ⟩ := hnorm Z hZb.1 hZR
  let T₀ := max TY TZ
  let τ₀ := fun ε => max (τY ε) (τZ ε)
  have hτ₀ (ε) : T₀ ≤ τ₀ ε := max_le_max (hτY ε) (hτZ ε)
  obtain ⟨S, σ, hTS, hσ, hmap⟩ := exists_normalized_arrival_time_map (d₁ := dY) (d₂ := dZ) ha τ₀ hτ₀
  let εΔ : Ioi (0 : ℝ) := ⟨Δ / 2, half_pos hΔ⟩
  let εY : Ioi (0 : ℝ) := ⟨min 1 (a / 2), lt_min (by norm_num) (half_pos ha)⟩
  let T := max (σ εΔ) (max (τZ ⟨1, by norm_num⟩) (τY εY))
  have hST : S ≤ T := (hσ εΔ).trans (le_max_left _ _)
  have hT₀ : 0 < T₀ := hTY.trans_le (le_max_left _ _)
  have hT : 0 < T := hT₀.trans_le (hTS.trans hST)
  refine ⟨T, fun ε => max T (σ ε), hT, fun _ => le_max_left _ _, ?_⟩
  intro p hp f hf hfn
  obtain ⟨gY, hYc, hYa, hYl, hYpoint⟩ := hsolveY p hp f hf hfn
  obtain ⟨gZ, hZc, _hZa, _hZl, hZpoint⟩ := hsolveZ p hp f hf hfn
  have hTY₀ : TY ≤ T₀ := le_max_left _ _
  have hTZ₀ : TZ ≤ T₀ := le_max_right _ _
  have hlog (q v u : ℝ) (hq : q ∈ Ioo B.inner B.event) (hu : 0 < u) :
      Real.log (B.z q / (u * (cν * Real.exp (a * v)))) =
        (Real.log (B.z q) - Real.log cν) - Real.log u - a * v := by
    rw [Real.log_div (B.z_pos hq).ne' (mul_pos hu (mul_pos hcν (Real.exp_pos _))).ne',
      Real.log_mul hu.ne' (mul_pos hcν (Real.exp_pos _)).ne',
      Real.log_mul hcν.ne' (Real.exp_ne_zero _)]
    simp only [Real.log_exp]
    ring
  obtain ⟨ψ, hψc, hψpoint, hψerror⟩ := hmap gY gZ
    (hYc.mono (fun _ ht => hTY₀.trans ht)) (hYa.mono (fun _ ht => hTY₀.trans ht)) hYl
    (hZc.mono (fun _ ht => hTZ₀.trans ht))
    (fun t ht => ⟨(hYpoint t (hTY₀.trans ht)).1.1, (hYpoint t (hTY₀.trans ht)).2.1,
      (hZpoint t (hTZ₀.trans ht)).1.1, (hZpoint t (hTZ₀.trans ht)).2.1⟩) (by
      intro ε t ht
      have htY := (le_max_left _ _).trans ht
      have htZ := (le_max_right _ _).trans ht
      have hy := (hYpoint t ((hτY ε).trans htY)).2.2.2.1 ε htY
      have hz := (hZpoint t ((hτZ ε).trans htZ)).2.2.2.1 ε htZ
      rw [hlog Y t (gY t) hYb (hYpoint t ((hτY ε).trans htY)).1.1] at hy
      rw [hlog Z t (gZ t) hZb (hZpoint t ((hτZ ε).trans htZ)).1.1] at hz
      exact ⟨hy, hz⟩)
  have hfuture (t : ℝ) (ht : T ≤ t) : t < ψ t := by
    have hh := hψerror εΔ t ((le_max_left _ _).trans ht)
    have hlo := (abs_lt.1 ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt hh)).1
    change -(Δ / 2) < ψ t - t - Δ at hlo
    linarith only [hlo, hΔ]
  refine ⟨gY, gZ, ψ, hψc.mono (fun _ ht => hST.trans ht), ?_, ?_, ?_⟩
  · intro t ht
    have hh := hψpoint t (hST.trans ht)
    refine ⟨hfuture t ht, (hZpoint t (hTZ₀.trans (hTS.trans (hST.trans ht)))).1.1,
      hh.2.1, hh.2.2.1.differentiableAt, ?_, ?_⟩
    · simpa only [hdd] using hh.2.2.2
    · have htZ : τZ ⟨1, by norm_num⟩ ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
      have hz := hZpoint t ((hτZ _).trans htZ)
      have herr := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt (hz.2.2.2.1 ⟨1, by norm_num⟩ htZ)
      rw [hlog Z t (gZ t) hZb hz.1.1] at herr
      have he := Real.exp_le_exp.2 (show Real.log (gZ t) + a * t ≤ 1 + Real.log (B.z Z) - Real.log cν by
        linarith only [(abs_lt.1 herr).1])
      simpa only [Real.exp_sub, Real.exp_add, Real.exp_log hz.1.1,
        Real.exp_log (B.z_pos hZb), Real.exp_log hcν] using he
  · intro ε t ht
    simpa only [hdd] using hψerror ε t ((le_max_right _ _).trans ht)
  · intro U V hU hV hUR hfU x hx t ht hgu hψV
    have hpt := hψpoint t (hST.trans ht)
    have htY : TY ≤ ψ t := hTY₀.trans hpt.1.le
    have htZ : TZ ≤ t := hTZ₀.trans (hTS.trans (hST.trans ht))
    have htV : t ≤ V := (hfuture t ht).le.trans hψV
    have hy := (hYpoint (ψ t) htY).2.2.2.2 U V hU hV hUR hfU x hx
      (by rw [hpt.2.1]; exact hgu) hψV
    have hz := (hZpoint t htZ).2.2.2.2 U V hU hV hUR hfU x hx hgu htV
    rw [hpt.2.1] at hy
    have htol : τY εY ≤ ψ t :=
      (((le_max_right _ _).trans (le_max_right _ _)).trans ht).trans (hfuture t ht).le
    have hlog := hy.2.2 εY htol
    have hspeed := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt
      ((hYpoint (ψ t) htY).2.2.2.1 εY htol)
    rw [hpt.2.1] at hspeed
    have hu : gZ t ∈ Icc 0 U := ⟨(hZpoint t htZ).1.1.le, hgu⟩
    have hv₀ : t ∈ Icc 0 V := ⟨hT.le.trans ht, htV⟩
    have hv₁ : ψ t ∈ Icc 0 V := ⟨hTY.le.trans htY, hψV⟩
    simp only [projIcc_of_mem hU hu, projIcc_of_mem hV hv₀, projIcc_of_mem hV hv₁] at hy hz hlog ⊢
    let u : Icc 0 U := ⟨gZ t, hu⟩
    let v : Icc 0 V := ⟨ψ t, hv₁⟩
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
    let N := gZ t * (-ν u v)
    let Q := a * N / (-B.F Y)
    let speed := -deriv gY (ψ t) / gZ t
    have hn : ν u v < 0 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU u v).2.2.1
    have hgpos : 0 < gZ t := (hZpoint t htZ).1.1
    have hN : 0 < N := mul_pos hgpos (neg_pos.2 hn)
    have hF : 0 < -B.F Y := neg_pos.2 (B.F_neg hYb)
    have hQ : 0 < Q := div_pos (mul_pos ha hN) hF
    have hQeq : a * (gZ t * ν u v / B.F Y) = Q := by dsimp only [Q, N]; ring
    change |Real.log (a * (gZ t * ν u v / B.F Y))| < (εY : ℝ) at hlog
    rw [hQeq] at hlog
    have hlog1 : |Real.log Q| ≤ 1 := hlog.le.trans (min_le_left _ _)
    have hQl : Real.exp (-1) ≤ Q := by
      rw [← Real.exp_log hQ]
      exact Real.exp_le_exp.2 (abs_le.1 hlog1).1
    have hQh : Q ≤ Real.exp 1 := by
      rw [← Real.exp_log hQ]
      exact Real.exp_le_exp.2 (abs_le.1 hlog1).2
    have hNl : Real.exp (-1) * (-B.F Y) / a ≤ N := by
      apply (div_le_iff₀ ha).2
      simpa only [mul_comm a N] using (le_div_iff₀ hF).1 hQl
    have hNh : N ≤ Real.exp 1 * (-B.F Y) / a := by
      apply (le_div_iff₀ ha).2
      simpa only [mul_comm a N] using (div_le_iff₀ hF).1 hQh
    have hsp : 0 < speed ∧ speed ≤ 2 * a := by
      have herr : |speed - a| ≤ a / 2 := hspeed.le.trans (min_le_right _ _)
      constructor <;> linarith only [(abs_le.1 herr).1, (abs_le.1 herr).2, ha]
    have heq : -x.2.1 u v 0 = speed * N := by
      dsimp only [speed, N]
      rw [hy.2.1.deriv]
      change -x.2.1 u v 0 = (-(-x.2.1 u v 0 / ν u v) / gZ t) * (gZ t * (-ν u v))
      field_simp [hgpos.ne', hn.ne]
    refine ⟨hz.1, hy.1, ?_, hNl, hNh, ?_, ?_⟩
    · have hd := hpt.2.2.1
      rw [hz.2.1.deriv, hy.2.1.deriv, hpt.2.1] at hd
      apply hd.congr_deriv
      simp only [neg_div, neg_neg, div_div]
      congr 1
      congr 1 <;> ring
    · exact heq ▸ mul_pos hsp.1 hN
    · rw [heq]
      calc
        _ ≤ (2 * a) * (Real.exp 1 * (-B.F Y) / a) :=
          mul_le_mul hsp.2 hNh hN.le (by positivity)
        _ = _ := by field_simp [ha.ne']

end CauchyHorizon.Background
