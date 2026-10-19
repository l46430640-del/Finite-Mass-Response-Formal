import CauchyHorizon.Characteristic.LateRadiation
import CauchyHorizon.Characteristic.GammaChart
import CauchyHorizon.Reduced.ScalarRegularity
import CauchyHorizon.Analysis.LateSources

/-! Full gamma radiation supplies the free source on the same physical late chart. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem IsWaveIntegral.exists_late_gamma_source
    {U V R e Λ φ₀ a k β j C L N T η Y ρ : ℝ}
    (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U))) (hfc : ContinuousOn f (Ioi 0))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU.le hV e Λ (incomingWaveCurve hU.le hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (ha : 0 < a) (hk : 0 < k) (hβ : 0 ≤ β) (hβ8 : β < 1 / 8)
    (hj : 0 < j) (hC : 0 < C) (hL : 0 ≤ L) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (g : ℝ → ℝ) (hgc : ContinuousOn g (Ici T)) (hga : AntitoneOn g (Ici T))
    (hgp : ∀ t ∈ Ici T, 0 < g t) (hscale : ∀ t ∈ Ici T, j ≤ g t * Real.exp (a * t))
    (hchart : RadiationGammaCharts hU.le hV x g T (1 + β) η C Y) :
    let α := 1 + β
    let ξ := k * β / α
    let χ := 3 * ξ
    let Cf := L * C / α * j ^ (-(2 * k / a))
    let Df := L * N * C / α * j ^ (-(2 * k / a - k / a * β))
    let ν := radialNuField hV e Λ (incomingWaveCurve hU.le hUR hp hf φ₀) x.1 hx.choose
    ∃ A : C(Icc 0 V, ℝ), (∀ v, 0 ≤ A v) ∧
      (∀ v : Icc 0 V, T ≤ (v : ℝ) / α → g ((v : ℝ) / α) ≤ U →
        A v = |g ((v : ℝ) / α) * Real.exp (k * ((v : ℝ) / α)) *
          (x.1 (projIcc 0 U hU.le (g ((v : ℝ) / α))) v 0 *
            derivWithin (fun u => intervalExtension hU.le x.1 u v 1)
              (Icc 0 U) (g ((v : ℝ) / α)))|) ∧
      ∀ (M : C(Icc 0 V, ℝ)), (∀ v, 0 ≤ M v) →
      ∀ (u : Icc 0 U) (b : Icc 0 V), T < (b : ℝ) / α → g ((b : ℝ) / α) ≤ u →
        (∀ t ∈ Icc (g ((b : ℝ) / α)) u,
          |x.2.1 (projIcc 0 U hU.le t) b 0| ≤
            L * t ^ (-(2 * k / a)) * Real.exp (-(2 * k) * b)) →
        (∀ t ∈ Icc (g ((b : ℝ) / α)) u, ∀ w : Icc 0 V,
          T < (w : ℝ) / α → g ((w : ℝ) / α) ≤ t → w ≤ b →
            ρ ≤ x.1 (projIcc 0 U hU.le t) w 0 ∧
            |ν (projIcc 0 U hU.le t) w| ≤ N * t ^ (k / a * β - 1) ∧
            Real.exp (k * w) *
              |x.1 (projIcc 0 U hU.le t) w 0 * x.2.1 (projIcc 0 U hU.le t) w 1| ≤ M w) →
        ∃ s : Icc 0 V, T < (s : ℝ) / α ∧ g ((s : ℝ) / α) = u ∧ s ≤ b ∧
          (Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1 -
              x.1 (projIcc 0 U hU.le (g ((b : ℝ) / α))) b 0 *
                x.2.1 (projIcc 0 U hU.le (g ((b : ℝ) / α))) b 1| ≤
            Cf / ρ * (∫ t in (s : ℝ)..b,
              Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-ξ * t) * A (projIcc 0 V hV t)) +
            Df / (ρ ^ 2 * (2 * k - χ)) * ∫ t in (s : ℝ)..b,
              Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-χ * t) * M (projIcc 0 V hV t)) ∧
          Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1| ≤
            Real.exp (k * b) *
              |x.1 (projIcc 0 U hU.le (g ((b : ℝ) / α))) b 0 *
                x.2.1 (projIcc 0 U hU.le (g ((b : ℝ) / α))) b 1| +
            Cf / ρ * (∫ t in (s : ℝ)..b,
              Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-ξ * t) * A (projIcc 0 V hV t)) +
            Df / (ρ ^ 2 * (2 * k - χ)) * ∫ t in (s : ℝ)..b,
              Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-χ * t) * M (projIcc 0 V hV t) := by
  dsimp only
  have hα : 0 < 1 + β := by linarith only [hβ]
  have hβ2 : β ≤ 2 := by linarith only [hβ8]
  have hgap : 0 < 2 * k - 3 * (k * β / (1 + β)) := by
    have hh : 3 * (k * β) < 2 * k * (1 + β) := by
      nlinarith only [mul_pos hk (show 0 < 2 - β by linarith only [hβ8])]
    have hh' : 3 * (k * β / (1 + β)) < 2 * k := by
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hα).2 hh
    exact sub_pos.2 hh'
  let G : C(Icc 0 V, Icc 0 U) := ⟨fun v =>
    ⟨min U (g (max T ((v : ℝ) / (1 + β)))),
      le_min hU.le (hgp _ (show T ≤ max T ((v : ℝ) / (1 + β)) from le_max_left _ _)).le,
      min_le_left _ _⟩,
    (continuous_const.min (hgc.comp_continuous
      (continuous_const.max (continuous_subtype_val.div_const (1 + β)))
      (fun v => (show T ≤ max T ((v : ℝ) / (1 + β)) from le_max_left _ _)))).subtype_mk _⟩
  have hG0 (v : Icc 0 V) : 0 < (G v : ℝ) :=
    lt_min hU (hgp _ (show T ≤ max T ((v : ℝ) / (1 + β)) from le_max_left _ _))
  have hG (v : Icc 0 V) (ht : T ≤ (v : ℝ) / (1 + β))
      (hu : g ((v : ℝ) / (1 + β)) ≤ U) : (G v : ℝ) = g ((v : ℝ) / (1 + β)) := by
    change min U (g (max T ((v : ℝ) / (1 + β)))) = _
    rw [max_eq_right ht, min_eq_right hu]
  have hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf t 1 = f t := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with t ht
    rw [ht]
    rfl
  obtain ⟨A, hA0, hAval, _hAE, hsource⟩ := hx.exists_curve_radiation_source
    (k := k / (1 + β)) rfl (incomingWave_constraint_data hU.le hUR hp hf φ₀).1 hfc hif G hG0
  refine ⟨A, hA0, ?_, ?_⟩
  · intro v ht hu
    have he : G v = projIcc 0 U hU.le (g ((v : ℝ) / (1 + β))) := by
      apply Subtype.ext
      rw [projIcc_of_mem hU.le ⟨(hgp _ ht).le, hu⟩]
      exact hG v ht hu
    rw [hAval]
    dsimp only
    rw [he]
    simp only [projIcc_of_mem hU.le ⟨(hgp _ ht).le, hu⟩,
      show k / (1 + β) * (v : ℝ) = k * ((v : ℝ) / (1 + β)) by ring]
  intro M hM0 u b hb hgu hlam hhistory
  obtain ⟨z, hzu, Q, J, hz, hz0, hQz, hder, hpoint⟩ := hchart u b hb hgu
  let τ := fun t => Q (projIcc (z : ℝ) u hzu t)
  let jac := fun t => J (projIcc (z : ℝ) u hzu t)
  have hrow (t : ℝ) (ht : t ∈ Icc (z : ℝ) u) : t ∈ Icc (g ((b : ℝ) / (1 + β))) u := by
    simpa only [hz] using ht
  have htu (t : ℝ) (ht : t ∈ Icc (z : ℝ) u) : t ∈ Icc 0 U :=
    ⟨(hz0.trans_le ht.1).le, ht.2.trans u.property.2⟩
  have hτscale (t : ℝ) (ht : t ∈ Icc (z : ℝ) u) :
      j ≤ t * Real.exp (a * ((τ t : ℝ) / (1 + β))) := by
    have hh := hscale _ (hpoint t ht).1.le
    simpa only [(hpoint t ht).2.1] using hh
  have hhist (t : ℝ) (ht : t ∈ Icc (z : ℝ) u) (w : Icc 0 V) (hw : w ∈ Icc (τ t) b) := by
    have htw : (τ t : ℝ) / (1 + β) ≤ (w : ℝ) / (1 + β) :=
      div_le_div_of_nonneg_right hw.1 hα.le
    have hTw := (hpoint t ht).1.trans_le htw
    have hgt : g ((w : ℝ) / (1 + β)) ≤ t := by
      have hh := hga (hpoint t ht).1.le hTw.le htw
      simpa only [(hpoint t ht).2.1] using hh
    exact hhistory t (hrow t ht) w hTw hgt hw.2
  have hdilate (v : Icc 0 V) : (1 + β) * ((v : ℝ) / (1 + β)) = v := by field_simp
  have hfeedback (t : ℝ) (ht : t ∈ Icc (z : ℝ) u) :
      |x.2.1 (projIcc 0 U hU.le t) b 0| * (N * t ^ (k / a * β - 1)) ≤
        (L * N * C / (1 + β) * j ^ (-(2 * k / a - k / a * β))) * jac t *
          Real.exp (-(2 * k) * b + (2 * k - 3 * (k * β / (1 + β))) * τ t) := by
    have hh := (late_weighted_sources (ζ := 0) (A := 0)
      (hz0.trans_le ht.1) hj ha hk.le hβ hβ2 hC hL hN (hτscale t ht)
      (hpoint t ht).2.2.2.2.2.1 (hlam t (hrow t ht)) (by simp)).1
    simpa only [hdilate] using hh
  have hfree : ∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.2.1 (projIcc 0 U hU.le t) b 0| *
        |x.1 (projIcc 0 U hU.le t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
          (L * C / (1 + β) * j ^ (-(2 * k / a))) * jac t *
            Real.exp (-(2 * k) * b + (k - k * β / (1 + β)) * τ t) * A (τ t) := by
    filter_upwards [hsource] with t ht
    intro htm
    have hgt : (G (τ t) : ℝ) = t := by
      rw [hG (τ t) (hpoint t htm).1.le
        (by rw [(hpoint t htm).2.1]; exact (htu t htm).2)]
      exact (hpoint t htm).2.1
    have hAt := ht (τ t) hgt
    rw [show k / (1 + β) * (τ t : ℝ) = k * ((τ t : ℝ) / (1 + β)) by ring] at hAt
    have hh := (late_weighted_sources (hz0.trans_le htm.1) hj ha hk.le hβ hβ2 hC hL hN
      (hτscale t htm) (hpoint t htm).2.2.2.2.2.1 (hlam t (hrow t htm)) hAt).2
    simpa only [hdilate] using hh
  have hbound := hx.late_radiation_causal hU.le hV hUR hp hf hρ (by positivity) hgap A M hM0
    z u hzu b Q J (fun t => N * t ^ (k / a * β - 1)) hQz
    (fun t ht => (hpoint t ht).2.2.2.1) hder
    (fun t ht => mul_nonneg hN (Real.rpow_nonneg (htu t ht).1 _))
    (fun t ht w hw => (hhist t ht w hw).1) (fun t ht w hw => (hhist t ht w hw).2.1)
    hfeedback (fun t ht w hw => (hhist t ht w hw).2.2) hfree
  have hzproj : projIcc 0 U hU.le (g ((b : ℝ) / (1 + β))) = z := by
    rw [← hz, projIcc_of_mem hU.le z.property]
  refine ⟨τ u, (hpoint u ⟨hzu, le_rfl⟩).1, (hpoint u ⟨hzu, le_rfl⟩).2.1,
    (hpoint u ⟨hzu, le_rfl⟩).2.2.2.1, ?_⟩
  simpa only [hzproj] using hbound

end CauchyHorizon
