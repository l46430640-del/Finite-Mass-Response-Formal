import CauchyHorizon.Characteristic.ConstraintWave
import CauchyHorizon.Reduced.LongitudinalConstraint

/-! The actual horizon data propagate the outgoing Raychaudhuri constraint. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem horizonWaveVelocity_radial_derivative {M e Λ V : ℝ} {h r : ℝ → ℝ}
    (hV : 0 ≤ V) (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t)) (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {t : ℝ} (ht : t ∈ Icc 0 V) :
    let w := horizonWaveVelocity M e Λ V hc hi hrc hr0
    HasDerivWithinAt (fun s => intervalExtension hV w s 0)
      (w ⟨t, ht⟩ 2 * w ⟨t, ht⟩ 0 - r t * (w ⟨t, ht⟩ 1) ^ 2) (Icc 0 V) t := by
  dsimp only
  have hd := horizonFunction_hasDerivWithinAt ((hrd t ht.1).mono (fun _ (hw : _ ∈ Icc 0 V) => hw.1))
    (horizonMass_hasDerivAt hc hi M t).hasDerivWithinAt (hr0 t) e Λ
  have he := hd.congr_of_mem (f₁ := fun s => intervalExtension hV
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) s 0) (fun s hs => ?_) ht
  · apply he.congr_deriv
    change 2 * horizonK (r t) (horizonMass M h t) e Λ * horizonFunction (r t) (horizonMass M h t) e Λ -
      2 * (h t ^ 2 / 2) / r t = 2 * horizonK (r t) (horizonMass M h t) e Λ *
        horizonFunction (r t) (horizonMass M h t) e Λ - r t * (h t / r t) ^ 2
    field_simp [hr0 t]
  · simp only [intervalExtension_apply, projIcc_of_mem hV hs]
    rfl

variable {M e Λ U V : ℝ} {h r : ℝ → ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
  {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
  {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)

include hφ hrd hx

theorem IsWaveIntegral.outgoing_radial_constraint (u : Icc 0 U) {v : ℝ} (hv : v ∈ Icc 0 V) :
    HasDerivWithinAt (fun t => intervalExtension hV (x.2.1 u) t 0)
      (x.2.1 u ⟨v, hv⟩ 2 * x.2.1 u ⟨v, hv⟩ 0 -
        x.1 u ⟨v, hv⟩ 0 * (x.2.1 u ⟨v, hv⟩ 1) ^ 2) (Icc 0 V) v := by
  apply hx.longitudinal_constraint hx.choose rfl hv _ u
  rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 ⟨v, hv⟩]
  exact horizonWaveVelocity_radial_derivative hV hc hi hrc hr0 hrd hv

theorem IsWaveIntegral.outgoing_integral_constraint (u : Icc 0 U) (v : Icc 0 V) :
    x.2.1 u v 0 * Real.exp (-x.1 u v 2) =
      x.2.1 u ⟨0, le_rfl, hV⟩ 0 * Real.exp (-x.1 u ⟨0, le_rfl, hV⟩ 2) -
        ∫ t in (0 : ℝ)..v, intervalExtension hV (x.1 u) t 0 *
          Real.exp (-intervalExtension hV (x.1 u) t 2) * (intervalExtension hV (x.2.1 u) t 1) ^ 2 := by
  apply hx.longitudinal_constraint_integral hx.choose rfl _ u v
  intro t ht
  rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 ⟨t, ht⟩]
  exact horizonWaveVelocity_radial_derivative hV hc hi hrc hr0 hrd ht

theorem IsWaveIntegral.outgoing_trapped_radius (u : Icc 0 U) (a b : Icc 0 V)
    (hab : a ≤ b) (ha : x.2.1 u a 0 < 0) :
    x.2.1 u b 0 < 0 ∧ x.1 u b 0 ≤ x.1 u a 0 := by
  let J : ℝ → ℝ := fun t => intervalExtension hV (x.1 u) t 0 *
    Real.exp (-intervalExtension hV (x.1 u) t 2) * (intervalExtension hV (x.2.1 u) t 1) ^ 2
  have hJc : Continuous J := by fun_prop
  have hJ (t : ℝ) : 0 ≤ J t := mul_nonneg (mul_nonneg
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u (projIcc 0 V hV t)).2.1.le
    (Real.exp_pos _).le) (sq_nonneg _)
  have hl (w : Icc 0 V) (haw : a ≤ w) : x.2.1 u w 0 < 0 := by
    have hiw := intervalIntegral.integral_mono_interval (μ := volume) le_rfl a.property.1 haw
      (Filter.Eventually.of_forall hJ) (hJc.intervalIntegrable (0 : ℝ) w)
    have hca := hx.outgoing_integral_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a
    have hcw := hx.outgoing_integral_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp hf u w
    have hneg := mul_neg_of_neg_of_pos ha (Real.exp_pos (-x.1 u a 2))
    have hh : x.2.1 u w 0 * Real.exp (-x.1 u w 2) < 0 := by
      dsimp only [J] at hiw
      linarith only [hiw, hca, hcw, hneg]
    by_contra hnot
    have hnonneg := mul_nonneg (le_of_not_gt hnot) (Real.exp_pos (-x.1 u w 2)).le
    linarith only [hh, hnonneg]
  let rad : ℝ → ℝ := fun t => intervalExtension hV (x.1 u) t 0
  let vel : ℝ → ℝ := fun t => intervalExtension hV (x.2.1 u) t 0
  have hanti : AntitoneOn rad (Icc (a : ℝ) b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := vel) (convex_Icc _ _) (by fun_prop)
    · intro t ht
      have ht' := interior_subset ht
      have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht'.1, ht'.2.trans b.property.2⟩
      have hd := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
        (hx.longitudinal_derivative u htV)
      change HasDerivWithinAt rad (x.2.1 u ⟨t, htV⟩ 0) (Icc 0 V) t at hd
      have hd' : HasDerivWithinAt rad (vel t) (Icc 0 V) t := by
        simpa only [vel, intervalExtension_apply, projIcc_of_mem hV htV] using hd
      exact hd'.mono (fun t ht => by
        have ht' := interior_subset ht
        exact ⟨a.property.1.trans ht'.1, ht'.2.trans b.property.2⟩)
    · intro t ht
      have ht' := interior_subset ht
      have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht'.1, ht'.2.trans b.property.2⟩
      simpa only [vel, intervalExtension_apply, projIcc_of_mem hV htV] using (hl ⟨t, htV⟩ ht'.1).le
  refine ⟨hl b hab, ?_⟩
  simpa only [rad, intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property] using
    hanti (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

end CauchyHorizon
