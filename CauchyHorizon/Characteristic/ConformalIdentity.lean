import CauchyHorizon.Reduced.ConformalIdentity
import CauchyHorizon.Characteristic.MassFlux

/-! The horizon normalization removes the boundary term in the conformal error. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_conformal_identity {M e Λ U V : ℝ} {h r : ℝ → ℝ}
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
    (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let R := fun t => intervalExtension hU x.1 t v 0
    let m := fun t => intervalExtension hU (massField e Λ x.1 x.2.1 N hx.choose) t v
    let κ := fun t => -Real.exp (intervalExtension hU x.1 t v 2) / (4 * intervalExtension hU N t v)
    let K := fun t => horizonK (R t) (m t) e Λ
    let S := fun t => κ t / intervalExtension hU N t v * (1 - e ^ 2 / (R t) ^ 2 - Λ * (R t) ^ 2) *
      (x.2.2 t v 1) ^ 2 +
      2 * x.2.2 t v 1 * intervalExtension hU x.2.1 t v 1
    IntervalIntegrable S volume 0 U ∧ ∀ u : Icc 0 U,
      x.2.1 u v 2 - 2 * K u = 2 * K u * (κ u - 1) - ∫ t in (0 : ℝ)..u, S t ∧
      |x.2.1 u v 2 - 2 * K u| ≤
        2 * |K u| * |κ u - 1| + ∫ t in (0 : ℝ)..u, |S t| := by
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let R := fun t => intervalExtension hU x.1 t v 0
  let m := fun t => intervalExtension hU (massField e Λ x.1 x.2.1 N hx.choose) t v
  let κ := fun t => -Real.exp (intervalExtension hU x.1 t v 2) / (4 * intervalExtension hU N t v)
  let K := fun t => horizonK (R t) (m t) e Λ
  let D := fun t => 2 * K t * deriv κ t + 2 * κ t * deriv m t / (R t) ^ 2 +
    2 * x.2.2 t v 1 * intervalExtension hU x.2.1 t v 1
  let S := fun t => κ t / intervalExtension hU N t v * (1 - e ^ 2 / (R t) ^ 2 - Λ * (R t) ^ 2) *
    (x.2.2 t v 1) ^ 2 +
    2 * x.2.2 t v 1 * intervalExtension hU x.2.1 t v 1
  let o : Icc 0 U := ⟨0, le_rfl, hU⟩
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)
  have hν (u v) := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1.ne
  obtain ⟨hDi, hid⟩ := hx.conformal_horizontal_identity hx.choose rfl hn hl hν v
  have hκd := (hx.kappa_horizontal_regular hx.choose rfl hn hl hν v).2
  have hDS : D =ᵐ[volume.restrict (Icc 0 U)] S := by
    filter_upwards [hκd, hx.mass_horizontal_derivative hx.choose rfl hn hl,
      ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc 0 U)).ae_ne 0,
      (volume.restrict (Icc 0 U)).ae_ne U] with t hk hm ht ht0 htU
    have hnhds := Icc_mem_nhds (lt_of_le_of_ne ht.1 ht0.symm) (lt_of_le_of_ne ht.2 htU)
    dsimp only [D]
    rw [(hk.hasDerivAt hnhds).deriv, ((hm v).hasDerivAt hnhds).deriv]
    simp only [S, K, R, κ, m, N, intervalExtension_apply, projIcc_of_mem hU ht,
      massField_apply, horizonK, renormalizedMass, Real.exp_neg]
    have hrn := hx.choose ⟨t, ht⟩ v
    have hνn := hν ⟨t, ht⟩ v
    field_simp [hrn, hνn, Real.exp_ne_zero]
    ring
  have hsu : uIoc (0 : ℝ) U ⊆ Icc 0 U := by rw [uIoc_of_le hU]; exact Ioc_subset_Icc_self
  have hSi : IntervalIntegrable S volume 0 U :=
    hDi.congr_ae (ae_mono (Measure.restrict_mono hsu le_rfl) hDS)
  have hκ : κ 0 = 1 := by
    have hg := hx.horizon_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
    simpa only [κ, N, intervalExtension_apply,
      projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from o.property)] using hg.2.2
  have hK : K 0 = horizonK (r v) (horizonMass M h v) e Λ := by
    have hray := (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v
    simp only [K, R, m, N, intervalExtension_apply,
      projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from o.property)]
    rw [hx.horizon_mass_trace hU hV hUR hc hi hrc hr0 hφ hrd hp hf v, hray]
    rfl
  have hw := waveIteration_outgoing_derivative hU hV e Λ
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x hx.choose
  rw [hx.choose_spec] at hw
  have hW : x.2.1 o v 2 = 2 * K 0 := by rw [hK, hw]; rfl
  refine ⟨hSi, ?_⟩
  intro u
  have hh : x.2.1 u v 2 - 2 * K u = 2 * K u * (κ u - 1) - ∫ t in (0 : ℝ)..u, S t := by
    have he := hid o u u.property.1
    change (x.2.1 u v 2 - 2 * K u) - (x.2.1 o v 2 - 2 * K 0) =
      2 * K u * (κ u - 1) - 2 * K 0 * (κ 0 - 1) - ∫ t in (0 : ℝ)..u, D t at he
    have hI : (∫ t in (0 : ℝ)..u, D t) = ∫ t in (0 : ℝ)..u, S t := by
      rw [intervalIntegral.integral_of_le u.property.1, intervalIntegral.integral_of_le u.property.1]
      exact integral_congr_ae (ae_mono (Measure.restrict_mono
        (show Ioc (0 : ℝ) u ⊆ Icc 0 U from fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩) le_rfl) hDS)
    simpa only [hW, hκ, hI, sub_self, mul_zero, sub_zero] using he
  refine ⟨hh, ?_⟩
  change |x.2.1 u v 2 - 2 * K u| ≤ 2 * |K u| * |κ u - 1| + ∫ t in (0 : ℝ)..u, |S t|
  rw [hh]
  calc
    _ ≤ |2 * K u * (κ u - 1)| + |∫ t in (0 : ℝ)..u, S t| := abs_sub _ _
    _ ≤ |2 * K u * (κ u - 1)| + ∫ t in (0 : ℝ)..u, |S t| :=
      add_le_add le_rfl (intervalIntegral.abs_integral_le_integral_abs u.property.1)
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

end CauchyHorizon
