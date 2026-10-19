import CauchyHorizon.Characteristic.FiniteScalar
import CauchyHorizon.Reduced.FiniteKappa

/-! Positive lapse and conformal lower bounds chosen before the incoming data. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_kappa_exponential {M e Λ U V : ℝ} {h r : ℝ → ℝ}
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
    let S := fun t => intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU N t v)
    IntervalIntegrable S volume 0 U ∧ ∀ u : Icc 0 U,
      -Real.exp (x.1 u v 2) / (4 * N u v) = Real.exp (-(∫ t in (0 : ℝ)..u, S t)) := by
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)
  exact hx.kappa_exponential hx.choose rfl hn hl
    (fun u v => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1)
    (fun v => (hx.horizon_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf v).2.1) v

theorem exists_uniform_finite_kappa_on_subrectangles {M e Λ Vmax : ℝ} {h r : ℝ → ℝ}
    (hVmax0 : 0 ≤ Vmax) (hrp : 0 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ k w : ℝ, 0 < k ∧ 0 < w ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (_hU1 : U ≤ 1) (hV : 0 ≤ V), V ≤ Vmax → ∀ hUR : U < r 0,
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ J →
      ∀ {x : WaveState U V}
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ u v, ρ ≤ x.1 u v 0) → ∀ u : Icc 0 U, ∀ v : Icc 0 V,
          let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          k ≤ -Real.exp (x.1 u v 2) / (4 * N u v) ∧ w ≤ Real.exp (x.1 u v 2) := by
  obtain ⟨R, A, C, hR, _hA, hC, hgeom⟩ :=
    exists_uniform_finite_geometry_on_subrectangles (Vmax := Vmax) hc hi hrc hr0 hφ hrd hρ
  obtain ⟨B, hB, hscalar⟩ := exists_uniform_finite_scalar_on_subrectangles hVmax0 hrp hc hi hrc hr0 hφ hrd hρ hJ
  let n := Real.exp (-C * Vmax)
  let K := 2 * B ^ 2 * (J ^ 2 + 1)
  let k := Real.exp (-(R / n * K))
  refine ⟨k, 4 * n * k, Real.exp_pos _, by dsimp only [n, k]; positivity, ?_⟩
  intro U V hU hU1 hV hVmax hUR p hp f hf hfn x hx hlo
  have hg := hgeom hU hV hVmax hUR hp hf hx hlo
  have hs := hscalar hU hU1 hV hVmax hUR hp hf hfn hx hlo
  have hf2 := hf.mono_exponent ((by norm_num : (2 : ℝ≥0∞) ≤ 4).trans hp)
  have hfi : IntervalIntegrable (fun t => (f t) ^ 2) volume 0 U := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    change Integrable (fun t => (f t) ^ 2) (volume.restrict (Icc 0 U))
    simpa only [pow_two] using (hf2.mul' hf2 (r := 1)).integrable le_rfl
  have hJ2 : (∫ t in (0 : ℝ)..U, (f t) ^ 2) ≤ J ^ 2 :=
    (incoming_integral_sq_le_lp hU hU1 hp hf).trans ((sq_le_sq₀ ENNReal.toReal_nonneg hJ).2 hfn)
  have henergy (v : Icc 0 V) : (∫ t in (0 : ℝ)..U, (x.2.2 t v 1) ^ 2) ≤ K := by
    let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (1 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
    have hphi : MemLp (fun t => x.2.2 t v 1) 2 (volume.restrict (Icc 0 U)) :=
      T.comp_memLp' (Lp.memLp x.2.2)
    have hphii : IntervalIntegrable (fun t => (x.2.2 t v 1) ^ 2) volume 0 U := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      change Integrable (fun t => (x.2.2 t v 1) ^ 2) (volume.restrict (Icc 0 U))
      simpa only [pow_two] using (hphi.mul' hphi (r := 1)).integrable le_rfl
    have hb : ∀ᵐ t ∂volume.restrict (Icc 0 U), (x.2.2 t v 1) ^ 2 ≤ (2 * B ^ 2) * ((f t) ^ 2 + 1) := by
      filter_upwards [hs.2.1] with t ht
      have hsquare := (sq_le_sq₀ (abs_nonneg (x.2.2 t v 1))
        (mul_nonneg hB.le (by positivity))).2 (ht v)
      rw [sq_abs, mul_pow] at hsquare
      have hsum : (|f t| + 1) ^ 2 ≤ 2 * ((f t) ^ 2 + 1) := by
        nlinarith [sq_abs (f t), sq_nonneg (|f t| - 1)]
      nlinarith only [hsquare, mul_le_mul_of_nonneg_left hsum (sq_nonneg B)]
    have hh := intervalIntegral.integral_mono_ae_restrict hU hphii
      ((hfi.add intervalIntegrable_const).const_mul (2 * B ^ 2)) hb
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hfi intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add hJ2 hU1) (by positivity))
  have hnlo (u : Icc 0 U) (v : Icc 0 V) :
      n ≤ -radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v :=
    (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (v.property.2.trans hVmax) (neg_nonpos.2 hC))).trans (hg u v).2.2.2.1
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)
  exact hx.finite_kappa_bound hx.choose rfl hn hl hR.le (Real.exp_pos _) (fun u v => (hg u v).1)
    hnlo (fun v => (hx.horizon_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf v).2.1) henergy

theorem exists_uniform_finite_kappa {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ k w : ℝ, 0 < k ∧ 0 < w ∧
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ J →
      ∀ {x : WaveState U V}
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ u v, ρ ≤ x.1 u v 0) → ∀ u : Icc 0 U, ∀ v : Icc 0 V,
          let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          k ≤ -Real.exp (x.1 u v 2) / (4 * N u v) ∧ w ≤ Real.exp (x.1 u v 2) := by
  obtain ⟨k, w, hk, hw, hb⟩ := exists_uniform_finite_kappa_on_subrectangles hV (hU.trans_lt hUR) hc hi hrc hr0 hφ hrd hρ hJ
  exact ⟨k, w, hk, hw, hb hU hU1 hV le_rfl hUR⟩

end CauchyHorizon
