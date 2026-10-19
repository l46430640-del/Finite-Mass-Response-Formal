import CauchyHorizon.Characteristic.ConformalIdentity
import CauchyHorizon.Characteristic.FiniteKappa

/-! Weighted Young controls the actual conformal source by constraint energy. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem conformal_source_bound {r n κ C a b ρ G H : ℝ}
    (hρ : 0 < ρ) (hr : ρ ≤ r) (hn : 0 < n) (hk : 0 ≤ κ) (hk1 : κ ≤ 1)
    (hC : |C| ≤ G) (hb : |b| ≤ H) :
    |-(κ / n) * C * a ^ 2 + 2 * a * b| ≤
      (G / ρ + 1) * (r * a ^ 2 / n) + (H ^ 2 / ρ) * n := by
  have hr0 : 0 < r := hρ.trans_le hr
  have hG : 0 ≤ G := (abs_nonneg C).trans hC
  have hH : 0 ≤ H := (abs_nonneg b).trans hb
  have hquad : |-(κ / n) * C * a ^ 2| ≤ (G / ρ) * (r * a ^ 2 / n) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (div_nonneg hk hn.le), abs_pow, sq_abs]
    have hh : κ * |C| ≤ G := (mul_le_mul hk1 hC (abs_nonneg _) (by norm_num)).trans_eq (one_mul G)
    have hh' : κ * |C| * ρ ≤ G * r :=
      (mul_le_mul_of_nonneg_right hh hρ.le).trans (mul_le_mul_of_nonneg_left hr hG)
    apply (mul_le_mul_iff_left₀ (mul_pos hρ hn)).mp
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_right hh' (sq_nonneg a)]
  have hyoung : |2 * a * b| ≤ r * a ^ 2 / n + n * b ^ 2 / r := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (mul_le_mul_iff_left₀ (mul_pos hr0 hn)).mp
    field_simp
    nlinarith only [sq_nonneg (r * |a| - n * |b|), sq_abs a, sq_abs b]
  have hb2 : b ^ 2 ≤ H ^ 2 := by nlinarith only [(sq_le_sq₀ (abs_nonneg b) hH).2 hb, sq_abs b]
  have hterm : n * b ^ 2 / r ≤ (H ^ 2 / ρ) * n := by
    have hh : b ^ 2 * ρ ≤ H ^ 2 * r :=
      (mul_le_mul_of_nonneg_right hb2 hρ.le).trans (mul_le_mul_of_nonneg_left hr (sq_nonneg H))
    apply (mul_le_mul_iff_left₀ (mul_pos hr0 hρ)).mp
    field_simp
    nlinarith only [hh]
  calc
    _ ≤ |-(κ / n) * C * a ^ 2| + |2 * a * b| := abs_add_le _ _
    _ ≤ (G / ρ) * (r * a ^ 2 / n) + (r * a ^ 2 / n + (H ^ 2 / ρ) * n) :=
      add_le_add hquad (hyoung.trans (add_le_add le_rfl hterm))
    _ = _ := by ring

theorem IsWaveIntegral.horizon_conformal_bound {M e Λ U V ρ G H : ℝ} {h r : ℝ → ℝ}
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
    (hρ : 0 < ρ) (v : Icc 0 V)
    (hlo : ∀ u, ρ ≤ x.1 u v 0)
    (hG : ∀ u, |1 - e ^ 2 / (x.1 u v 0) ^ 2 - Λ * (x.1 u v 0) ^ 2| ≤ G)
    (hH : ∀ u, |x.2.1 u v 1| ≤ H) (u : Icc 0 U) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let K := horizonK (x.1 u v 0) (massField e Λ x.1 x.2.1 N hx.choose u v) e Λ
    let Q := ∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU N t v)
    |x.2.1 u v 2 - 2 * K| ≤ (2 * |K| + G / ρ + 1) * Q + (H ^ 2 / ρ) * (r v - x.1 u v 0) := by
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let E := fun t => intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 / (-intervalExtension hU N t v)
  let κ := fun t => -Real.exp (intervalExtension hU x.1 t v 2) / (4 * intervalExtension hU N t v)
  let S := fun t => κ t / intervalExtension hU N t v *
    (1 - e ^ 2 / (intervalExtension hU x.1 t v 0) ^ 2 - Λ * (intervalExtension hU x.1 t v 0) ^ 2) *
    (x.2.2 t v 1) ^ 2 + 2 * x.2.2 t v 1 * intervalExtension hU x.2.1 t v 1
  let K := horizonK (x.1 u v 0) (massField e Λ x.1 x.2.1 N hx.choose u v) e Λ
  let Q := ∫ t in (0 : ℝ)..u, E t
  obtain ⟨hEi, hκid⟩ := hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
  obtain ⟨hSi, hsource⟩ := hx.horizon_conformal_identity hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
  have hκ1 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.2.2
  have hκ : |κ u - 1| ≤ Q := by
    change -Real.exp (x.1 u v 2) / (4 * N u v) ≤ 1 at hκ1
    simp only [κ, intervalExtension_apply, projIcc_of_mem hU u.property]
    rw [abs_of_nonpos (sub_nonpos.2 hκ1), hκid u]
    have he := Real.add_one_le_exp (-Q)
    change -(Real.exp (-Q) - 1) ≤ Q
    linarith only [he]
  have hpt (t : ℝ) : |S t| ≤ (G / ρ + 1) * E t + (H ^ 2 / ρ) * (-intervalExtension hU N t v) := by
    let w := projIcc 0 U hU t
    have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf w v
    have hh := conformal_source_bound hρ (hlo w) (neg_pos.2 hg.2.2.1)
      hg.2.2.2.1.le hg.2.2.2.2 (hG w) (hH w) (a := x.2.2 t v 1)
    simpa only [S, E, κ, N, intervalExtension_apply, w, div_neg, neg_neg] using hh
  have hNc : Continuous (fun t => -intervalExtension hU N t v) := by fun_prop
  have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le u.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl u.property.2
  have hEu : IntervalIntegrable E volume 0 u := hEi.mono_set hsub
  have hNu : IntervalIntegrable (fun t => -intervalExtension hU N t v) volume 0 u :=
    hNc.intervalIntegrable _ _
  have hb := intervalIntegral.integral_mono_on u.property.1 (hSi.mono_set hsub).abs
    ((hEu.const_mul (G / ρ + 1)).add (hNu.const_mul (H ^ 2 / ρ))) (fun t _ => hpt t)
  rw [intervalIntegral.integral_add (hEu.const_mul _) (hNu.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hb
  have hrad : (∫ t in (0 : ℝ)..u, -intervalExtension hU N t v) = r v - x.1 u v 0 := by
    obtain ⟨hn, _hl⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)
    have he := hx.radial_horizontal_identity hx.choose rfl hn u v
    have he0 := hx.radial_horizontal_identity hx.choose rfl hn ⟨0, le_rfl, hU⟩ v
    have htrace := (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v
    have hpv : continuousPrimitive hU N u v = ∫ t in (0 : ℝ)..u, intervalExtension hU N t v := by
      exact ((ContinuousMap.evalCLM ℝ v).intervalIntegral_comp_comm
        (show IntervalIntegrable (intervalExtension hU N) volume 0 u from
          (intervalExtension hU N).continuous.intervalIntegrable _ _)).symm
    have hp0 : continuousPrimitive hU N ⟨0, le_rfl, hU⟩ v = 0 := by simp [continuousPrimitive]
    rw [htrace, hp0, add_zero] at he0
    rw [← he0, hpv] at he
    change x.1 u v 0 = r v + ∫ t in (0 : ℝ)..u, intervalExtension hU N t v at he
    rw [intervalIntegral.integral_neg]
    linarith only [he]
  rw [hrad] at hb
  have hh : |x.2.1 u v 2 - 2 * K| ≤ 2 * |K| * |κ u - 1| + ∫ t in (0 : ℝ)..u, |S t| := by
    simpa only [K, κ, N, S, intervalExtension_apply, projIcc_of_mem hU u.property] using (hsource u).2
  change |x.2.1 u v 2 - 2 * K| ≤ (2 * |K| + G / ρ + 1) * Q + (H ^ 2 / ρ) * (r v - x.1 u v 0)
  have hkQ := mul_le_mul_of_nonneg_left hκ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg K))
  nlinarith only [hh, hb, hkQ]

end CauchyHorizon
