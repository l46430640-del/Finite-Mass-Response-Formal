import CauchyHorizon.Characteristic.MassFlux
import CauchyHorizon.Characteristic.FiniteKappa

/-! The mass and lapse are controlled by the same nonnegative constraint source. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

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

theorem IsWaveIntegral.mass_kappa_bound {R L : ℝ} (hR : 0 ≤ R)
    (hrhi : ∀ u v, x.1 u v 0 ≤ R) (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    |m u v - horizonMass M h v| ≤ (R * L / 2) * ((-Real.exp (x.1 u v 2) / (4 * N u v))⁻¹ - 1) := by
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let D := fun t => intervalExtension hU x.1 t v 0 * Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2
  let J := fun t => -2 * (intervalExtension hU x.1 t v 0) ^ 2 * intervalExtension hU x.2.1 t v 0 *
    Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2
  obtain ⟨hn, hell⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)
  have hDi : IntervalIntegrable D volume 0 U := (hx.transverse_constraint_integral hx.choose rfl hn hell v).1
  have hD (t : ℝ) : 0 ≤ D t := mul_nonneg
    (mul_nonneg (hx.incoming_radius_pos hU hV hUR hp hf (projIcc 0 U hU t) v).le (Real.exp_pos _).le) (sq_nonneg _)
  have hbound (t : ℝ) : ‖J t‖ ≤ (2 * (R * L)) * D t := by
    let a := projIcc 0 U hU t
    have hrp := hx.incoming_radius_pos hU hV hUR hp hf a v
    calc
      _ = (2 * (x.1 a v 0 * |x.2.1 a v 0|)) * D t := by
        simp only [J, D, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hrp, abs_of_pos (Real.exp_pos _),
          sq_abs, intervalExtension_apply, a]
        norm_num
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul (hrhi a v) (hlam a v) (abs_nonneg _) hR) (by norm_num)) (hD t)
  have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le u.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl u.property.2
  have hb := intervalIntegral.norm_integral_le_of_norm_le u.property.1
    (Filter.Eventually.of_forall (fun t _ => hbound t)) ((hDi.mono_set hsub).const_mul (2 * (R * L)))
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hb
  have hg := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).1
  have he : (-Real.exp (x.1 u v 2) / (4 * N u v))⁻¹ - 1 = 4 * ∫ t in (0 : ℝ)..u, D t := by
    rw [inv_div, div_neg, div_eq_mul_inv, ← Real.exp_neg]
    change N u v * Real.exp (-x.1 u v 2) = -1 / 4 - ∫ t in (0 : ℝ)..u, D t at hg
    linarith only [hg]
  have hm := (hx.incoming_mass_integral hU hV hUR hc hi hrc hr0 hφ hrd hp hf v).2 u
  dsimp only
  rw [hm, add_sub_cancel_left]
  exact hb.trans_eq (by rw [he]; ring)

theorem IsWaveIntegral.mass_constraint_bound {R L B : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hrhi : ∀ u v, x.1 u v 0 ≤ R) (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (u : Icc 0 U) (v : Icc 0 V)
    (henergy : (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU (radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose) t v)) ≤ B) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    Real.exp (-B) ≤ -Real.exp (x.1 u v 2) / (4 * N u v) ∧
      |massField e Λ x.1 x.2.1 N hx.choose u v - horizonMass M h v| ≤ (R * L / 2) * (Real.exp B - 1) := by
  have hk := (hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd hp hf v).2 u
  have hm := hx.mass_kappa_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf hR hrhi hlam u v
  dsimp only at hm
  refine ⟨?_, ?_⟩
  · rw [hk]
    exact Real.exp_le_exp.2 (neg_le_neg henergy)
  · rw [hk, ← Real.exp_neg, neg_neg] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_le_exp.2 henergy) 1)
      (div_nonneg (mul_nonneg hR hL) (by norm_num)))

end CauchyHorizon
