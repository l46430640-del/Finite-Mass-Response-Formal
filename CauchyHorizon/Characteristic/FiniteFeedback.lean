import CauchyHorizon.Characteristic.FiniteKappa
import CauchyHorizon.Characteristic.OuterBootstrap

/-! Uniform small constraint energy on a fixed finite history as the width shrinks. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_finite_small_width_kappa {M e Λ T ρ A η : ℝ} {h r : ℝ → ℝ}
    (hT : 0 ≤ T) (hrp : 0 < r 0) (hρ : 0 < ρ) (hA : 0 ≤ A) (hη : 0 < η)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ δ → V ≤ T →
        (∀ u v, ρ ≤ x.1 u v 0) → ∀ (u : Icc 0 U) (v : Icc 0 V),
          let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
            (-intervalExtension hU ν t v)) ≤ η ∧
          Real.exp (-η) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) := by
  obtain ⟨R, L, C, hR, _hL, hC, hgeom⟩ :=
    exists_uniform_finite_geometry_on_subrectangles (Vmax := T) hc hi hrc hr0 hφ hrd hρ
  obtain ⟨B, hB, hscalar⟩ := exists_uniform_finite_scalar_on_subrectangles hT hrp hc hi hrc hr0 hφ hrd hρ hA
  let n := Real.exp (-C * T)
  have hn : 0 < n := Real.exp_pos _
  let C₁ := (R / n) * (2 * B ^ 2 * A ^ 2)
  let C₂ := (R / n) * (2 * B ^ 2)
  obtain ⟨δ, hδ, hδ1, hδr, _hgap, _hsmall, herror⟩ := exists_small_outer_width hrp hρ hη 0 0 C₁ C₂
  refine ⟨δ, hδ, hδ1, hδr, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hUU hVT hlo u v
  have hg := hgeom hU hV hVT hUR hp hf hx hlo
  have hs := hscalar hU (hUU.trans hδ1) hV hVT hUR hp hf hfn hx hlo
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hnlo (q : Icc 0 U) (w : Icc 0 V) : n ≤ -ν q w :=
    (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (w.property.2.trans hVT) (neg_nonpos.2 hC))).trans
      (hg q w).2.2.2.1
  let q : ℝ → ℝ := fun t => intervalExtension hU x.1 t v 0 / (-intervalExtension hU ν t v)
  have hq (t : ℝ) : q t ≤ R / n :=
    div_le_div₀ hR.le (hg (projIcc 0 U hU t) v).1 hn (hnlo (projIcc 0 U hU t) v)
  have hk := hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
  have hqi : IntervalIntegrable (fun t => q t * (x.2.2 t v 1) ^ 2) volume 0 U := by
    simpa only [q, div_mul_eq_mul_div] using hk.1
  have hψ : ∀ᵐ t ∂volume.restrict (Icc 0 U), |x.2.2 t v 1| ≤ B * |f t| + B := by
    filter_upwards [hs.2.1] with t ht
    simpa only [mul_add, mul_one] using ht v
  have he := weighted_quadratic_integral_le_lp hU ((by norm_num : (2 : ℝ≥0∞) ≤ 4).trans hp)
    hf hA hfn hB.le hB.le (div_nonneg hR.le hn.le) hqi (Filter.Eventually.of_forall hq) hψ u
  have heq : (∫ t in (0 : ℝ)..u, q t * (x.2.2 t v 1) ^ 2) =
      ∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
        (-intervalExtension hU ν t v) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact div_mul_eq_mul_div _ _ _
  rw [heq] at he
  have huδ : (u : ℝ) ≤ δ := u.property.2.trans hUU
  have hpow : (u : ℝ) ^ (1 - 2 / p.toReal) ≤ δ ^ (1 / 2 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge' u.property.1 (huδ.trans hδ1) (by norm_num)
      (incoming_exponent_bounds hp).2).trans (Real.rpow_le_rpow u.property.1 huδ (by norm_num))
  have henergy : (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU ν t v)) ≤ η := by
    apply he.trans
    calc
      _ ≤ (R / n) * (2 * B ^ 2 * A ^ 2 * δ ^ (1 / 2 : ℝ) + 2 * B ^ 2 * δ) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hpow (by positivity))
          (mul_le_mul_of_nonneg_left huδ (by positivity))) (div_nonneg hR.le hn.le)
      _ = C₁ * δ ^ (1 / 2 : ℝ) + C₂ * δ := by dsimp only [C₁, C₂]; ring
      _ ≤ η := herror
  refine ⟨henergy, ?_⟩
  rw [hk.2 u]
  exact Real.exp_le_exp.2 (neg_le_neg henergy)

end CauchyHorizon
