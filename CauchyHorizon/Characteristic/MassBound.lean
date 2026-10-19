import CauchyHorizon.Characteristic.MassConstraint

/-! Algebraic mass control and the uniform initial mass bound. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem renormalizedMass_le_of_optical {r ν l ell e Λ ρ R Q : ℝ}
    (hρ : 0 < ρ) (hr : ρ ≤ r) (hR : r ≤ R) (hΛ : 0 ≤ Λ) (hQ : 0 ≤ Q)
    (hprod : (-ν) * (-l / Real.exp ell) ≤ Q) :
    renormalizedMass r ν l ell e Λ ≤ R / 2 + e ^ 2 / (2 * ρ) + 2 * R * Q := by
  have hr0 := hρ.le.trans hr
  have he := div_le_div_of_nonneg_left (sq_nonneg e)
    (by positivity : 0 < 2 * ρ) (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
  have hterm : 2 * r * ((-ν) * (-l / Real.exp ell)) ≤ 2 * R * Q :=
    (mul_le_mul_of_nonneg_left hprod (by positivity)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num)) hQ)
  have hcos : 0 ≤ Λ * r ^ 3 / 6 := by positivity
  unfold renormalizedMass
  rw [Real.exp_neg]
  have heq : 2 * r * ν * l * (Real.exp ell)⁻¹ = 2 * r * ((-ν) * (-l / Real.exp ell)) := by ring
  rw [heq]
  linarith only [hR, he, hterm, hcos]

theorem exists_uniform_initial_mass_bound {M e Λ ρ A : ℝ} {h r : ℝ → ℝ}
    (hrp : 0 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (hρ : 0 < ρ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {U : ℝ} (hU : 0 ≤ U), U ≤ 1 → ∀ hUR : U < r 0,
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
      ∀ {x : WaveState U 0}
        (hx : IsWaveIntegral hU le_rfl e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ 0 hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ u v, ρ ≤ x.1 u v 0) → ∀ u : Icc 0 U,
          let N := radialNuField le_rfl e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          |massField e Λ x.1 x.2.1 N hx.choose u ⟨0, le_rfl, le_rfl⟩| ≤ C := by
  obtain ⟨R, L, _, hR, hL, _, hgeom⟩ :=
    exists_uniform_finite_geometry_on_subrectangles (Vmax := 0) hc hi hrc hr0 hφ hrd hρ
  obtain ⟨k, _, hk, _, hkappa⟩ :=
    exists_uniform_finite_kappa_on_subrectangles (Vmax := 0) le_rfl hrp hc hi hrc hr0 hφ hrd hρ hA
  refine ⟨|horizonMass M h 0| + (R * L / 2) * k⁻¹, by positivity, ?_⟩
  intro U hU hU1 hUR p hp f hf hfn x hx hlo u
  have hg := hgeom hU le_rfl le_rfl hUR hp hf hx hlo
  have hkap := (hkappa hU hU1 le_rfl le_rfl hUR hp hf hfn hx hlo u ⟨0, le_rfl, le_rfl⟩).1
  have hm := hx.mass_kappa_bound hU le_rfl hUR hc hi hrc hr0 hφ hrd hp hf hR.le
    (fun u v => (hg u v).1) (fun u v => (hg u v).2.2.1) u ⟨0, le_rfl, le_rfl⟩
  have hinv := one_div_le_one_div_of_le hk hkap
  simp only [one_div] at hinv
  have hb := hm.trans (mul_le_mul_of_nonneg_left
    (show _ - 1 ≤ k⁻¹ by linarith only [hinv]) (by positivity : 0 ≤ R * L / 2))
  apply abs_le.2
  constructor <;> linarith only [(abs_le.1 hb).1, (abs_le.1 hb).2,
    neg_abs_le (horizonMass M h 0), le_abs_self (horizonMass M h 0)]

end CauchyHorizon
