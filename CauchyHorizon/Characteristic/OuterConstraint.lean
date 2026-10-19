import CauchyHorizon.Characteristic.OuterBootstrap

/-! The outer constraint energy has a uniform small-width bound. -/

open scoped ENNReal

namespace CauchyHorizon

theorem outer_constraint_envelope {a c ρ R r₀ n N L H A δ u v : ℝ} {p : ℝ≥0∞}
    (hp : 4 ≤ p) (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : c < a)
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hr : 0 ≤ r₀) (hn : 0 < n)
    (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : u * Real.exp (a * v) ≤ δ) :
    let E := 2 * (H + L * (r₀ / ρ) * (A * δ ^ (1 - 1 / p.toReal))) / ρ
    let E₀ := 2 * (H + L * (r₀ / ρ) * A) / ρ
    (2 * R / n) * ((r₀ / ρ) ^ 2 * A ^ 2 * Real.exp (-a * v) * u ^ (1 - 2 / p.toReal) +
      (N / (ρ * (a - c)) * E) ^ 2 * u * Real.exp ((a - 2 * c) * v)) ≤
    ((2 * R / n) * (r₀ / ρ) ^ 2 * A ^ 2) * δ ^ (1 / 2 : ℝ) +
      ((2 * R / n) * (N / (ρ * (a - c)) * E₀) ^ 2) * δ := by
  let E := 2 * (H + L * (r₀ / ρ) * (A * δ ^ (1 - 1 / p.toReal))) / ρ
  let E₀ := 2 * (H + L * (r₀ / ρ) * A) / ρ
  let β := N / (ρ * (a - c)) * E
  let β₀ := N / (ρ * (a - c)) * E₀
  have huδ : u ≤ δ := (le_mul_of_one_le_right hu (Real.one_le_exp_iff.2 (mul_nonneg ha hv))).trans hw
  obtain ⟨hb1, hb2⟩ := incoming_exponent_bounds hp
  have he : δ ^ (1 - 1 / p.toReal) ≤ 1 := Real.rpow_le_one hδ hδ1 (by linarith only [hb1])
  have hE : E ≤ E₀ := by
    dsimp only [E, E₀]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hA he) (by positivity)))
      (by norm_num)) hρ.le
  have hβ : β ≤ β₀ := mul_le_mul_of_nonneg_left hE (by positivity)
  have hβ0 : 0 ≤ β := by dsimp only [β, E]; positivity
  have hβsq : β ^ 2 ≤ β₀ ^ 2 := (sq_le_sq₀ hβ0 (hβ0.trans hβ)).2 hβ
  have hupow : u ^ (1 - 2 / p.toReal) ≤ δ ^ (1 / 2 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge' hu (huδ.trans hδ1) (by norm_num) hb2).trans
      (Real.rpow_le_rpow hu huδ (by norm_num))
  have hem : Real.exp (-a * v) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith only [mul_nonneg ha hv])
  have hfirst := mul_le_mul hem hupow (Real.rpow_nonneg hu _) zero_le_one
  simp only [one_mul] at hfirst
  have heg : Real.exp ((a - 2 * c) * v) ≤ Real.exp (a * v) :=
    Real.exp_le_exp.2 (by nlinarith only [mul_nonneg hc hv])
  have hsecond := mul_le_mul hβsq ((mul_le_mul_of_nonneg_left heg hu).trans hw)
    (mul_nonneg hu (Real.exp_pos _).le) (sq_nonneg β₀)
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ (r₀ / ρ) ^ 2 * A ^ 2)) hsecond
  have htotal := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * R / n)
  dsimp only
  dsimp only [β, β₀, E, E₀] at htotal
  nlinarith only [htotal]

end CauchyHorizon
