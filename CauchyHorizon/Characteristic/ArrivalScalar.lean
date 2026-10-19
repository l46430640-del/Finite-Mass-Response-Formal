import CauchyHorizon.Characteristic.EntryScalar
import CauchyHorizon.Characteristic.ArrivalRadiation

/-! Horizontal scalar feedback using the exact matching-curve derivative. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.arrival_scalar_feedback {U V R e Λ φ₀ c ℓ ρ L Lᵧ B H : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hℓ : c < ℓ) (hρ : 0 < ρ) (hL : 0 ≤ L) (hLᵧ : 0 ≤ Lᵧ) (hB : 0 ≤ B)
    (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (T : C(Icc (z : ℝ) u, Icc 0 V)) :
    let τ := fun t => T (projIcc (z : ℝ) u hzu t)
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
    τ z = b →
    (∀ t ∈ Icc (z : ℝ) u, ν (projIcc 0 U hU t) (τ t) < 0) →
    (∀ t ∈ Icc (z : ℝ) u, -Lᵧ ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧
      x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0) →
    (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
      (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) →
    (∀ w ∈ Icc z u, ρ ≤ x.1 w b 0) →
    (∀ t ∈ Icc (z : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
      L * Real.exp (-ℓ * ((b : ℝ) - τ t))) →
    (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1| ≤
        (-ν (projIcc 0 U hU t) (τ t)) * Real.exp (-c * τ t) * B) →
    Real.exp (c * b) * |x.1 z b 0 * x.2.1 z b 1| ≤ H →
      Real.exp (c * b) * |x.2.1 u b 1| ≤ H / ρ + L * Lᵧ * B / (ρ ^ 2 * (ℓ - c)) := by
  dsimp only
  let τ := fun t => T (projIcc (z : ℝ) u hzu t)
  intro hτz hν hentry hder hr hlam hζ hθ
  let d := ℓ - c
  have hd : 0 < d := sub_pos.2 hℓ
  have hdiff := hx.arrival_radiation_majorant hU hV hUR hp hf hρ hL
    (ContinuousMap.const (Icc 0 V) B) z u hzu b T hτz hν hentry hder hr hlam hζ
  have hh := mul_le_mul_of_nonneg_left
    (abs_sub_le (x.1 u b 0 * x.2.1 u b 1) (x.1 z b 0 * x.2.1 z b 1) 0) (Real.exp_pos (c * b)).le
  simp only [sub_zero, mul_add] at hh
  have hh := hh.trans (add_le_add hdiff le_rfl)
  rw [add_comm] at hh
  have hkernel : (∫ t in (τ u : ℝ)..b, Real.exp (-d * ((b : ℝ) - t))) ≤ 1 / d := by
    have he : (∫ t in (τ u : ℝ)..b, Real.exp (-d * ((b : ℝ) - t))) =
        Real.exp (-d * b) * ∫ t in (τ u : ℝ)..b, Real.exp (d * t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, intervalIntegral.integral_comp_mul_left _ hd.ne', integral_exp, smul_eq_mul]
    have hc : Real.exp (-d * b) * Real.exp (d * b) = 1 := by
      rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
    have hn := mul_nonneg (mul_nonneg (Real.exp_pos (-d * b)).le (inv_nonneg.2 hd.le))
      (Real.exp_pos (d * τ u)).le
    rw [one_div]
    nlinarith only [congrArg (fun t => d⁻¹ * t) hc, hn]
  have hcoef : 0 ≤ L * Lᵧ / ρ := div_nonneg (mul_nonneg hL hLᵧ) hρ.le
  have hb : Real.exp (c * b) * |x.1 u b 0 * x.2.1 u b 1| ≤ H + L * Lᵧ * B / (ρ * d) := by
    change _ ≤ _ + L * Lᵧ / ρ *
      (∫ t in (τ u : ℝ)..b, Real.exp (-d * ((b : ℝ) - t)) * B) at hh
    rw [intervalIntegral.integral_mul_const] at hh
    calc
      _ ≤ H + L * Lᵧ / ρ * (1 / d * B) := hh.trans (add_le_add hθ
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkernel hB) hcoef))
      _ = _ := by ring
  rw [abs_mul, abs_of_pos (hρ.trans_le (hr u ⟨hzu, le_rfl⟩))] at hb
  have hrad := mul_le_mul_of_nonneg_right (hr u ⟨hzu, le_rfl⟩)
    (mul_nonneg (Real.exp_pos (c * b)).le (abs_nonneg (x.2.1 u b 1)))
  have hfinal : (Real.exp (c * b) * |x.2.1 u b 1|) * ρ ≤ H + L * Lᵧ * B / (ρ * d) := by
    nlinarith only [hb, hrad]
  exact ((le_div_iff₀ hρ).2 hfinal).trans_eq (by dsimp only [d]; field_simp)

end CauchyHorizon
