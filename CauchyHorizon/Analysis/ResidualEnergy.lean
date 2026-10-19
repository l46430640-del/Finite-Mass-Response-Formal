import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith

/-! The two scalar residuals have finite energy controlled by the envelope and its derivative. -/

open MeasureTheory

namespace CauchyHorizon

theorem residual_square_le {a b c H D ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (he : |a| + |b| ≤ ε) (hc : |c| ≤ C) :
    (a * H) ^ 2 + (b * H - c * D) ^ 2 ≤ 2 * ε ^ 2 * H ^ 2 + 2 * C ^ 2 * D ^ 2 := by
  have hab := (sq_le_sq₀ (add_nonneg (abs_nonneg a) (abs_nonneg b)) hε).2 he
  have hcsq : c ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg c) hC).2 hc
  rw [add_sq, sq_abs, sq_abs] at hab
  have hcoeff : a ^ 2 + 2 * b ^ 2 ≤ 2 * ε ^ 2 := by
    nlinarith only [hab, sq_nonneg a, mul_nonneg (abs_nonneg a) (abs_nonneg b)]
  have h₁ := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg H)
  have h₂ := mul_le_mul_of_nonneg_right hcsq (sq_nonneg D)
  nlinarith only [h₁, h₂, sq_nonneg (b * H + c * D)]

theorem residual_energy_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b c H D : α → ℝ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) (hc : AEStronglyMeasurable c μ)
    (hH : MemLp H 2 μ) (hD : MemLp D 2 μ)
    (he : ∀ᵐ t ∂μ, |a t| + |b t| ≤ ε) (hbound : ∀ᵐ t ∂μ, |c t| ≤ C) :
    MemLp (fun t => a t * H t) 2 μ ∧ MemLp (fun t => b t * H t - c t * D t) 2 μ ∧
      (∫ t, (a t * H t) ^ 2 + (b t * H t - c t * D t) ^ 2 ∂μ) ≤
        2 * ε ^ 2 * (∫ t, H t ^ 2 ∂μ) + 2 * C ^ 2 * (∫ t, D t ^ 2 ∂μ) := by
  have hHi := (memLp_two_iff_integrable_sq hH.aestronglyMeasurable).1 hH
  have hDi := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).1 hD
  have hsource : ∀ᵐ t ∂μ, (a t * H t) ^ 2 + (b t * H t - c t * D t) ^ 2 ≤
      2 * ε ^ 2 * H t ^ 2 + 2 * C ^ 2 * D t ^ 2 := by
    filter_upwards [he, hbound] with t ht hct
    exact residual_square_le hε hC ht hct
  have hS₁ := ha.mul hH.aestronglyMeasurable
  have hS₂ := (hb.mul hH.aestronglyMeasurable).sub (hc.mul hD.aestronglyMeasurable)
  have hmajor := (hHi.const_mul (2 * ε ^ 2)).add (hDi.const_mul (2 * C ^ 2))
  have hsum : Integrable (fun t => (a t * H t) ^ 2 + (b t * H t - c t * D t) ^ 2) μ := by
    apply hmajor.mono' ((hS₁.pow 2).add (hS₂.pow 2))
    filter_upwards [hsource] with t ht
    change ‖(a t * H t) ^ 2 + (b t * H t - c t * D t) ^ 2‖ ≤ _
    simpa only [Real.norm_eq_abs, Pi.add_apply,
      abs_of_nonneg (add_nonneg (sq_nonneg (a t * H t)) (sq_nonneg (b t * H t - c t * D t)))] using ht
  have h₁i : Integrable (fun t => (a t * H t) ^ 2) μ := by
    apply hsum.mono' (hS₁.pow 2)
    filter_upwards [] with t
    change ‖(a t * H t) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a t * H t))]
    exact le_add_of_nonneg_right (sq_nonneg (b t * H t - c t * D t))
  have h₂i : Integrable (fun t => (b t * H t - c t * D t) ^ 2) μ := by
    apply hsum.mono' (hS₂.pow 2)
    filter_upwards [] with t
    change ‖(b t * H t - c t * D t) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (b t * H t - c t * D t))]
    exact le_add_of_nonneg_left (sq_nonneg (a t * H t))
  refine ⟨(memLp_two_iff_integrable_sq hS₁).2 h₁i, (memLp_two_iff_integrable_sq hS₂).2 h₂i, ?_⟩
  have hh := integral_mono_ae hsum hmajor hsource
  simp only [Pi.add_apply, integral_add (hHi.const_mul _) (hDi.const_mul _), integral_const_mul] at hh
  exact hh

end CauchyHorizon
