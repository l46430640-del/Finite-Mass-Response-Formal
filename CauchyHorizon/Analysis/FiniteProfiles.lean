import CauchyHorizon.Analysis.PrimitiveEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Finite linear combinations retain their full quadratic energy and satisfy Minkowski bounds. -/

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction ENNReal

namespace CauchyHorizon

theorem finite_sum_lp_norm {ι α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (c : ι → ℝ) (f : ι → α → ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp (fun x => ∑ i ∈ s, c i * f i x) p μ ∧
      (eLpNorm (fun x => ∑ i ∈ s, c i * f i x) p μ).toReal ≤
        ∑ i ∈ s, |c i| * (eLpNorm (f i) p μ).toReal := by
  have hm : MemLp (fun x => ∑ i ∈ s, c i * f i x) p μ :=
    memLp_finsetSum s (fun i hi => (hf i hi).const_smul (c i))
  refine ⟨hm, ?_⟩
  rw [toReal_eLpNorm hm.aestronglyMeasurable]
  have hh := lpNorm_sum_le (fun i hi => (hf i hi).const_smul (c i)) hp
  calc
    _ ≤ ∑ i ∈ s, |c i| * lpNorm (f i) p μ := by
      have he : (fun x => ∑ i ∈ s, c i * f i x) = ∑ i ∈ s, c i • f i := by
        ext x
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [he]
      simpa only [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs] using hh
    _ = _ := Finset.sum_congr rfl (fun i hi => by
      rw [toReal_eLpNorm (hf i hi).aestronglyMeasurable])

theorem finite_sum_squared_integral {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (f : ι → ℝ →ᵇ ℝ)
    (hf : ∀ i ∈ s, Integrable (fun x => f i x ^ 2)) :
    Integrable (fun x => (∑ i ∈ s, c i * f i x) ^ 2) ∧
      (∫ x, (∑ i ∈ s, c i * f i x) ^ 2) ≤
        (∑ i ∈ s, |c i| * Real.sqrt (∫ x, f i x ^ 2)) ^ 2 := by
  have hm i hi : MemLp (f i) 2 volume :=
    (memLp_two_iff_integrable_sq (f i).continuous.aestronglyMeasurable).2 (hf i hi)
  have hnorm {g : ℝ → ℝ} (hg : AEStronglyMeasurable g volume) :
      (eLpNorm g 2 volume).toReal = Real.sqrt (∫ x, g x ^ 2) := by
    rw [toReal_eLpNorm hg, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hg]
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs,
      ← one_div, ← Real.sqrt_eq_rpow]
  obtain ⟨hsm, hbound⟩ := finite_sum_lp_norm s c (fun i => f i) (by norm_num) hm
  have hi := (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).1 hsm
  refine ⟨hi, ?_⟩
  rw [hnorm hsm.aestronglyMeasurable] at hbound
  simp_rw [hnorm (f _).continuous.aestronglyMeasurable] at hbound
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hbound 2
  rwa [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hh

end CauchyHorizon
