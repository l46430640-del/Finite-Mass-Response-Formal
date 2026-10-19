import CauchyHorizon.Analysis.PrimitiveCompatibility
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Absolute continuity of Banach-valued primitives and their smooth compositions. -/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace CauchyHorizon

theorem absolutelyContinuous_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : ℝ → Y} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b, dist (f s) (f t) ≤ K * dist (g s) (g t)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hg (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hs := hd E hE hlen
  calc
    _ ≤ (K + 1) * ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      exact (h _ (hE.1 i hi).1 _ (hE.1 i hi).2).trans
        (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg)
    _ < (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left hs (by positivity)
    _ = ε := by field_simp

theorem horizontalPrimitive_absolutelyContinuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    (f : Lp E 2 (volume.restrict (Icc a b))) (c : E) :
    AbsolutelyContinuousOnInterval
      (fun t => c + intervalExtension hab (horizontalPrimitive hab f) t) a b := by
  have hf := l2_intervalIntegrable hab f
  apply absolutelyContinuous_of_dist_le
    (hf.norm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc) (K := 1) zero_le_one
  intro s hs t ht
  have hs' : s ∈ Icc a b := by simpa only [uIcc_of_le hab] using hs
  have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
  simp only [intervalExtension_apply, projIcc_of_mem hab hs', projIcc_of_mem hab ht',
    one_mul, dist_eq_norm, add_sub_add_left_eq_sub]
  change ‖(∫ x in a..s, f x) - ∫ x in a..t, f x‖ ≤
    ‖(∫ x in a..s, ‖f x‖) - ∫ x in a..t, ‖f x‖‖
  rw [intervalIntegral.integral_interval_sub_left (hf.mono_set (uIcc_subset_uIcc_left hs))
      (hf.mono_set (uIcc_subset_uIcc_left ht)),
    intervalIntegral.integral_interval_sub_left (hf.norm.mono_set (uIcc_subset_uIcc_left hs))
      (hf.norm.mono_set (uIcc_subset_uIcc_left ht)), Real.norm_eq_abs]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

theorem absolutelyContinuous_comp_contDiffAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E} {g : E → F} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ∀ x ∈ f '' uIcc a b, ContDiffAt ℝ 1 g x) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  have hc : IsCompact (f '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hf.continuousOn
  have hl : LocallyLipschitzOn (f '' uIcc a b) g := by
    intro x hx
    obtain ⟨K, s, hs, hgs⟩ := (hg x hx).exists_lipschitzOnWith
    exact ⟨K, s, nhdsWithin_le_nhds hs, hgs⟩
  obtain ⟨K, hK⟩ := hl.exists_lipschitzOnWith_of_compact hc
  exact absolutelyContinuous_of_dist_le hf K.coe_nonneg
    (fun s hs t ht => hK.dist_le_mul _ (mem_image_of_mem f hs) _ (mem_image_of_mem f ht))

end CauchyHorizon
