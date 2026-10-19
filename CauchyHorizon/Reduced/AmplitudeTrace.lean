import CauchyHorizon.Reduced.BoundaryTrace
import Mathlib.Analysis.Calculus.MeanValue

/-! Exponentiation preserves compact incoming traces and quantitative tails. -/

open Set

namespace CauchyHorizon

noncomputable def waveAmplitude {K : Type*} [TopologicalSpace K] : C(C(K, WaveVector), C(K, ℝ)) :=
  ⟨(⟨fun z : WaveVector => Real.exp (z 2), by fun_prop⟩ : C(WaveVector, ℝ)).comp,
    ContinuousMap.continuous_postcomp _⟩

theorem waveAmplitude_renormalizedWaveRow_apply {U ε k : ℝ} (hε : 0 ≤ ε)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (T : Ici (0 : ℝ)) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U) :
    waveAmplitude (renormalizedWaveRow hε k X t) u =
      Real.exp (2 * k * t) * Real.exp ((X T).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htT⟩ 2) := by
  change Real.exp (renormalizedWaveRow hε k X t u 2) = _
  rw [renormalizedWaveRow_apply hε X hcompat T ht htT u 2]
  simp only [ite_true, Real.exp_add, mul_comm]

theorem waveAmplitude_norm_sub_le {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {f g : C(K, WaveVector)} {M : ℝ} (hM : 0 < M)
    (hf : ∀ u, waveAmplitude f u ≤ M) (hg : ∀ u, waveAmplitude g u ≤ M) :
    ‖waveAmplitude f - waveAmplitude g‖ ≤ M * ‖f - g‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hM.le (norm_nonneg _))).2
  intro u
  have hfu : f u 2 ≤ Real.log M := (Real.le_log_iff_exp_le hM).2 (hf u)
  have hgu : g u 2 ≤ Real.log M := (Real.le_log_iff_exp_le hM).2 (hg u)
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ht : t ∈ Iic (Real.log M)) => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (Real.exp_le_exp.2 ht).trans_eq (Real.exp_log hM))
    (convex_Iic (Real.log M)) hgu hfu
  have hc := (norm_le_pi_norm (f u - g u) 2).trans ((f - g).norm_coe_le_norm u)
  exact he.trans (mul_le_mul_of_nonneg_left hc hM.le)

end CauchyHorizon
