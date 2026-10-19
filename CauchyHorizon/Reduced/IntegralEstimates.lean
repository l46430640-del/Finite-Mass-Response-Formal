import CauchyHorizon.Reduced.IntegralMap

/-! Uniform estimates for the actual characteristic map on a positive-radius range. -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CauchyHorizon

theorem wave_coefficients_control {lo hi : WaveVector × WaveVector}
    (hr : 0 < lo.1 0) (e Λ : ℝ) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun p : WaveVector × WaveVector =>
      (wavePotential e Λ p.1, waveLinear p.1 p.2)) (Icc lo.1 hi.1 ×ˢ Icc lo.2 hi.2) ∧
      ∀ p ∈ Icc lo.1 hi.1 ×ˢ Icc lo.2 hi.2,
        ‖(wavePotential e Λ p.1, waveLinear p.1 p.2)‖ ≤ C := by
  obtain ⟨L, hL⟩ := wave_coefficients_lipschitz (hi := hi) hr e Λ
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hL.continuousOn
  refine ⟨max L (Real.toNNReal K), hL.weaken (le_max_left _ _), ?_⟩
  intro p hp
  exact (hK p hp).trans ((Real.le_coe_toNNReal K).trans (by exact_mod_cast le_max_right L (Real.toNNReal K)))

variable {U V : ℝ}

def waveRange (lo hi : WaveVector × WaveVector) (x : WaveState U V) : Prop :=
  ∀ u v, (x.1 u v, x.2.1 u v) ∈ Icc lo.1 hi.1 ×ˢ Icc lo.2 hi.2

theorem waveRange_radius {lo hi : WaveVector × WaveVector} (hr : 0 < lo.1 0)
    {x : WaveState U V} (hx : waveRange lo hi x) : ∀ u v, x.1 u v 0 ≠ 0 :=
  fun u v => (hr.trans_le ((hx u v).1.1 0)).ne'

theorem rectangleSource_difference_bound (hU : 0 ≤ U) (e Λ : ℝ)
    {lo hi : WaveVector × WaveVector} {C : ℝ≥0}
    (hL : LipschitzOnWith C (fun p : WaveVector × WaveVector =>
      (wavePotential e Λ p.1, waveLinear p.1 p.2)) (Icc lo.1 hi.1 ×ˢ Icc lo.2 hi.2))
    (hC : ∀ p ∈ Icc lo.1 hi.1 ×ˢ Icc lo.2 hi.2,
      ‖(wavePotential e Λ p.1, waveLinear p.1 p.2)‖ ≤ C)
    (x y : WaveState U V) (hx : ∀ u v, x.1 u v 0 ≠ 0) (hy : ∀ u v, y.1 u v 0 ≠ 0)
    (hxr : waveRange lo hi x) (hyr : waveRange lo hi y) :
    ‖rectangleSource hU e Λ x hx - rectangleSource hU e Λ y hy‖ ≤
      C * (Real.sqrt U + ‖x.2.2‖ + 1) * ‖x - y‖ := by
  have hd (u : Icc 0 U) (v : Icc 0 V) :
      ‖(x.1 u v, x.2.1 u v) - (y.1 u v, y.2.1 u v)‖ ≤ ‖x - y‖ := by
    apply norm_prod_le_iff.2
    constructor
    · exact (((x.1 - y.1) u).norm_coe_le_norm v).trans
        (((x.1 - y.1).norm_coe_le_norm u).trans (norm_fst_le (x - y)))
    · exact (((x.2.1 - y.2.1) u).norm_coe_le_norm v).trans
        (((x.2.1 - y.2.1).norm_coe_le_norm u).trans
          ((norm_fst_le (x.2 - y.2)).trans (norm_snd_le (x - y))))
  have hcoeff (u : Icc 0 U) (v : Icc 0 V) :
      ‖(wavePotential e Λ (x.1 u v), waveLinear (x.1 u v) (x.2.1 u v)) -
        (wavePotential e Λ (y.1 u v), waveLinear (y.1 u v) (y.2.1 u v))‖ ≤ C * ‖x - y‖ := by
    have h := hL.dist_le_mul _ (hxr u v) _ (hyr u v)
    simp only [dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hd u v) C.2)
  have hG : ‖rectanglePotential hU e Λ x.1 hx - rectanglePotential hU e Λ y.1 hy‖ ≤
      Real.sqrt U * (C * ‖x - y‖) := by
    unfold rectanglePotential
    rw [← map_sub]
    refine (intervalToL2_norm_le hU _).trans ?_
    rw [sub_zero]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg U)
    apply (ContinuousMap.norm_le _ (mul_nonneg C.2 (norm_nonneg (x - y)))).2
    intro u
    apply (ContinuousMap.norm_le _ (mul_nonneg C.2 (norm_nonneg (x - y)))).2
    intro v
    exact (norm_fst_le _).trans (hcoeff u v)
  have hA : ‖rectangleOperator hU x.1 x.2.1 hx - rectangleOperator hU y.1 y.2.1 hy‖ ≤
      C * ‖x - y‖ := by
    unfold rectangleOperator
    rw [← map_sub, ← map_sub]
    refine (intervalToLinf_norm_le hU _).trans ?_
    apply (ContinuousMap.norm_le _ (mul_nonneg C.2 (norm_nonneg (x - y)))).2
    intro u
    refine (pointwiseOperator_norm_le _).trans ?_
    apply (ContinuousMap.norm_le _ (mul_nonneg C.2 (norm_nonneg (x - y)))).2
    intro v
    exact (norm_snd_le _).trans (hcoeff u v)
  have hB : ‖rectangleOperator hU y.1 y.2.1 hy‖ ≤ C := by
    unfold rectangleOperator
    refine (intervalToLinf_norm_le hU _).trans ?_
    apply (ContinuousMap.norm_le _ C.2).2
    intro u
    refine (pointwiseOperator_norm_le _).trans ?_
    apply (ContinuousMap.norm_le _ C.2).2
    intro v
    exact (norm_snd_le _).trans (hC _ (hyr u v))
  have hdu : ‖x.2.2 - y.2.2‖ ≤ ‖x - y‖ :=
    (norm_snd_le (x.2 - y.2)).trans (norm_snd_le (x - y))
  refine (affineMixedSource_difference_bound _ _ _ _ _ _).trans ?_
  calc
    _ ≤ Real.sqrt U * (C * ‖x - y‖) + (C * ‖x - y‖) * ‖x.2.2‖ + C * ‖x - y‖ :=
      add_le_add (add_le_add hG (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
        (mul_le_mul hB hdu (norm_nonneg _) C.2)
    _ = _ := by ring

theorem waveIteration_local_bound {lo hi : WaveVector × WaveVector}
    (hr : 0 < lo.1 0) (e Λ M : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ 1 →
      ∀ (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
        (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x y : WaveState U V)
        (hx : waveRange lo hi x) (hy : waveRange lo hi y), ‖x.2.2‖ ≤ M →
      ‖waveIteration hU hV e Λ zIn vOut uIn x (waveRange_radius hr hx) -
        waveIteration hU hV e Λ zIn vOut uIn y (waveRange_radius hr hy)‖ ≤
        B * (Real.sqrt U + V) * ‖x - y‖ := by
  obtain ⟨C, hL, hC⟩ := wave_coefficients_control (hi := hi) hr e Λ
  let B : ℝ := max 1 (C * (M + 2))
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  refine ⟨B, hB, ?_⟩
  intro U V hU hV hU1 zIn vOut uIn x y hx hy hxu
  have hsU : Real.sqrt U ≤ 1 := (Real.sqrt_le_one).2 hU1
  have hF := rectangleSource_difference_bound hU e Λ hL hC x y
    (waveRange_radius hr hx) (waveRange_radius hr hy) hx hy
  have hFB : ‖rectangleSource hU e Λ x (waveRange_radius hr hx) -
      rectangleSource hU e Λ y (waveRange_radius hr hy)‖ ≤ B * ‖x - y‖ := by
    refine hF.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg (x - y)))
    exact (mul_le_mul_of_nonneg_left (by linarith : Real.sqrt U + ‖x.2.2‖ + 1 ≤ M + 2) C.2).trans (le_max_right _ _)
  obtain ⟨hz, hv, hu⟩ := waveIteration_difference hU hV e Λ zIn vOut uIn x y
    (waveRange_radius hr hx) (waveRange_radius hr hy)
  apply norm_prod_le_iff.2
  refine ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · refine hz.trans ?_
    have hdv : ‖x.2.1 - y.2.1‖ ≤ ‖x - y‖ :=
      (norm_fst_le (x.2 - y.2)).trans (norm_snd_le (x - y))
    calc
      _ ≤ V * ‖x - y‖ := mul_le_mul_of_nonneg_left hdv hV
      _ ≤ B * (Real.sqrt U + V) * ‖x - y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg (x - y))
        nlinarith [Real.sqrt_nonneg U]
  · refine hv.trans ((mul_le_mul_of_nonneg_left hFB (Real.sqrt_nonneg U)).trans ?_)
    nlinarith [norm_nonneg (x - y), mul_nonneg hV (mul_nonneg hB0 (norm_nonneg (x - y)))]
  · refine hu.trans ((mul_le_mul_of_nonneg_left hFB hV).trans ?_)
    nlinarith [norm_nonneg (x - y), mul_nonneg (Real.sqrt_nonneg U) (mul_nonneg hB0 (norm_nonneg (x - y)))]

end CauchyHorizon
