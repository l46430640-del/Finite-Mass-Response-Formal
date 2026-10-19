import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Order.MonotoneConvergence

/-! Scalar monotonicity for the locally Lipschitz causal-curve convention. -/

open Set MeasureTheory Filter
open scoped Topology

namespace CauchyHorizon

theorem monotoneOn_Iic_of_locallyLipschitz_ae_deriv_nonneg {f : ℝ → ℝ}
    (hf : LocallyLipschitzOn (Iic 0) f)
    (hd : ∀ᵐ t ∂volume.restrict (Iio (0 : ℝ)), 0 ≤ deriv f t) :
    MonotoneOn f (Iic 0) := by
  intro a ha b hb hab
  have hsub : Icc a b ⊆ Iic (0 : ℝ) := fun _ ht => ht.2.trans hb
  obtain ⟨K, hK⟩ := (hf.mono hsub).exists_lipschitzOnWith_of_compact isCompact_Icc
  have hKu : LipschitzOnWith K f (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hK
  have hac := hKu.absolutelyContinuousOnInterval
  rw [restrict_Iio_eq_restrict_Iic] at hd
  have hn := intervalIntegral.integral_nonneg_of_ae_restrict hab
    (ae_mono (Measure.restrict_mono hsub le_rfl) hd)
  rw [hac.integral_deriv_eq_sub] at hn
  exact sub_nonneg.mp hn

theorem exists_past_limit_of_monotoneOn {f : ℝ → ℝ}
    (hf : MonotoneOn f (Iic 0)) {b : ℝ} (hb : ∀ t ≤ 0, b ≤ f t) :
    ∃ l : ℝ, Tendsto f atBot (𝓝 l) := by
  let g : ℝ → ℝ := fun t => f (min t 0)
  have hg : Monotone g := by
    intro x y h
    exact hf (show min x 0 ∈ Iic 0 from min_le_right x 0)
      (show min y 0 ∈ Iic 0 from min_le_right y 0) (min_le_min_right 0 h)
  have hgb : BddBelow (range g) := ⟨b, by
    rintro _ ⟨t, rfl⟩
    exact hb _ (min_le_right _ _)⟩
  refine ⟨⨅ t, g t, (tendsto_atBot_ciInf hg hgb).congr' ?_⟩
  filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
  simp [g, min_eq_left ht]

end CauchyHorizon
