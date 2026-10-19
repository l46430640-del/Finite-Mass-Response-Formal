import CauchyHorizon.Analysis.LogarithmicProfile

/-! A logarithmic support escaping to the right leaves every positive incoming interval. -/

open Set Filter

namespace CauchyHorizon

theorem logarithmicIncoming_eventually_zero {ι : Type*} {l : Filter ι}
    (b : ℝ) {ℓ m : ι → ℝ} {P : ι → ℝ → ℝ}
    (hfront : Tendsto (fun i => m i - ℓ i) l atTop)
    (hsupport : ∀ i t, t ≤ m i → P i t = 0) :
    (∀ η : ℝ, 0 < η → ∀ᶠ i in l, ∀ u ∈ Ici η, logarithmicIncoming b (ℓ i) (P i) u = 0) ∧
      ∀ T : ℝ, ∀ᶠ i in l, ∀ t ≤ T, P i (ℓ i + t) = 0 := by
  constructor
  · intro η hη
    filter_upwards [(tendsto_atTop.1 hfront) (-Real.log η)] with i hi u hu
    have hlog := Real.log_le_log hη hu
    have hz := hsupport i (ℓ i - Real.log u) (by linarith only [hi, hlog])
    simp only [logarithmicIncoming, hz, mul_zero]
  · intro T
    filter_upwards [(tendsto_atTop.1 hfront) T] with i hi t ht
    exact hsupport i (ℓ i + t) (by linarith only [hi, ht])

end CauchyHorizon
