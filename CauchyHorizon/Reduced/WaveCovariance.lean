import CauchyHorizon.Reduced.WaveSource
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The reduced source transforms correctly under lapse normalization and exchange of null coordinates. -/

namespace CauchyHorizon

theorem waveSource_regular_swap (e Λ : ℝ) (z p q : WaveVector) {a : ℝ} (ha : 0 < a) (β : ℝ) :
    waveSource e Λ (z - ![0, 0, Real.log a]) (a⁻¹ • (q - ![0, 0, β])) p =
      a⁻¹ • waveSource e Λ z p q := by
  ext i
  fin_cases i <;>
    simp [waveSource, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.exp_sub, Real.exp_log ha,
      div_eq_mul_inv, Matrix.vecHead, Matrix.vecTail] <;> ring

end CauchyHorizon
