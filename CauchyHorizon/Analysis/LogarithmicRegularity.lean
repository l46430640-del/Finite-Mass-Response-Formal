import CauchyHorizon.Analysis.LogarithmicProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Smooth profiles give the positive-radius regularity needed by scalar energy transport. -/

open Set

namespace CauchyHorizon

theorem logarithmicIncoming_contDiff {P : ℝ → ℝ} (hP : ContDiff ℝ 1 P) (b ℓ : ℝ) :
    ContDiffOn ℝ 1 (logarithmicIncoming b ℓ P) (Ioi 0) := by
  exact (contDiffOn_const.mul (contDiffOn_id.rpow_const_of_ne (fun _ hu => hu.ne'))).mul
    (hP.comp_contDiffOn (contDiffOn_const.sub (contDiffOn_id.log (fun _ hu => hu.ne'))))

end CauchyHorizon
