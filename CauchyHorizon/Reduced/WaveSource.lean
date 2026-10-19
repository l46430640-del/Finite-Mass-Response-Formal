import CauchyHorizon.Algebra
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The actual reduced wave source is affine in the rough transverse derivative. -/

open Set
open scoped NNReal

namespace CauchyHorizon

abbrev WaveVector := Fin 3 → ℝ

noncomputable def conformalPotential (r e : ℝ) : ℝ := 1 / (2 * r ^ 2) - e ^ 2 / r ^ 4

noncomputable def wavePotential (e Λ : ℝ) (z : WaveVector) : WaveVector :=
  ![Real.exp (z 2) * radialPotential (z 0) e Λ, 0,
    Real.exp (z 2) * conformalPotential (z 0) e]

noncomputable def waveEntry (i j : Fin 3) : WaveVector →L[ℝ] WaveVector :=
  ContinuousLinearMap.pi (fun k => if k = i then ContinuousLinearMap.proj j else 0)

noncomputable def waveLinear (z v : WaveVector) : WaveVector →L[ℝ] WaveVector :=
  (-v 0 / z 0) • waveEntry 0 0 + (-v 1 / z 0) • waveEntry 1 0 -
    (v 0 / z 0) • waveEntry 1 1 + (2 * v 0 / z 0 ^ 2) • waveEntry 2 0 -
    (2 * v 1) • waveEntry 2 1

noncomputable def waveSource (e Λ : ℝ) (z u v : WaveVector) : WaveVector :=
  ![Real.exp (z 2) * radialPotential (z 0) e Λ - u 0 * v 0 / z 0,
    -(u 0 * v 1 + v 0 * u 1) / z 0,
    -2 * u 1 * v 1 + Real.exp (z 2) * conformalPotential (z 0) e + 2 * u 0 * v 0 / z 0 ^ 2]

theorem waveSource_affine (e Λ : ℝ) (z u v : WaveVector) :
    waveSource e Λ z u v = wavePotential e Λ z + waveLinear z v u := by
  ext i
  fin_cases i <;> simp [waveSource, wavePotential, waveLinear, waveEntry,
    ContinuousLinearMap.proj_apply, smul_eq_mul] <;> ring

theorem wavePotential_contDiffAt {z : WaveVector} (hz : z 0 ≠ 0) (e Λ : ℝ) :
    ContDiffAt ℝ 1 (wavePotential e Λ) z := by
  apply contDiffAt_pi.2
  intro i
  fin_cases i <;> dsimp [wavePotential, radialPotential, conformalPotential] <;>
    fun_prop (disch := positivity)

theorem waveLinear_contDiffAt {p : WaveVector × WaveVector} (hp : p.1 0 ≠ 0) :
    ContDiffAt ℝ 1 (fun q : WaveVector × WaveVector => waveLinear q.1 q.2) p := by
  unfold waveLinear
  fun_prop (disch := positivity)

theorem wave_coefficients_lipschitz {lo hi : WaveVector × WaveVector}
    (hr : 0 < lo.1 0) (e Λ : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (fun p : WaveVector × WaveVector =>
      (wavePotential e Λ p.1, waveLinear p.1 p.2)) (Icc lo.1 hi.1 ×ˢ Icc lo.2 hi.2) := by
  have hc : ContDiffOn ℝ 1 (fun p : WaveVector × WaveVector =>
      (wavePotential e Λ p.1, waveLinear p.1 p.2)) (Icc lo.1 hi.1 ×ˢ Icc lo.2 hi.2) := by
    intro p hp
    have hp0 : p.1 0 ≠ 0 := (hr.trans_le (hp.1.1 0)).ne'
    exact (((wavePotential_contDiffAt hp0 e Λ).comp p contDiffAt_fst).prodMk
      (waveLinear_contDiffAt hp0)).contDiffWithinAt
  exact hc.exists_lipschitzOnWith (by norm_num) ((convex_Icc _ _).prod (convex_Icc _ _))
    (isCompact_Icc.prod isCompact_Icc)

theorem waveSource_difference_bound (e Λ : ℝ) (z z' u u' v v' : WaveVector) :
    ‖waveSource e Λ z u v - waveSource e Λ z' u' v'‖ ≤
      ‖wavePotential e Λ z - wavePotential e Λ z'‖ +
      ‖waveLinear z v - waveLinear z' v'‖ * ‖u‖ + ‖waveLinear z' v'‖ * ‖u - u'‖ := by
  rw [waveSource_affine, waveSource_affine]
  have he : wavePotential e Λ z + waveLinear z v u -
      (wavePotential e Λ z' + waveLinear z' v' u') =
      (wavePotential e Λ z - wavePotential e Λ z') +
      (waveLinear z v - waveLinear z' v') u + waveLinear z' v' (u - u') := by
    simp only [sub_apply, map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add_right ((waveLinear z v - waveLinear z' v').le_opNorm u) _))
    ((waveLinear z' v').le_opNorm (u - u')))

end CauchyHorizon
