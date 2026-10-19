import CauchyHorizon.Reduced.WeakWave
import CauchyHorizon.Analysis.RectangleDistribution

/-! Every smooth compactly supported test in the open rectangle is an admissible wave test. -/

open MeasureTheory Set
open scoped Distributions

namespace CauchyHorizon

noncomputable def WaveTest.ofTestFunction {U V : ℝ}
    (ψ : 𝓓(openRectangle U V, ℝ)) : WaveTest U V := by
  let ψu : 𝓓(openRectangle U V, ℝ) := TestFunction.lineDerivCLM ℝ (1, 0) ψ
  let ψuv : 𝓓(openRectangle U V, ℝ) := TestFunction.lineDerivCLM ℝ (0, 1) ψu
  refine {
    val := fun u v => ψ (u, v)
    du := fun u v => ψu (u, v)
    duv := fun u v => ψuv (u, v)
    continuous_val := ψ.continuous
    continuous_du := ψu.continuous
    continuous_duv := ψuv.continuous
    smooth_u := ?_
    deriv_u := ?_
    deriv_du_v := ?_
    boundary_u := ?_
    boundary_du_v := ?_ }
  · intro v
    exact (ψ.contDiff.of_le (by simp)).comp (contDiff_id.prodMk contDiff_const)
  · intro u v
    dsimp only [ψu]
    rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le ψ le_top]
    exact ((ψ.contDiff.differentiable (by simp)) (u, v)).hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))
  · intro u v
    dsimp only [ψuv]
    rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le ψu le_top]
    exact ((ψu.contDiff.differentiable (by simp)) (u, v)).hasFDerivAt.comp_hasDerivAt v
      ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))
  · intro v
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (ψ.tsupport_subset h).1.1),
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl U) (ψ.tsupport_subset h).1.2)⟩
  · intro u
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (ψu.tsupport_subset h).2.1),
      image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl V) (ψu.tsupport_subset h).2.2)⟩

end CauchyHorizon
