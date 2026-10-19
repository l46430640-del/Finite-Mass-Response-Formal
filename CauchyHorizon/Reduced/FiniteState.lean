import CauchyHorizon.Reduced.IntegralRegularity
import CauchyHorizon.Analysis.L2Majorant

/-! The fixed-point identities turn a source bound into quantitative state bounds. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.finite_state_bound {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {S : ℝ} (hsource : ‖rectangleSource hU e Λ x hr‖ ≤ S) :
    ‖x.2.1‖ ≤ ‖vOut‖ + Real.sqrt U * S ∧
      ‖x.2.2‖ ≤ ‖uIn‖ + V * S ∧
      ‖x.1‖ ≤ ‖zIn‖ + V * (‖vOut‖ + Real.sqrt U * S) := by
  let F := rectangleSource hU e Λ x hr
  have hv : ContinuousMap.const _ vOut + horizontalPrimitive hU F = x.2.1 :=
    congrArg (fun y : WaveState U V => y.2.1) hx.choose_spec
  have hu : incomingTransverse uIn + verticalPrimitive hV F = x.2.2 :=
    congrArg (fun y : WaveState U V => y.2.2) hx.choose_spec
  have hz : incomingField zIn + longitudinalIntegral hV x.2.1 = x.1 := congrArg Prod.fst hx.choose_spec
  have hvb : ‖x.2.1‖ ≤ ‖vOut‖ + Real.sqrt U * S := by
    rw [← hv]
    refine (norm_add_le (ContinuousMap.const (Icc 0 U) vOut) (horizontalPrimitive hU F)).trans (add_le_add ?_ ?_)
    · exact (ContinuousMap.norm_le _ (norm_nonneg vOut)).2 (fun _ => le_rfl)
    · have hh := horizontalPrimitive_norm_le hU F
      rw [sub_zero] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hsource (Real.sqrt_nonneg U))
  refine ⟨hvb, ?_, ?_⟩
  · rw [← hu]
    refine (norm_add_le (incomingTransverse (V := V) uIn) (verticalPrimitive hV F)).trans
      (add_le_add (incomingTransverse_norm_le uIn) ?_)
    have hh := verticalPrimitive_norm_le hV F
    rw [sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hsource hV)
  · rw [← hz]
    refine (norm_add_le (incomingField (V := V) zIn) (longitudinalIntegral hV x.2.1)).trans (add_le_add ?_ ?_)
    · apply (ContinuousMap.norm_le _ (norm_nonneg zIn)).2
      intro u
      exact (ContinuousMap.norm_le _ (norm_nonneg zIn)).2 (fun _ => zIn.norm_coe_le_norm u)
    · exact (longitudinalIntegral_norm_le hV x.2.1).trans (mul_le_mul_of_nonneg_left hvb hV)

end CauchyHorizon
