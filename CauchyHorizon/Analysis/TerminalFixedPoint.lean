import CauchyHorizon.Analysis.TerminalIntegral
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Linarith

/-! A terminal nonlinear equation on a small closed ball of bounded continuous functions. -/

open MeasureTheory Set
open scoped Topology BoundedContinuousFunction NNReal

namespace CauchyHorizon

structure TerminalSource where
  rate : ℝ
  radius : ℝ
  rate_pos : 0 < rate
  radius_pos : 0 < radius
  source : ℝ → ℝ → ℝ
  continuous : ∀ Y : ℝ →ᵇ ℝ, ‖Y‖ ≤ radius → Continuous (fun t => source t (Y t))
  difference : ∀ t x y, ‖x‖ ≤ radius → ‖y‖ ≤ radius →
    ‖source t x - source t y‖ ≤ rate / 2 * ‖x - y‖
  zero_bound : ∀ t, ‖source t 0‖ ≤ rate * radius / 2

namespace TerminalSource

variable (S : TerminalSource)

abbrev Ball := Metric.closedBall (0 : ℝ →ᵇ ℝ) S.radius

theorem ball_norm_le (Y : S.Ball) : ‖(Y : ℝ →ᵇ ℝ)‖ ≤ S.radius := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using Y.property

noncomputable def onCurve (Y : S.Ball) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => S.source t (Y.val t))
    (S.continuous Y.val (S.ball_norm_le Y)) (S.rate * S.radius) (fun t => by
      have hy := (Y.val.norm_coe_le_norm t).trans (S.ball_norm_le Y)
      have hd := S.difference t (Y.val t) 0 hy (by simpa using S.radius_pos.le)
      have hz := S.zero_bound t
      have hn := norm_le_insert (S.source t 0) (S.source t (Y.val t))
      rw [norm_sub_rev] at hn
      simp only [sub_zero] at hd
      nlinarith [mul_le_mul_of_nonneg_left hy S.rate_pos.le])

theorem onCurve_norm_le (Y : S.Ball) : ‖S.onCurve Y‖ ≤ S.rate * S.radius :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg S.rate_pos.le S.radius_pos.le) _

noncomputable def map (Y : S.Ball) : S.Ball :=
  ⟨terminalGreen S.rate_pos (S.onCurve Y), by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      _ ≤ ‖S.onCurve Y‖ / S.rate := terminalGreen_norm_le S.rate_pos _
      _ ≤ (S.rate * S.radius) / S.rate :=
        div_le_div_of_nonneg_right (S.onCurve_norm_le Y) S.rate_pos.le
      _ = S.radius := mul_div_cancel_left₀ _ S.rate_pos.ne'⟩

theorem map_contracting : ContractingWith (1 / 2) S.map := by
  have hc := S.rate_pos
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun Y Z => ?_⟩
  have hbound : ‖S.onCurve Y - S.onCurve Z‖ ≤ S.rate / 2 * dist Y Z := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro t
    exact (S.difference t (Y.val t) (Z.val t)
      ((Y.val.norm_coe_le_norm t).trans (S.ball_norm_le Y))
      ((Z.val.norm_coe_le_norm t).trans (S.ball_norm_le Z))).trans
        (mul_le_mul_of_nonneg_left (by
          simpa! only [Subtype.dist_eq, dist_eq_norm, BoundedContinuousFunction.sub_apply]
            using (Y.val - Z.val).norm_coe_le_norm t)
          (by positivity))
  change dist (terminalGreen S.rate_pos (S.onCurve Y))
    (terminalGreen S.rate_pos (S.onCurve Z)) ≤ (1 / 2 : ℝ≥0) * dist Y Z
  rw [dist_eq_norm, ← terminalGreen_sub]
  calc
    _ ≤ ‖S.onCurve Y - S.onCurve Z‖ / S.rate := terminalGreen_norm_le S.rate_pos _
    _ ≤ (S.rate / 2 * dist Y Z) / S.rate :=
      div_le_div_of_nonneg_right hbound S.rate_pos.le
    _ = _ := by norm_num; field_simp

theorem exists_solution : ∃ Y : ℝ →ᵇ ℝ, ‖Y‖ ≤ S.radius ∧
    (∀ t, HasDerivAt Y (S.rate * Y t - S.source t (Y t)) t) ∧
    (∀ t, Y t = terminalIntegral S.rate (fun w => S.source w (Y w)) t) := by
  let : CompleteSpace S.Ball := Metric.isClosed_closedBall.isComplete.completeSpace_coe
  let : Nonempty S.Ball := ⟨⟨0, by simp [Ball, S.radius_pos.le]⟩⟩
  let Y := S.map_contracting.fixedPoint S.map
  have hfix := S.map_contracting.fixedPoint_isFixedPt
  have heq : (Y : ℝ →ᵇ ℝ) = terminalGreen S.rate_pos (S.onCurve Y) :=
    (congrArg Subtype.val hfix).symm
  refine ⟨Y.val, S.ball_norm_le Y, ?_, ?_⟩
  · intro t
    have hd := terminalIntegral_hasDerivAt S.rate_pos (S.onCurve Y) t
    change HasDerivAt (terminalGreen S.rate_pos (S.onCurve Y))
      (S.rate * terminalGreen S.rate_pos (S.onCurve Y) t - S.source t (Y.val t)) t at hd
    rw [← heq] at hd
    exact hd
  · intro t
    exact congrArg (fun f : ℝ →ᵇ ℝ => f t) heq

theorem integral_solution_unique {Y Z : ℝ →ᵇ ℝ} (hY : ‖Y‖ ≤ S.radius) (hZ : ‖Z‖ ≤ S.radius)
    (hYi : ∀ t, Y t = terminalIntegral S.rate (fun w => S.source w (Y w)) t)
    (hZi : ∀ t, Z t = terminalIntegral S.rate (fun w => S.source w (Z w)) t) : Y = Z := by
  let y : S.Ball := ⟨Y, by simpa only [Metric.mem_closedBall, dist_zero_right] using hY⟩
  let z : S.Ball := ⟨Z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hZ⟩
  have hy : Function.IsFixedPt S.map y := by
    apply Subtype.ext
    ext t
    exact (hYi t).symm
  have hz : Function.IsFixedPt S.map z := by
    apply Subtype.ext
    ext t
    exact (hZi t).symm
  exact congrArg Subtype.val (S.map_contracting.fixedPoint_unique' hy hz)

end TerminalSource
end CauchyHorizon
