import CauchyHorizon.Algebra
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.LinearCombination

/-! The four-root factorization follows from the three positive RN-dS roots. -/

namespace CauchyHorizon

structure Background where
  mass : ℝ
  charge : ℝ
  cosmological : ℝ
  inner : ℝ
  event : ℝ
  cosmologicalRadius : ℝ
  charge_ne : charge ≠ 0
  cosmological_pos : 0 < cosmological
  inner_pos : 0 < inner
  inner_lt_event : inner < event
  event_lt_cosmological : event < cosmologicalRadius
  root_inner : horizonFunction inner mass charge cosmological = 0
  root_event : horizonFunction event mass charge cosmological = 0
  root_cosmological : horizonFunction cosmologicalRadius mass charge cosmological = 0

theorem horizonFunction_mul_radius {r : ℝ} (hr : r ≠ 0) (M e Λ : ℝ) :
    horizonFunction r M e Λ * (3 * r ^ 2) =
      3 * r ^ 2 - 6 * M * r + 3 * e ^ 2 - Λ * r ^ 4 := by
  unfold horizonFunction
  field_simp
  ring

theorem horizon_roots_secant {l r M e Λ : ℝ} (hl : l ≠ 0) (hr : r ≠ 0)
    (hlr : l ≠ r) (hfl : horizonFunction l M e Λ = 0)
    (hfr : horizonFunction r M e Λ = 0) :
    6 * M = (l + r) * (3 - Λ * (l ^ 2 + r ^ 2)) := by
  have hpl := horizonFunction_mul_radius hl M e Λ
  have hpr := horizonFunction_mul_radius hr M e Λ
  rw [hfl, zero_mul] at hpl
  rw [hfr, zero_mul] at hpr
  have hmul : (r - l) * ((l + r) * (3 - Λ * (l ^ 2 + r ^ 2)) - 6 * M) = 0 := by
    linear_combination hpl - hpr
  exact (sub_eq_zero.1 ((mul_eq_zero.1 hmul).resolve_left (sub_ne_zero.2 hlr.symm))).symm

namespace Background

variable (B : Background)

noncomputable def F (r : ℝ) : ℝ := horizonFunction r B.mass B.charge B.cosmological

noncomputable def negativeRoot : ℝ := -(B.inner + B.event + B.cosmologicalRadius)

theorem event_pos : 0 < B.event := B.inner_pos.trans B.inner_lt_event

theorem cosmologicalRadius_pos : 0 < B.cosmologicalRadius :=
  B.event_pos.trans B.event_lt_cosmological

theorem negativeRoot_neg : B.negativeRoot < 0 := by
  unfold negativeRoot
  linarith [B.inner_pos, B.event_pos, B.cosmologicalRadius_pos]

theorem root_parameter_relations :
    B.cosmological * (B.inner ^ 2 + B.event ^ 2 + B.cosmologicalRadius ^ 2 +
      B.inner * B.event + B.inner * B.cosmologicalRadius + B.event * B.cosmologicalRadius) = 3 ∧
    6 * B.mass = B.cosmological * (B.inner + B.event + B.cosmologicalRadius) *
      (B.inner * B.event + B.inner * B.cosmologicalRadius + B.event * B.cosmologicalRadius) -
      B.cosmological * B.inner * B.event * B.cosmologicalRadius ∧
    3 * B.charge ^ 2 = B.cosmological * B.inner * B.event * B.cosmologicalRadius *
      (B.inner + B.event + B.cosmologicalRadius) := by
  have h₁ := horizon_roots_secant B.inner_pos.ne' B.event_pos.ne'
    B.inner_lt_event.ne B.root_inner B.root_event
  have h₂ := horizon_roots_secant B.inner_pos.ne' B.cosmologicalRadius_pos.ne'
    (B.inner_lt_event.trans B.event_lt_cosmological).ne B.root_inner B.root_cosmological
  have hp := horizonFunction_mul_radius B.inner_pos.ne' B.mass B.charge B.cosmological
  rw [B.root_inner, zero_mul] at hp
  have hmul : (B.cosmologicalRadius - B.event) *
      (B.cosmological * (B.inner ^ 2 + B.event ^ 2 + B.cosmologicalRadius ^ 2 +
      B.inner * B.event + B.inner * B.cosmologicalRadius + B.event * B.cosmologicalRadius) - 3) = 0 := by
    linear_combination h₂ - h₁
  have hΛ := sub_eq_zero.1 ((mul_eq_zero.1 hmul).resolve_left
    (sub_ne_zero.2 B.event_lt_cosmological.ne'))
  refine ⟨hΛ, ?_, ?_⟩
  · linear_combination h₁ - (B.inner + B.event) * hΛ
  · linear_combination -hp + B.inner * h₁ - B.inner * B.event * hΛ

theorem factorization {r : ℝ} (hr : r ≠ 0) :
    B.F r = -B.cosmological * (r - B.inner) * (r - B.event) *
      (r - B.cosmologicalRadius) * (r - B.negativeRoot) / (3 * r ^ 2) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ hr))).2
  rw [F, horizonFunction_mul_radius hr]
  obtain ⟨hΛ, hM, he⟩ := B.root_parameter_relations
  unfold negativeRoot
  linear_combination -(r ^ 2) * hΛ - r * hM + he

theorem F_neg {r : ℝ} (hr : r ∈ Set.Ioo B.inner B.event) : B.F r < 0 := by
  have hr0 := B.inner_pos.trans hr.1
  rw [B.factorization hr0.ne']
  apply div_neg_of_neg_of_pos _ (by positivity)
  have h₁ : 0 < r - B.inner := sub_pos.2 hr.1
  have h₂ : r - B.event < 0 := sub_neg.2 hr.2
  have h₃ : r - B.cosmologicalRadius < 0 := sub_neg.2 (hr.2.trans B.event_lt_cosmological)
  have h₄ : 0 < r - B.negativeRoot := sub_pos.2 (B.negativeRoot_neg.trans hr0)
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg
      (mul_neg_of_neg_of_pos (neg_neg_of_pos B.cosmological_pos) h₁) h₂) h₃) h₄

noncomputable def outerRate : ℝ :=
  -B.cosmological * (B.event - B.inner) * (B.event - B.cosmologicalRadius) *
    (B.event - B.negativeRoot) / (3 * B.event ^ 2)

noncomputable def innerRate : ℝ :=
  B.cosmological * (B.inner - B.event) * (B.inner - B.cosmologicalRadius) *
    (B.inner - B.negativeRoot) / (6 * B.inner ^ 2)

theorem outerRate_pos : 0 < B.outerRate := by
  unfold outerRate
  apply div_pos _ (by positivity [B.event_pos])
  apply mul_pos _ (sub_pos.2 (B.negativeRoot_neg.trans B.event_pos))
  exact mul_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (neg_neg_of_pos B.cosmological_pos) (sub_pos.2 B.inner_lt_event))
    (sub_neg.2 B.event_lt_cosmological)

theorem innerRate_pos : 0 < B.innerRate := by
  unfold innerRate
  apply div_pos _ (by positivity [B.inner_pos])
  apply mul_pos _ (sub_pos.2 (B.negativeRoot_neg.trans B.inner_pos))
  exact mul_pos_of_neg_of_neg
    (mul_neg_of_pos_of_neg B.cosmological_pos (sub_neg.2 B.inner_lt_event))
    (sub_neg.2 (B.inner_lt_event.trans B.event_lt_cosmological))

end Background

theorem factored_horizon_hasDerivAt_root {r : ℝ} (hr : r ≠ 0) (s t u Λ : ℝ) :
    HasDerivAt (fun x => -Λ * (x - r) * (x - s) * (x - t) * (x - u) / (3 * x ^ 2))
      (-Λ * (r - s) * (r - t) * (r - u) / (3 * r ^ 2)) r := by
  have hd := (((((hasDerivAt_id r).sub_const r).const_mul (-Λ)).mul
    ((hasDerivAt_id r).sub_const s)).mul ((hasDerivAt_id r).sub_const t)).mul
    ((hasDerivAt_id r).sub_const u)
  have h := hd.div (((hasDerivAt_id r).pow 2).const_mul 3)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hr))
  apply h.congr_deriv
  dsimp
  field_simp
  ring

namespace Background

open Filter
open scoped Topology

variable (B : Background)

theorem hasDerivAt_F_event : HasDerivAt B.F B.outerRate B.event := by
  apply (factored_horizon_hasDerivAt_root B.event_pos.ne' B.inner
    B.cosmologicalRadius B.negativeRoot B.cosmological).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds B.event_pos.ne'] with r hr
  rw [B.factorization hr]
  ring

theorem hasDerivAt_F_inner : HasDerivAt B.F (-2 * B.innerRate) B.inner := by
  have hd := factored_horizon_hasDerivAt_root B.inner_pos.ne' B.event
    B.cosmologicalRadius B.negativeRoot B.cosmological
  have hderiv : -B.cosmological * (B.inner - B.event) * (B.inner - B.cosmologicalRadius) *
      (B.inner - B.negativeRoot) / (3 * B.inner ^ 2) = -2 * B.innerRate := by
    unfold innerRate
    ring
  apply (hd.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds B.inner_pos.ne'] with r hr
  exact B.factorization hr

theorem hasDerivAt_F_cosmological : HasDerivAt B.F
    (-B.cosmological * (B.cosmologicalRadius - B.inner) * (B.cosmologicalRadius - B.event) *
      (B.cosmologicalRadius - B.negativeRoot) / (3 * B.cosmologicalRadius ^ 2)) B.cosmologicalRadius := by
  apply (factored_horizon_hasDerivAt_root B.cosmologicalRadius_pos.ne' B.inner
    B.event B.negativeRoot B.cosmological).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds B.cosmologicalRadius_pos.ne'] with r hr
  rw [B.factorization hr]
  ring

theorem hasDerivAt_F_negative : HasDerivAt B.F
    (-B.cosmological * (B.negativeRoot - B.inner) * (B.negativeRoot - B.event) *
      (B.negativeRoot - B.cosmologicalRadius) / (3 * B.negativeRoot ^ 2)) B.negativeRoot := by
  apply (factored_horizon_hasDerivAt_root B.negativeRoot_neg.ne B.inner
    B.event B.cosmologicalRadius B.cosmological).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds B.negativeRoot_neg.ne] with r hr
  rw [B.factorization hr]
  ring

end Background

end CauchyHorizon
