import CauchyHorizon.Radial.Background

namespace CauchyHorizon

theorem four_pole_decomposition {a b c d x : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d) :
    x ^ 2 / ((x - a) * (x - b) * (x - c) * (x - d)) =
      a ^ 2 / ((a - b) * (a - c) * (a - d) * (x - a)) +
      b ^ 2 / ((b - a) * (b - c) * (b - d) * (x - b)) +
      c ^ 2 / ((c - a) * (c - b) * (c - d) * (x - c)) +
      d ^ 2 / ((d - a) * (d - b) * (d - c) * (x - d)) := by
  field_simp
  ring

noncomputable def poleCoefficient (A Λ r s t u : ℝ) : ℝ :=
  (-3 * A / Λ) * (r ^ 2 / ((r - s) * (r - t) * (r - u)))

namespace Background

variable (B : Background)

noncomputable def innerExponent : ℝ :=
  poleCoefficient B.outerRate B.cosmological B.inner B.event B.cosmologicalRadius B.negativeRoot

noncomputable def cosmologicalExponent : ℝ :=
  poleCoefficient B.outerRate B.cosmological B.cosmologicalRadius B.inner B.event B.negativeRoot

noncomputable def negativeExponent : ℝ :=
  poleCoefficient B.outerRate B.cosmological B.negativeRoot B.inner B.event B.cosmologicalRadius

theorem event_pole_coefficient :
    poleCoefficient B.outerRate B.cosmological B.event B.inner B.cosmologicalRadius B.negativeRoot = 1 := by
  have hΛ := B.cosmological_pos.ne'
  have he := B.event_pos.ne'
  have h₁ := sub_ne_zero.2 B.inner_lt_event.ne'
  have h₂ := sub_ne_zero.2 B.event_lt_cosmological.ne
  have h₃ := sub_ne_zero.2 (B.negativeRoot_neg.trans B.event_pos).ne'
  unfold poleCoefficient outerRate
  field_simp

theorem inner_exponent_eq : B.innerExponent = -B.outerRate / (2 * B.innerRate) := by
  have hΛ := B.cosmological_pos.ne'
  have hi := B.inner_pos.ne'
  have h₁ := sub_ne_zero.2 B.inner_lt_event.ne
  have h₂ := sub_ne_zero.2 (B.inner_lt_event.trans B.event_lt_cosmological).ne
  have h₃ := sub_ne_zero.2 (B.negativeRoot_neg.trans B.inner_pos).ne'
  unfold innerExponent poleCoefficient innerRate
  field_simp
  ring

theorem cosmological_exponent_eq :
    B.cosmologicalExponent = B.outerRate / deriv B.F B.cosmologicalRadius := by
  rw [B.hasDerivAt_F_cosmological.deriv]
  unfold cosmologicalExponent poleCoefficient
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem negative_exponent_eq : B.negativeExponent = B.outerRate / deriv B.F B.negativeRoot := by
  rw [B.hasDerivAt_F_negative.deriv]
  unfold negativeExponent poleCoefficient
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem logarithmic_partial_fractions {r : ℝ} (hr : r ∈ Set.Ioo B.inner B.event) :
    B.outerRate / B.F r = B.innerExponent / (r - B.inner) + 1 / (r - B.event) +
      B.cosmologicalExponent / (r - B.cosmologicalRadius) + B.negativeExponent / (r - B.negativeRoot) := by
  have hir := (B.negativeRoot_neg.trans B.inner_pos).ne'
  have her := (B.negativeRoot_neg.trans B.event_pos).ne'
  have hcr := (B.negativeRoot_neg.trans B.cosmologicalRadius_pos).ne'
  have hr0 := (B.inner_pos.trans hr.1).ne'
  have hri := hr.1.ne'
  have hre := hr.2.ne
  have hrc := (hr.2.trans B.event_lt_cosmological).ne
  have hrn := (B.negativeRoot_neg.trans (B.inner_pos.trans hr.1)).ne'
  have hΛ := B.cosmological_pos.ne'
  have hid := four_pole_decomposition B.inner_lt_event.ne
    (B.inner_lt_event.trans B.event_lt_cosmological).ne hir B.event_lt_cosmological.ne her hcr
    hri hre hrc hrn
  have hs := congrArg (fun y => (-3 * B.outerRate / B.cosmological) * y) hid
  have he := B.event_pole_coefficient
  unfold poleCoefficient at he
  rw [B.factorization hr0]
  unfold innerExponent cosmologicalExponent negativeExponent poleCoefficient
  calc
    _ = (-3 * B.outerRate / B.cosmological) *
        (r ^ 2 / ((r - B.inner) * (r - B.event) * (r - B.cosmologicalRadius) * (r - B.negativeRoot))) := by
      field_simp
    _ = _ := by
      rw [hs]
      simp only [div_eq_mul_inv, mul_inv_rev] at he ⊢
      linear_combination (r - B.event)⁻¹ * he

end Background

end CauchyHorizon
