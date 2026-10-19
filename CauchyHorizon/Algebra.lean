import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Algebraic identities used by the reduced field equations and mass response. -/

namespace CauchyHorizon

noncomputable def horizonFunction (r mass charge cosmological : ℝ) : ℝ :=
  1 - 2 * mass / r + charge ^ 2 / r ^ 2 - cosmological * r ^ 2 / 3

noncomputable def radialPotential (r charge cosmological : ℝ) : ℝ :=
  -1 / (4 * r) + charge ^ 2 / (4 * r ^ 3) + cosmological * r / 4

theorem horizonFunction_mass_difference (r mass reference charge cosmological : ℝ) :
    horizonFunction r mass charge cosmological =
      horizonFunction r reference charge cosmological - 2 * (mass - reference) / r := by
  unfold horizonFunction
  ring

theorem mass_from_flux {r mass charge cosmological nu flux : ℝ} (hr : r ≠ 0)
    (hF : horizonFunction r mass charge cosmological = 4 * nu * flux) :
    mass = r / 2 * (1 + charge ^ 2 / r ^ 2 - cosmological * r ^ 2 / 3 -
      4 * nu * flux) := by
  unfold horizonFunction at hF
  field_simp [hr] at hF ⊢
  nlinarith [hF]

theorem density_decomposition (c c0 theta theta0 : ℝ) :
    c * theta ^ 2 - c0 * theta0 ^ 2 =
      c * (theta - theta0) ^ 2 + 2 * c * theta0 * (theta - theta0) +
        (c - c0) * theta0 ^ 2 := by
  ring

theorem square_difference (x y : ℝ) : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by
  ring

theorem critical_range {p : ℝ} (hp : 4 ≤ p) :
    0 < 1 - 1 / p ∧ 1 - 1 / p < 1 ∧ 0 < 1 - 2 / p := by
  have hp0 : 0 < p := by linarith
  constructor
  · have : 1 / p < 1 := (div_lt_one hp0).2 (by linarith)
    linarith
  constructor
  · have : 0 < 1 / p := div_pos zero_lt_one hp0
    linarith
  · have : 2 / p < 1 := (div_lt_one hp0).2 (by linarith)
    linarith

end CauchyHorizon
