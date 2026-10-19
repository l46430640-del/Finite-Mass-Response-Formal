import CauchyHorizon.Analysis.PrimitiveCompatibility

/-! The continuous primitive determines its almost-everywhere derivative. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem horizontalPrimitive_injective {a b : ℝ} (hab : a < b)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    Function.Injective (horizontalPrimitive (E := E) hab.le) := by
  intro f g he
  apply Lp.ext
  filter_upwards [horizontalPrimitive_ae_hasDerivWithinAt hab.le f,
    horizontalPrimitive_ae_hasDerivWithinAt hab.le g, ae_restrict_mem measurableSet_Icc]
    with t hf hg ht
  rw [he] at hf
  exact (hf.derivWithin (uniqueDiffOn_Icc hab t ht)).symm.trans
    (hg.derivWithin (uniqueDiffOn_Icc hab t ht))

end CauchyHorizon
