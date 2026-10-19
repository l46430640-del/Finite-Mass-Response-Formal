import CauchyHorizon.Reduced.MassRows
import CauchyHorizon.Reduced.CompactifiedGeometry

/-! Continuity of the actual mass on the full compatible observation half-line. -/

open Set

namespace CauchyHorizon

theorem continuousOn_massRow {U ε e Λ : ℝ} (hε : 0 ≤ ε)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)))
    (hr : ∀ (V : Ici (0 : ℝ)) u v, (X V).1 u v 0 ≠ 0)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hN : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      N S u v = N T u ⟨v, v.property.1, v.property.2.trans hST⟩) :
    ContinuousOn (massRow hε e Λ X N hr) (Ici 0) := by
  apply scalarBoundaryRow_continuousOn
  intro S T hST u v
  have hz := congrArg (fun w : WaveState U S => w.1 u v) (hX S T hST)
  have hw := congrArg (fun w : WaveState U S => w.2.1 u v) (hX S T hST)
  change (X T).1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
    ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X S).1 u v at hz
  change (X T).2.1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
    ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X S).2.1 u v at hw
  simp only [zero_add] at hz hw
  simp only [massField_apply, ← hz, ← hw, hN S T hST]

end CauchyHorizon
