import CauchyHorizon.Characteristic.FiniteUniqueness
import CauchyHorizon.Reduced.MassRows

/-! Equal physical inputs give identical developments and their actual mass rows. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.incoming_unique_of_eq {U V R e Λ φ₀ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f g : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hg : MemLp g p (volume.restrict (Icc 0 U))) (he : f = g)
    {vOut : C(Icc 0 V, WaveVector)} {x y : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hg φ₀) vOut
      (incomingWaveVelocity hUR hp hg) y) : x = y := by
  subst g
  exact hx.incoming_unique hU hV hUR hp hf hy

theorem incoming_massRow_eq {U ε R e Λ φ₀ : ℝ} (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (hUR : U < R) {p : ℝ≥0∞} (hp : 4 ≤ p) {f g : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hg : MemLp g p (volume.restrict (Icc 0 U))) (he : f = g)
    {X Y : (V : Ici (0 : ℝ)) → WaveState U V}
    (hrX : ∀ (V : Ici (0 : ℝ)) u v, (X V).1 u v 0 ≠ 0)
    (hrY : ∀ (V : Ici (0 : ℝ)) u v, (Y V).1 u v 0 ≠ 0) (hXY : X = Y) :
    let N := fun V => radialNuField V.property e Λ (incomingWaveCurve hU hUR hp hf φ₀)
      (X V).1 (hrX V)
    let N' := fun V => radialNuField V.property e Λ (incomingWaveCurve hU hUR hp hg φ₀)
      (Y V).1 (hrY V)
    massRow hε e Λ X N hrX = massRow hε e Λ Y N' hrY := by
  subst g
  subst Y
  rfl

end CauchyHorizon
