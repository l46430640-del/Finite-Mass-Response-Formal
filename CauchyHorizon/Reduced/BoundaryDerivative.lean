import CauchyHorizon.Analysis.PrimitiveLimit
import CauchyHorizon.Reduced.BoundaryTrace

/-! Compact physical derivative limits are derivatives of the actual horizon field. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

def IsTransverseWaveBoundary {U ε : ℝ} (hU : 0 ≤ U) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector))
    (Dh : C(Icc ε U, WaveVector)) : Prop :=
  (∀ (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U),
    HasDerivWithinAt (fun x => intervalExtension hU (X T).1 x ⟨t, ht, htT⟩)
      (D t u) (Icc 0 U) u) ∧
  Tendsto D atTop (𝓝 Dh) ∧
  Tendsto (fun w => D (χ w)) (𝓝[<] (0 : ℝ)) (𝓝 Dh) ∧
  ∀ u : Icc ε U, HasDerivWithinAt (intervalExtension hεU Z) (Dh u) (Icc ε U) u

theorem renormalized_boundary_hasDerivWithinAt {U ε k : ℝ}
    (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hZ : Tendsto (renormalizedWaveRow hε k X) atTop (𝓝 Z))
    (hD : Tendsto D atTop (𝓝 Dh))
    (hder : ∀ (t : ℝ) (ht : 0 ≤ t) (u : Icc ε U),
      HasDerivWithinAt (fun x => intervalExtension (hε.trans hεU) (X ⟨t, ht⟩).1 x ⟨t, ht, le_rfl⟩)
        (D t u) (Icc 0 U) u) :
    ∀ u : Icc ε U, HasDerivWithinAt (intervalExtension hεU Z) (Dh u) (Icc ε U) u := by
  apply (continuous_derivative_limit hεU hZ hD ?_).2
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  intro u
  have hd := ((hder t ht u).add_const (fun i => if i = 2 then 2 * k * t else 0)).mono
    (Icc_subset_Icc hε le_rfl)
  apply hd.congr_of_mem _ u.property
  intro x hx
  ext i
  change renormalizedWaveRow hε k X t (projIcc ε U hεU x) i = _
  rw [projIcc_of_mem hεU hx, renormalizedWaveRow_apply hε X hcompat ⟨t, ht⟩ ht le_rfl ⟨x, hx⟩ i]
  simp only [Pi.add_apply, intervalExtension_apply, projIcc_of_mem (hε.trans hεU)
    (show x ∈ Icc 0 U from ⟨hε.trans hx.1, hx.2⟩)]

end CauchyHorizon
