import CauchyHorizon.Reduced.CompactifiedGeometry
import CauchyHorizon.Reduced.SphericalCausalBoundary

/-! The compatible original solution in regular time, with a continuous auxiliary past collar. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

noncomputable def originalSpacetimeField {U : ℝ} (hU : 0 ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (ψ : ℝ → ℝ)
    (p : SphericalSpacetime) : WaveVector :=
  let row := renormalizedWaveRow (ε := 0) le_rfl 0 X (max 0 (ψ p.1.1))
  row (projIcc 0 U hU p.1.2) - (fun i => if i = 2 then row ⟨U, hU, le_rfl⟩ 2 else 0)

theorem originalSpacetimeField_continuousOn {U vm : ℝ} (hU : 0 ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (ψ : ℝ → ℝ)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hψ : ContinuousOn ψ (Ioo vm 0)) :
    ContinuousOn (originalSpacetimeField hU X ψ) (sphericalOpenRectangle vm 0 (-1) U) := by
  let P := sphericalOpenRectangle vm 0 (-1) U
  have ht : ContinuousOn (fun p : SphericalSpacetime => max 0 (ψ p.1.1)) P :=
    continuousOn_const.sup (hψ.comp (continuous_fst.fst.continuousOn) (fun _ hp => hp.1.1))
  have hrow : ContinuousOn (fun p : SphericalSpacetime =>
      renormalizedWaveRow (ε := 0) le_rfl 0 X (max 0 (ψ p.1.1))) P :=
    (renormalizedWaveRow_continuousOn le_rfl X hX).comp ht
      (fun p _ => show 0 ≤ max 0 (ψ p.1.1) from le_max_left 0 (ψ p.1.1))
  have hc : ContinuousOn (fun p : SphericalSpacetime =>
      renormalizedWaveRow (ε := 0) le_rfl 0 X (max 0 (ψ p.1.1))
        (projIcc 0 U hU p.1.2)) P :=
    continuous_eval.comp_continuousOn (hrow.prodMk (by fun_prop))
  have ha : ContinuousOn (fun p : SphericalSpacetime =>
      renormalizedWaveRow (ε := 0) le_rfl 0 X (max 0 (ψ p.1.1)) ⟨U, hU, le_rfl⟩ 2) P :=
    (continuous_apply 2).comp_continuousOn
      ((continuous_eval_const _).comp_continuousOn hrow)
  apply hc.sub
  apply continuousOn_pi.2
  intro i
  by_cases hi : i = 2
  · simpa only [hi, if_true] using ha
  · simpa only [hi, if_false] using (continuousOn_const : ContinuousOn (fun _ : SphericalSpacetime => (0 : ℝ)) P)

theorem originalSpacetimeField_radius_pos {U : ℝ} (hU : 0 ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (ψ : ℝ → ℝ)
    (hr : ∀ (S : Ici (0 : ℝ)) u v, 0 < (X S).1 u v 0) (p : SphericalSpacetime) :
    0 < originalSpacetimeField hU X ψ p 0 := by
  dsimp only [originalSpacetimeField, renormalizedWaveRow, ContinuousMap.coe_mk,
    Pi.sub_apply, Pi.add_apply]
  simp only [show (0 : Fin 3) ≠ 2 by decide, if_false, add_zero, sub_zero]
  exact hr _ _ _

theorem originalSpacetimeField_apply {U : ℝ} (hU : 0 ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) {ψ : ℝ → ℝ}
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hψ : IsRegularTimeCoordinate (anchoringLapse hU X) (-1) ψ)
    (S : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htS : t ≤ S)
    (u : Icc 0 U) (ω : UnitSphere) :
    originalSpacetimeField hU X ψ ((regularTime (anchoringLapse hU X) t, u), ω) =
      (X S).1 u ⟨t, ht, htS⟩ - (fun i => if i = 2 then (X S).1 ⟨U, hU, le_rfl⟩ ⟨t, ht, htS⟩ 2 else 0) := by
  have he : ψ (regularTime (anchoringLapse hU X) t) = t :=
    hψ.2.2.2.2.2.2.2.2.2.2.2 t (by change -1 < t; linarith)
  unfold originalSpacetimeField
  dsimp only
  rw [he, max_eq_right ht, projIcc_of_mem hU u.property]
  ext i
  simp only [Pi.sub_apply, renormalizedWaveRow_apply le_rfl X hX S ht htS,
    mul_zero, zero_mul, ite_self, add_zero]

end CauchyHorizon
