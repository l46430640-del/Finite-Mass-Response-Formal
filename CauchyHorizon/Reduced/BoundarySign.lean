import CauchyHorizon.Reduced.BoundaryConstraint

/-! A positive transported scalar persists at the horizon and makes its radial trace negative. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

theorem scalarBoundaryRow_pos_of_monotone {U d : ℝ} (hd : 0 ≤ d)
    (Y : (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      Y S u v = Y T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (hmono : ∀ T u, Monotone (Y T u))
    (hpos : ∀ u, 0 < Y ⟨1, (show (0 : ℝ) ≤ 1 from zero_le_one)⟩ u ⟨1, zero_le_one, le_rfl⟩)
    (Sh : C(Icc d U, ℝ)) (hlim : Tendsto (scalarBoundaryRow hd Y) atTop (𝓝 Sh)) :
    ∀ u, 0 < Sh u := by
  intro u
  let w : Icc 0 U := ⟨u, hd.trans u.property.1, u.property.2⟩
  have hl := ((continuous_eval_const u).tendsto Sh).comp hlim
  apply (hpos w).trans_le
  apply ge_of_tendsto hl
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  let T : Ici (0 : ℝ) := ⟨max 0 t, le_max_left (0 : ℝ) t⟩
  have hT : (1 : ℝ) ≤ T := ht.trans (le_max_right _ _)
  change Y ⟨1, (show (0 : ℝ) ≤ 1 from zero_le_one)⟩ w ⟨1, zero_le_one, le_rfl⟩ ≤
    Y T w ⟨T, T.property, le_rfl⟩
  rw [hcompat ⟨1, (show (0 : ℝ) ≤ 1 from zero_le_one)⟩ T hT w ⟨1, zero_le_one, le_rfl⟩]
  exact hmono T w hT

theorem BoundaryTransverseConstraint.strict_negative {d U : ℝ} {hdU : d ≤ U}
    {Z : C(Icc d U, WaveVector)} {N S : C(Icc d U, ℝ)}
    (hb : BoundaryTransverseConstraint hdU Z N S)
    (hR : ∀ u, 0 < Z u 0) (hN : ∀ u, N u ≤ 0) (hS : ∀ u, 0 < S u)
    (u : Icc d U) (hu : d < (u : ℝ)) : N u < 0 := by
  let G := fun t : ℝ => S (projIcc d U hdU t) ^ 2 *
    Real.exp (-Z (projIcc d U hdU t) 2) / Z (projIcc d U hdU t) 0
  have hsc : Continuous (fun t => S (projIcc d U hdU t)) := S.continuous.comp continuous_projIcc
  have hrc : Continuous (fun t => Z (projIcc d U hdU t) 0) :=
    (continuous_apply 0).comp (Z.continuous.comp continuous_projIcc)
  have hlc : Continuous (fun t => Z (projIcc d U hdU t) 2) :=
    (continuous_apply 2).comp (Z.continuous.comp continuous_projIcc)
  have hGc : Continuous G := ((hsc.pow 2).mul (Real.continuous_exp.comp hlc.neg)).div hrc
    (fun _ => (hR _).ne')
  have hI : 0 < ∫ t in d..(u : ℝ), G t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hGc.intervalIntegrable _ _)
      (fun _ _ => div_pos (mul_pos (pow_pos (hS _) 2) (Real.exp_pos _)) (hR _)) hu
  have he := hb u
  have hleft := mul_nonpos_of_nonpos_of_nonneg (hN ⟨d, le_rfl, hdU⟩)
    (Real.exp_pos (-Z ⟨d, le_rfl, hdU⟩ 2)).le
  have hn : N u * Real.exp (-Z u 2) < 0 := by
    change N u * Real.exp (-Z u 2) = _ - ∫ t in d..(u : ℝ), G t at he
    linarith only [he, hleft, hI]
  exact neg_of_mul_neg_left hn (Real.exp_pos _).le

end CauchyHorizon
