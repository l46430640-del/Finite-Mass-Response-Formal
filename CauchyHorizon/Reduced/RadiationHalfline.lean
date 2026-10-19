import CauchyHorizon.Reduced.RectangleRestriction
import CauchyHorizon.Reduced.SpatialRadiation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Compatible actual radiation rows and their full-time energy. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

noncomputable def radiationRow {U : ℝ} (k : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (t : ℝ) : C(Icc 0 U, ℝ) :=
  spatialRadiationRows 0 k 0 (X ⟨max 0 t, le_max_left (0 : ℝ) t⟩)
    ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩

variable {U k : ℝ} (X : (T : Ici (0 : ℝ)) → WaveState U T)
  (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
    waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
      le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)

include hcompat

theorem radiationRow_eq (T : Ici (0 : ℝ)) {t : ℝ} (htT : t ≤ T) :
    radiationRow k X t = spatialRadiationRows 0 k 0 (X T) (projIcc 0 (T : ℝ) T.property t) := by
  have hv : projIcc 0 (T : ℝ) T.property t =
      (⟨max 0 t, le_max_left (0 : ℝ) t, max_le T.property htT⟩ : Icc 0 (T : ℝ)) := by
    apply Subtype.ext
    simp only [projIcc, min_eq_right htT]
  rw [hv]
  apply ContinuousMap.ext
  intro u
  have hh := congrArg (fun x : WaveState U (max 0 t) =>
    x.1 u ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ 0 *
      x.2.1 u ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ 1)
    (hcompat ⟨max 0 t, le_max_left (0 : ℝ) t⟩ T (max_le T.property htT))
  change (X T).1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + max 0 t, by simp, by simpa using max_le T.property htT⟩ 0 *
      (X T).2.1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + max 0 t, by simp, by simpa using max_le T.property htT⟩ 1 =
    (X ⟨max 0 t, le_max_left (0 : ℝ) t⟩).1 u ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ 0 *
      (X ⟨max 0 t, le_max_left (0 : ℝ) t⟩).2.1 u ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ 1 at hh
  simp only [zero_add] at hh
  simp only [radiationRow, spatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
    zero_mul, sub_zero]
  exact congrArg (fun z => Real.exp (k * max 0 t) * z) hh.symm

theorem continuous_radiationRow : Continuous (radiationRow k X) := by
  rw [continuous_iff_continuousAt]
  intro t
  let T : Ici (0 : ℝ) := ⟨max 0 t + 1, by change 0 ≤ max 0 t + 1; positivity⟩
  have htT : t < T := (le_max_right (0 : ℝ) t).trans_lt (lt_add_one _)
  have hc := (spatialRadiationRows 0 k 0 (X T)).continuous.comp
    (continuous_projIcc (h := T.property))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds htT] with s hs
  exact radiationRow_eq X hcompat T hs.le

theorem radiationRow_energy {E : ℝ} (hU : 0 ≤ U)
    (henergy : ∀ T : Ici (0 : ℝ),
      let S := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 (T : ℝ)) U)
        (fun _ => hU) 0 k 0 (X T)
      (∫ t in (0 : ℝ)..(T : ℝ), (S (projIcc 0 (T : ℝ) T.property t)) ^ 2) ≤ E) :
    MemLp (radiationRow k X) 2 (volume.restrict (Ici 0)) ∧
      (∫ t in Ici (0 : ℝ), ‖radiationRow k X t‖ ^ 2) ≤ E := by
  have hc := continuous_radiationRow (k := k) X hcompat
  have hfinite (T : Ici (0 : ℝ)) : (∫ t in (0 : ℝ)..(T : ℝ), ‖radiationRow k X t‖ ^ 2) ≤ E := by
    apply le_trans _ (henergy T)
    apply le_of_eq
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le T.property] at ht
    dsimp only
    rw [radiationRow_eq X hcompat T ht.2]
    congr 2
    apply ContinuousMap.ext
    intro u
    simp only [spatialRadiationRows, movingSpatialRadiationRows,
      ContinuousMap.curry_apply, ContinuousMap.coe_mk, ContinuousMap.const_apply, min_eq_left u.property.2]
  have hi : IntegrableOn (fun t => ‖radiationRow k X t‖ ^ 2) (Ioi 0) :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded E 0
      (fun t : ℝ => ((hc.norm.pow 2).intervalIntegrable (μ := volume) 0 t).1) tendsto_id (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hfinite ⟨t, ht⟩)
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 hi), ?_⟩
  rw [integral_Ici_eq_integral_Ioi]
  exact le_of_tendsto (intervalIntegral_tendsto_integral_Ioi (μ := volume) 0 hi tendsto_id)
    ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht => hfinite ⟨t, ht⟩))

end CauchyHorizon
