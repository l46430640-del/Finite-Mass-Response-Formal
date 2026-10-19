import CauchyHorizon.Characteristic.LateRadiationEnergy
import CauchyHorizon.Reduced.RadiationHalfline

/-! The actual late difference has a uniform exponentially decaying mixed tail. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

def LateRadiationHalfline {U : ℝ} (hU : 0 ≤ U) (k β T₀ q E : ℝ)
    (X : (V : Ici (0 : ℝ)) → WaveState U V) (g : ℝ → ℝ) : Prop :=
  ∃ D : C(ℝ, C(Icc (0 : ℝ) U, ℝ)),
    (∀ t u,
      let z := projIcc 0 U hU (g (max T₀ (t / (1 + β))))
      D t u = radiationRow k X t (max z u) - radiationRow k X t z) ∧
    MemLp (fun t => Real.exp (q * t) * ‖D t‖) 2 (volume.restrict (Ici 0)) ∧
    (∫ t in Ici (0 : ℝ), (Real.exp (q * t) * ‖D t‖) ^ 2) ≤ E ∧
    ∀ T : ℝ, 0 ≤ T → MemLp D 2 (volume.restrict (Ici T)) ∧
      (∫ t in Ici T, ‖D t‖ ^ 2) ≤ Real.exp (-(2 * q) * T) * E

set_option maxHeartbeats 800000 in
theorem late_radiation_halfline {U k β T₀ q E : ℝ} (hU : 0 ≤ U) (hq : 0 ≤ q)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ici T₀))
    (hfinite : ∀ V : Ici (0 : ℝ), ∃ W : C(Icc 0 (V : ℝ), ℝ),
      (∀ v, W v = g (max T₀ ((v : ℝ) / (1 + β)))) ∧
      (∫ t in (0 : ℝ)..(V : ℝ),
        (Real.exp (q * t) * ‖lateRadiationDifferenceRows hU W k (X V)
          (projIcc 0 (V : ℝ) V.property t)‖) ^ 2) ≤ E) :
    LateRadiationHalfline hU k β T₀ q E X g := by
  let R : C(ℝ, C(Icc (0 : ℝ) U, ℝ)) := ⟨radiationRow k X, continuous_radiationRow X hcompat⟩
  let z : C(ℝ, Icc (0 : ℝ) U) :=
    ⟨fun t => projIcc 0 U hU (g (max T₀ (t / (1 + β)))),
      continuous_projIcc.comp (hg.comp_continuous (by fun_prop)
        (fun t => show T₀ ≤ max T₀ (t / (1 + β)) from le_max_left _ _))⟩
  let D : C(ℝ, C(Icc (0 : ℝ) U, ℝ)) :=
    (⟨fun w : ℝ × Icc (0 : ℝ) U => R w.1 (max (z w.1) w.2) - R w.1 (z w.1),
      by fun_prop⟩ : C(ℝ × Icc (0 : ℝ) U, ℝ)).curry
  let F := fun t => Real.exp (q * t) * ‖D t‖
  have hFc : Continuous F := by fun_prop
  have hF0 (t : ℝ) : 0 ≤ F t := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hbound (V : Ici (0 : ℝ)) : (∫ t in (0 : ℝ)..(V : ℝ), F t ^ 2) ≤ E := by
    obtain ⟨W, hW, hE⟩ := hfinite V
    apply le_trans (le_of_eq _) hE
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le V.property] at ht
    have heq : D t = lateRadiationDifferenceRows hU W k (X V) (projIcc 0 (V : ℝ) V.property t) := by
      ext u
      simp only [D, R, z, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
        radiationRow_eq X hcompat V ht.2, lateRadiationDifferenceRows, transverseRadiationRows,
        spatialRadiationRows, ContinuousMap.const_apply, projIcc_of_mem V.property ht,
        hW, min_eq_left (show u ≤ ⟨U, hU, le_rfl⟩ from u.property.2), zero_mul, sub_zero]
      ring
    simp only [F, heq]
  have hi : IntegrableOn (fun t => F t ^ 2) (Ioi 0) :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded E 0
      (fun t : ℝ => ((hFc.pow 2).intervalIntegrable (μ := volume) 0 t).1) tendsto_id (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hbound ⟨t, ht⟩)
  have hi₀ : IntegrableOn (fun t => F t ^ 2) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 hi
  have hF : MemLp F 2 (volume.restrict (Ici 0)) :=
    (memLp_two_iff_integrable_sq hFc.aestronglyMeasurable).2 hi₀
  have hE : (∫ t in Ici (0 : ℝ), F t ^ 2) ≤ E := by
    rw [integral_Ici_eq_integral_Ioi]
    exact le_of_tendsto (intervalIntegral_tendsto_integral_Ioi (μ := volume) 0 hi tendsto_id)
      ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht => hbound ⟨t, ht⟩))
  refine ⟨D, fun t u => rfl, hF, hE, ?_⟩
  intro T hT
  have hsub : Ici T ⊆ Ici (0 : ℝ) := Ici_subset_Ici.2 hT
  have hFT := hF.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hdom (t : ℝ) (ht : T ≤ t) : ‖D t‖ ≤ Real.exp (-q * T) * F t := by
    have he : Real.exp (-q * T) * Real.exp (q * T) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht hq)) (norm_nonneg (D t))
    have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-q * T)).le
    simpa only [F, ← mul_assoc, he, one_mul] using hh'
  have hDi : MemLp D 2 (volume.restrict (Ici T)) := hFT.of_le_mul
    D.continuous.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      simpa only [Real.norm_of_nonneg (hF0 t)] using hdom t ht)
  have hFi := hi₀.mono_set hsub
  have hDii := (memLp_two_iff_integrable_sq_norm hDi.1).1 hDi
  have htail := integral_mono_ae hDii (hFi.const_mul ((Real.exp (-q * T)) ^ 2)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (hdom t ht) 2)
  have he : (Real.exp (-q * T)) ^ 2 = Real.exp (-(2 * q) * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change (∫ t in Ici T, ‖D t‖ ^ 2) ≤ ∫ t in Ici T, (Real.exp (-q * T)) ^ 2 * F t ^ 2 at htail
  rw [integral_const_mul, he] at htail
  exact ⟨hDi, htail.trans (mul_le_mul_of_nonneg_left
    ((setIntegral_mono_set hi₀ (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun _ ht => hsub ht))).trans hE) (Real.exp_pos _).le)⟩

end CauchyHorizon
