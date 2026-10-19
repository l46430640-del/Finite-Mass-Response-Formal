import CauchyHorizon.Characteristic.AuxiliaryRadiationEnergy
import CauchyHorizon.Reduced.RadiationHalfline

/-! The actual moving transverse difference on a late half-line. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

def AuxiliaryRadiationHalfline (B : Background) {U : ℝ} (hU : 0 ≤ U)
    (X : (V : Ici (0 : ℝ)) → WaveState U V) (gY g : ℝ → ℝ) (β Y L l b₀ : ℝ)
    (A : ℝ → ℝ) : Prop :=
  ∃ D : C(ℝ, C(Icc (0 : ℝ) U, ℝ)),
    (∀ t ≥ b₀, ∀ u : Icc (0 : ℝ) U,
      let z := projIcc 0 U hU (gY t)
      let w := projIcc 0 U hU (g (t / (1 + β)))
      D t u = radiationRow B.innerRate X t (max z (min u w)) - radiationRow B.innerRate X t z) ∧
    MemLp D 2 (volume.restrict (Ici b₀)) ∧
    let C := Real.exp (2 + 1 / 16) * (L * (Y - B.inner)) ^ 2
    (∫ t in Ici b₀, ‖D t‖ ^ 2) ≤
      2 * (C / ((B.inner / 2) * B.innerRate)) ^ 2 * (∫ t in Ici l, A t ^ 2) +
        2 * (C * (2 * Real.exp 2) / (4 * B.innerRate ^ 2 * (B.inner / 2) ^ 2)) ^ 2 *
          ∫ t in Ici l, ‖radiationRow B.innerRate X t‖ ^ 2

set_option maxHeartbeats 800000 in
theorem auxiliary_radiation_halfline (B : Background) {U T₀ β Y L l b₀ : ℝ}
    (hU : 0 ≤ U) (hβ : 0 ≤ β) (hl : 0 ≤ l)
    (hstart : max l T₀ ≤ b₀ / (1 + β))
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hR : MemLp (radiationRow B.innerRate X) 2 (volume.restrict (Ici 0)))
    (gY g A : ℝ → ℝ) (hgY : ContinuousOn gY (Ici l)) (hg : ContinuousOn g (Ici T₀))
    (hA : MemLp A 2 (volume.restrict (Ici l)))
    (hfinite : ∀ (V : Ici (0 : ℝ)) (hV : b₀ ≤ V),
      AuxiliaryRadiationEstimate B hU V.property (X V) gY g β Y L
        (projIcc 0 (V : ℝ) V.property l) ⟨b₀, by
          have hα : 0 < 1 + β := by linarith only [hβ]
          have hh := (le_div_iff₀ hα).1 (hl.trans ((le_max_left _ _).trans hstart))
          simpa only [zero_mul] using hh, hV⟩ A) :
    AuxiliaryRadiationHalfline B hU X gY g β Y L l b₀ A := by
  have hα : 0 < 1 + β := by linarith only [hβ]
  have hb₀ : 0 ≤ b₀ := by
    have hh := (le_div_iff₀ hα).1 (hl.trans ((le_max_left _ _).trans hstart))
    simpa only [zero_mul] using hh
  have hlb : l ≤ b₀ := ((le_max_left _ _).trans hstart).trans
    (div_le_self hb₀ (by linarith only [hβ]))
  let R : C(ℝ, C(Icc (0 : ℝ) U, ℝ)) :=
    ⟨radiationRow B.innerRate X, continuous_radiationRow X hcompat⟩
  let z : C(ℝ, Icc (0 : ℝ) U) := ⟨fun t => projIcc 0 U hU (gY (max b₀ t)),
    continuous_projIcc.comp (hgY.comp_continuous (by fun_prop)
      (fun t => hlb.trans (le_max_left _ _)))⟩
  let w : C(ℝ, Icc (0 : ℝ) U) := ⟨fun t => projIcc 0 U hU (g (max b₀ t / (1 + β))),
    continuous_projIcc.comp (hg.comp_continuous (by fun_prop)
      (fun t => ((le_max_right _ _).trans hstart).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) hα.le)))⟩
  let D : C(ℝ, C(Icc (0 : ℝ) U, ℝ)) :=
    (⟨fun q : ℝ × Icc (0 : ℝ) U =>
      R q.1 (max (z q.1) (min q.2 (w q.1))) - R q.1 (z q.1), by fun_prop⟩ :
      C(ℝ × Icc (0 : ℝ) U, ℝ)).curry
  have hD (t : ℝ) : ‖D t‖ ≤ 2 * ‖radiationRow B.innerRate X t‖ := by
    apply (ContinuousMap.norm_le (D t) (by positivity)).2
    intro u
    change ‖R t (max (z t) (min u (w t))) - R t (z t)‖ ≤ 2 * ‖R t‖
    exact (norm_sub_le _ _).trans ((add_le_add (R t |>.norm_coe_le_norm _)
      (R t |>.norm_coe_le_norm _)).trans_eq (by ring))
  have hRi : IntegrableOn (fun t => ‖radiationRow B.innerRate X t‖ ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq_norm hR.1).1 hR
  have hRil : IntegrableOn (fun t => ‖radiationRow B.innerRate X t‖ ^ 2) (Ioi l) :=
    hRi.mono_set (fun _ ht => hl.trans ht.le)
  have hDi : MemLp D 2 (volume.restrict (Ici b₀)) :=
    (hR.mono_measure (Measure.restrict_mono (Ici_subset_Ici.2 hb₀) le_rfl)).of_le_mul
      D.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hD)
  have hDii : IntegrableOn (fun t => ‖D t‖ ^ 2) (Ioi b₀) :=
    (show IntegrableOn (fun t => ‖D t‖ ^ 2) (Ici b₀) volume from
      (memLp_two_iff_integrable_sq_norm hDi.1).1 hDi).mono_set Ioi_subset_Ici_self
  have hAi : IntegrableOn (fun t => A t ^ 2) (Ioi l) :=
    (show IntegrableOn (fun t => A t ^ 2) (Ici l) volume from
      (memLp_two_iff_integrable_sq hA.1).1 hA).mono_set Ioi_subset_Ici_self
  let C := Real.exp (2 + 1 / 16) * (L * (Y - B.inner)) ^ 2
  let CA := 2 * (C / ((B.inner / 2) * B.innerRate)) ^ 2
  let CM := 2 * (C * (2 * Real.exp 2) / (4 * B.innerRate ^ 2 * (B.inner / 2) ^ 2)) ^ 2
  have hE (V : Ici (0 : ℝ)) (hV : b₀ ≤ V) :
      (∫ t in b₀..(V : ℝ), ‖D t‖ ^ 2) ≤ CA * (∫ t in l..(V : ℝ), A t ^ 2) +
        CM * ∫ t in l..(V : ℝ), ‖radiationRow B.innerRate X t‖ ^ 2 := by
    obtain ⟨zV, wV, hzw, henergy⟩ := hfinite V hV
    have hlV : l ∈ Icc 0 (V : ℝ) := ⟨hl, hlb.trans hV⟩
    have hrow (t : ℝ) (ht : t ∈ Icc b₀ (V : ℝ)) :
        D t = transverseRadiationRows B.innerRate (X V) zV wV (projIcc 0 (V : ℝ) V.property t) := by
      have htV : t ∈ Icc 0 (V : ℝ) := ⟨hb₀.trans ht.1, ht.2⟩
      have hv : (⟨b₀, hb₀, hV⟩ : Icc 0 (V : ℝ)) ≤ projIcc 0 (V : ℝ) V.property t := by
        rw [projIcc_of_mem V.property htV]; exact ht.1
      obtain ⟨hz, hw, _⟩ := hzw _ hv
      simp only [projIcc_of_mem V.property htV] at hz hw
      ext u
      simp only [D, R, z, w, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
        max_eq_right ht.1, radiationRow_eq X hcompat V ht.2, transverseRadiationRows,
        spatialRadiationRows, projIcc_of_mem V.property htV, hz, hw, zero_mul, sub_zero]
      ring
    have hM (t : ℝ) (ht : t ∈ Icc l (V : ℝ)) :
        movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 (V : ℝ)) U) (fun _ => hU)
          0 B.innerRate 0 (X V) (projIcc 0 (V : ℝ) V.property t) = ‖radiationRow B.innerRate X t‖ := by
      change ‖movingSpatialRadiationRows (ContinuousMap.const (Icc 0 (V : ℝ)) U) (fun _ => hU)
        0 B.innerRate 0 (X V) (projIcc 0 (V : ℝ) V.property t)‖ = _
      rw [radiationRow_eq X hcompat V ht.2]
      congr 1
      ext u
      simp only [movingSpatialRadiationRows, spatialRadiationRows, ContinuousMap.curry_apply,
        ContinuousMap.coe_mk, ContinuousMap.const_apply, min_eq_left u.property.2]
    dsimp only [AuxiliaryRadiationEstimate] at henergy
    rw [projIcc_of_mem V.property hlV] at henergy
    change (∫ t in b₀..(V : ℝ), ‖transverseRadiationRows B.innerRate (X V) zV wV
      (projIcc 0 (V : ℝ) V.property t)‖ ^ 2) ≤ CA * (∫ t in l..(V : ℝ), A t ^ 2) +
        CM * ∫ t in l..(V : ℝ), _ at henergy
    convert henergy using 1
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hV] at ht
      exact congrArg (fun v : C(Icc (0 : ℝ) U, ℝ) => ‖v‖ ^ 2) (hrow t ht)
    · congr 1
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hlV.2] at ht
      exact (congrArg (fun v : ℝ => v ^ 2) (hM t ht)).symm
  refine ⟨D, ?_, hDi, ?_⟩
  · intro t ht u
    simp only [D, R, z, w, ContinuousMap.curry_apply, ContinuousMap.coe_mk, max_eq_right ht]
  · change (∫ t in Ici b₀, ‖D t‖ ^ 2) ≤ CA * (∫ t in Ici l, A t ^ 2) +
      CM * ∫ t in Ici l, ‖radiationRow B.innerRate X t‖ ^ 2
    simp only [integral_Ici_eq_integral_Ioi]
    exact le_of_tendsto_of_tendsto
      (intervalIntegral_tendsto_integral_Ioi (μ := volume) b₀ hDii tendsto_id)
      (((intervalIntegral_tendsto_integral_Ioi (μ := volume) l hAi tendsto_id).const_mul CA).add
        ((intervalIntegral_tendsto_integral_Ioi (μ := volume) l hRil tendsto_id).const_mul CM))
      ((eventually_ge_atTop b₀).mono (fun t ht => hE ⟨t, hb₀.trans ht⟩ ht))

end CauchyHorizon
