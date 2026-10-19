import CauchyHorizon.Analysis.IntervalTranslate

/-! Moving an arbitrary left endpoint to zero preserves the initial primitive and does not increase its norms. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

def intervalRebase {a b c : ℝ} (hcb : c ≤ b) : C(Icc 0 (c - a), Icc a b) :=
  ⟨fun t => ⟨a + t, le_add_of_nonneg_right t.property.1,
    (by have := t.property.2; linarith : a + (t : ℝ) ≤ c).trans hcb⟩, by fun_prop⟩

theorem rebase_characteristic_data {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (z : C(Icc a b, E)) (d : Lp E 2 (volume.restrict (Icc a b))) {z₀ : E}
    (hz : z = ContinuousMap.const _ z₀ + horizontalPrimitive (hac.trans hcb) d) :
    ∃ d' : Lp E 2 (volume.restrict (Icc 0 (c - a))),
      (d' =ᵐ[volume.restrict (Icc 0 (c - a))] fun t => d (a + t)) ∧
      ‖d'‖ ≤ ‖d‖ ∧ ‖z.comp (intervalRebase hcb)‖ ≤ ‖z‖ ∧
      z.comp (intervalRebase hcb) = ContinuousMap.const _ z₀ +
        horizontalPrimitive (sub_nonneg.2 hac) d' := by
  have hs : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb
  have hm : MeasurePreserving (fun t : ℝ => a + t) (volume.restrict (Icc 0 (c - a)))
      (volume.restrict (Icc a c)) := by
    simpa only [add_sub_cancel] using intervalTranslate_measure a (c - a)
  have hpart := (Lp.memLp d).mono_measure (Measure.restrict_mono hs le_rfl)
  have hlp := hpart.comp_measurePreserving hm
  let d' := hlp.toLp (fun t => d (a + t))
  have hd' : d' =ᵐ[volume.restrict (Icc 0 (c - a))] fun t => d (a + t) := hlp.coeFn_toLp
  refine ⟨d', hd', ?_, ?_, ?_⟩
  · rw [Lp.norm_toLp, Lp.norm_def,
      show (fun t => d (a + t)) = (fun t => d t) ∘ (fun t => a + t) from rfl,
      eLpNorm_comp_measurePreserving hpart.1 hm]
    exact ENNReal.toReal_mono (Lp.memLp d).2.ne
      (eLpNorm_mono_measure _ (Measure.restrict_mono hs le_rfl))
  · apply (ContinuousMap.norm_le _ (norm_nonneg z)).2
    intro t
    exact z.norm_coe_le_norm _
  · apply ContinuousMap.ext
    intro t
    rw [hz]
    change z₀ + (∫ s in a..(a + (t : ℝ)), d s) = z₀ + ∫ s in (0 : ℝ)..(t : ℝ), d' s
    congr 1
    have hsub : Ioc 0 (t : ℝ) ⊆ Icc 0 (c - a) :=
      fun s hs => ⟨hs.1.le, hs.2.trans t.property.2⟩
    rw [intervalIntegral.integral_congr_ae_restrict (μ := volume)
      (f := fun s => d' s) (g := fun s => d (a + s))
      (by rw [uIoc_of_le t.property.1]; exact ae_mono (Measure.restrict_mono hsub le_rfl) hd'),
      intervalIntegral.integral_comp_add_left, add_zero]

end CauchyHorizon
