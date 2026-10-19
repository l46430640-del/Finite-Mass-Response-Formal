import CauchyHorizon.Analysis.RegularTime
import CauchyHorizon.Reduced.AmplitudeTrace
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The actual lapse on the anchoring ray supplies an integrable regular time coordinate. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def anchoringLapse {U : ℝ} (hU : 0 ≤ U)
    (X : (V : Ici (0 : ℝ)) → WaveState U V) (t : ℝ) : ℝ :=
  Real.exp (renormalizedWaveRow (ε := U) hU 0 X (max 0 t) ⟨U, le_rfl, le_rfl⟩ 2)

theorem anchoring_lapse_data {U k T₀ Alo Ahi : ℝ} (hU : 0 ≤ U) (hk : 0 < k) (hT₀ : 0 ≤ T₀)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hamp : ∀ t, T₀ ≤ t →
      Alo ≤ waveAmplitude (renormalizedWaveRow (ε := U) hU k X t) ⟨U, le_rfl, le_rfl⟩ ∧
        waveAmplitude (renormalizedWaveRow (ε := U) hU k X t) ⟨U, le_rfl, le_rfl⟩ ≤ Ahi) :
    Continuous (anchoringLapse hU X) ∧ (∀ t, 0 < anchoringLapse hU X t) ∧
      (∀ t, IntegrableOn (anchoringLapse hU X) (Ioi t)) ∧
      (∀ (V : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htV : t ≤ V),
        anchoringLapse hU X t = Real.exp ((X V).1 ⟨U, hU, le_rfl⟩ ⟨t, ht, htV⟩ 2)) ∧
      ∀ t, T₀ ≤ t → Alo * Real.exp (-(2 * k) * t) ≤ anchoringLapse hU X t ∧
        anchoringLapse hU X t ≤ Ahi * Real.exp (-(2 * k) * t) := by
  have hp (V : Ici (0 : ℝ)) {t : ℝ} (htV : t ≤ V) :
      anchoringLapse hU X t = Real.exp ((X V).1 ⟨U, hU, le_rfl⟩ (projIcc 0 (V : ℝ) V.property t) 2) := by
    have hv : projIcc 0 (V : ℝ) V.property t =
        (⟨max 0 t, le_max_left (0 : ℝ) t, max_le V.property htV⟩ : Icc 0 (V : ℝ)) := by
      apply Subtype.ext
      simp only [projIcc, min_eq_right htV]
    unfold anchoringLapse
    rw [renormalizedWaveRow_apply hU X hX V (le_max_left (0 : ℝ) t)
      (max_le V.property htV) ⟨U, le_rfl, le_rfl⟩ 2, hv]
    simp only [ite_true, mul_zero, zero_mul, add_zero]
  have he (V : Ici (0 : ℝ)) {t : ℝ} (ht : 0 ≤ t) (htV : t ≤ V) :
      anchoringLapse hU X t = Real.exp ((X V).1 ⟨U, hU, le_rfl⟩ ⟨t, ht, htV⟩ 2) := by
    rw [hp V htV, projIcc_of_mem V.property (show t ∈ Icc 0 (V : ℝ) from ⟨ht, htV⟩)]
  have hc : Continuous (anchoringLapse hU X) := by
    rw [continuous_iff_continuousAt]
    intro t
    let V : Ici (0 : ℝ) := ⟨max 0 t + 1, by change 0 ≤ max 0 t + 1; positivity⟩
    have htV : t < V := (le_max_right (0 : ℝ) t).trans_lt (lt_add_one _)
    have hcont : Continuous (fun w => Real.exp ((X V).1 ⟨U, hU, le_rfl⟩
        (projIcc 0 (V : ℝ) V.property w) 2)) := by fun_prop
    apply hcont.continuousAt.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds htV] with w hw
    exact hp V hw.le
  have hpos (t : ℝ) : 0 < anchoringLapse hU X t := Real.exp_pos _
  have hb (t : ℝ) (ht : T₀ ≤ t) :
      Alo * Real.exp (-(2 * k) * t) ≤ anchoringLapse hU X t ∧
        anchoringLapse hU X t ≤ Ahi * Real.exp (-(2 * k) * t) := by
    have ht0 := hT₀.trans ht
    have hh := hamp t ht
    rw [waveAmplitude_renormalizedWaveRow_apply hU X hX ⟨t, ht0⟩ ht0 le_rfl,
      ← he ⟨t, ht0⟩ ht0 le_rfl] at hh
    have hcancel : (Real.exp (2 * k * t) * anchoringLapse hU X t) * Real.exp (-(2 * k) * t) =
        anchoringLapse hU X t := by
      rw [neg_mul, Real.exp_neg]
      field_simp
    exact ⟨(mul_le_mul_of_nonneg_right hh.1 (Real.exp_pos _).le).trans_eq hcancel,
      hcancel.symm.trans_le (mul_le_mul_of_nonneg_right hh.2 (Real.exp_pos _).le)⟩
  have htail : IntegrableOn (anchoringLapse hU X) (Ioi T₀) := by
    apply ((integrableOn_exp_mul_Ioi (by linarith only [hk] : -(2 * k) < 0) T₀).const_mul Ahi).mono'
      hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs, abs_of_pos (hpos t)] using (hb t ht.le).2
  refine ⟨hc, hpos, ?_, (fun V t ht htV => he V ht htV), hb⟩
  intro t
  have hi : IntegrableOn (anchoringLapse hU X) (Ici t) := by
    apply integrableOn_Ici_iff_integrableAtFilter_atTop.2
    exact ⟨⟨Ioi T₀, Ioi_mem_atTop _, htail⟩, hc.continuousOn.locallyIntegrableOn measurableSet_Ici⟩
  exact hi.mono_set Ioi_subset_Ici_self

end CauchyHorizon
