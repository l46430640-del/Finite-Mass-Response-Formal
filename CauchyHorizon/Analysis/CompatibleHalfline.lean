import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Continuous compatible finite traces and their uniform half-line energy bound. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

theorem exists_continuous_compatible_halfline {E : Type*} [TopologicalSpace E] {l : ℝ}
    (F : Ici l → ℝ → E) (hc : ∀ S, ContinuousOn (F S) (Icc l S))
    (hcompat : ∀ S T : Ici l, ∀ t ∈ Icc l (S : ℝ), t ∈ Icc l (T : ℝ) → F S t = F T t) :
    ∃ f : ℝ → E, ContinuousOn f (Ici l) ∧ ∀ S, EqOn f (F S) (Icc l S) := by
  let f := fun t : ℝ => F ⟨max l t, le_max_left l t⟩ t
  have heq (S : Ici l) : EqOn f (F S) (Icc l S) := by
    intro t ht
    exact hcompat _ S t ⟨ht.1, le_max_right _ _⟩ ht
  refine ⟨f, ?_, heq⟩
  intro t ht
  let S : Ici l := ⟨t + 1, by
    change l ≤ t + 1
    exact le_trans ht (le_add_of_nonneg_right zero_le_one)⟩
  have htS : t < (S : ℝ) := lt_add_one t
  have hnear : Icc l (S : ℝ) ∈ 𝓝[Ici l] t := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds htS)] with s hs hsS
    exact ⟨hs, hsS.le⟩
  exact ((hc S t ⟨ht, htS.le⟩).mono_of_mem_nhdsWithin hnear).congr_of_eventuallyEq
    (by filter_upwards [hnear] with s hs; exact heq S hs) (heq S ⟨ht, htS.le⟩)

theorem pair_energy_halfline {p q : ℝ → ℝ} {l C : ℝ}
    (hp : ContinuousOn p (Ici l)) (hq : ContinuousOn q (Ici l))
    (hb : ∀ S ≥ l, Real.sqrt (∫ t in l..S, p t ^ 2 + q t ^ 2) ≤ C) :
    MemLp p 2 (volume.restrict (Ici l)) ∧ MemLp q 2 (volume.restrict (Ici l)) ∧
      Real.sqrt (∫ t in Ici l, p t ^ 2 + q t ^ 2) ≤ C := by
  have hc := (hp.pow 2).add (hq.pow 2)
  have hlocal (S : ℝ) : IntegrableOn (fun t => p t ^ 2 + q t ^ 2) (Ioc l S) := by
    by_cases hS : l ≤ S
    · exact (hc.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · simp only [Ioc_eq_empty_of_le (le_of_not_ge hS), integrableOn_empty]
  have hi : IntegrableOn (fun t => p t ^ 2 + q t ^ 2) (Ioi l) :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded (C ^ 2) l hlocal tendsto_id (by
      filter_upwards [eventually_ge_atTop l] with S hS
      have hn (t : ℝ) : ‖p t ^ 2 + q t ^ 2‖ = p t ^ 2 + q t ^ 2 :=
        Real.norm_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      simpa only [hn] using (Real.sqrt_le_iff.1 (hb S hS)).2)
  have hi' := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 hi
  have hpmeas : AEStronglyMeasurable p (volume.restrict (Ici l)) := hp.aestronglyMeasurable measurableSet_Ici
  have hqmeas : AEStronglyMeasurable q (volume.restrict (Ici l)) := hq.aestronglyMeasurable measurableSet_Ici
  have hpi : Integrable (fun t => p t ^ 2) (volume.restrict (Ici l)) := by
    apply hi'.mono' (hpmeas.pow 2)
    filter_upwards [] with t
    change ‖p t ^ 2‖ ≤ p t ^ 2 + q t ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_add_of_nonneg_right (sq_nonneg (q t))
  have hqi : Integrable (fun t => q t ^ 2) (volume.restrict (Ici l)) := by
    apply hi'.mono' (hqmeas.pow 2)
    filter_upwards [] with t
    change ‖q t ^ 2‖ ≤ p t ^ 2 + q t ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_add_of_nonneg_left (sq_nonneg (p t))
  refine ⟨(memLp_two_iff_integrable_sq hpmeas).2 hpi, (memLp_two_iff_integrable_sq hqmeas).2 hqi, ?_⟩
  rw [integral_Ici_eq_integral_Ioi]
  exact le_of_tendsto (Real.continuous_sqrt.continuousAt.tendsto.comp
    (intervalIntegral_tendsto_integral_Ioi (μ := volume) l hi tendsto_id))
      ((eventually_ge_atTop l).mono (fun S hS => hb S hS))

end CauchyHorizon
