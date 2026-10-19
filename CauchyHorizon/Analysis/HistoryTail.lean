import CauchyHorizon.Analysis.PhaseEnergy

/-! A fixed-history limit and ordered small tails give a half-line energy limit. -/

open Set MeasureTheory Filter
open scoped Topology

namespace CauchyHorizon

theorem pair_energy_tendsto_of_history_tail {ι : Type*} {L : Filter ι} {l : ℝ}
    {F G : ι → ℝ → ℝ} {F₀ G₀ : ℝ → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Ici l)))
    (hG : ∀ i, MemLp (G i) 2 (volume.restrict (Ici l)))
    (hF₀ : MemLp F₀ 2 (volume.restrict (Ici l)))
    (hG₀ : MemLp G₀ 2 (volume.restrict (Ici l)))
    (hhistory : ∀ S : ℝ, l ≤ S → Tendsto (fun i => ∫ t in l..S,
      (F i t - F₀ t) ^ 2 + (G i t - G₀ t) ^ 2) L (𝓝 0))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ S : ℝ, T ≤ S →
      ∀ᶠ i in L, (∫ t in Ici S, F i t ^ 2 + G i t ^ 2) < ε) :
    Tendsto (fun i => ∫ t in Ici l,
      (F i t - F₀ t) ^ 2 + (G i t - G₀ t) ^ 2) L (𝓝 0) := by
  let E := fun i t => (F i t - F₀ t) ^ 2 + (G i t - G₀ t) ^ 2
  have hEi (i : ι) : IntegrableOn (E i) (Ici l) :=
    ((memLp_two_iff_integrable_sq (hF i |>.sub hF₀).aestronglyMeasurable).1 (hF i |>.sub hF₀)).add
      ((memLp_two_iff_integrable_sq (hG i |>.sub hG₀).aestronglyMeasurable).1 (hG i |>.sub hG₀))
  have hAi (i : ι) : IntegrableOn (fun t => F i t ^ 2 + G i t ^ 2) (Ici l) :=
    ((memLp_two_iff_integrable_sq (hF i).aestronglyMeasurable).1 (hF i)).add
      ((memLp_two_iff_integrable_sq (hG i).aestronglyMeasurable).1 (hG i))
  have hBi : IntegrableOn (fun t => F₀ t ^ 2 + G₀ t ^ 2) (Ici l) :=
    ((memLp_two_iff_integrable_sq hF₀.aestronglyMeasurable).1 hF₀).add
      ((memLp_two_iff_integrable_sq hG₀.aestronglyMeasurable).1 hG₀)
  have hBlim : Tendsto (fun S : ℝ => ∫ t in Ici S, F₀ t ^ 2 + G₀ t ^ 2) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun i => hc.trans_le (integral_nonneg (fun t =>
      add_nonneg (sq_nonneg _) (sq_nonneg _))))
  · intro ε hε
    obtain ⟨T, hT⟩ := htail (ε / 8) (by positivity)
    obtain ⟨S, hS, hST, hSB⟩ := ((eventually_ge_atTop l).and
      ((eventually_ge_atTop T).and (hBlim.eventually_lt_const (show 0 < ε / 8 by positivity)))).exists
    filter_upwards [hT S hST, (hhistory S hS).eventually_lt_const (show 0 < ε / 2 by positivity)] with i hi hhist
    have hsub : Ici S ⊆ Ici l := Ici_subset_Ici.2 hS
    have hiE := (hEi i).mono_set hsub
    have hiA := (hAi i).mono_set hsub
    have hiB := hBi.mono_set hsub
    have hbound : (∫ t in Ici S, E i t) ≤
        2 * (∫ t in Ici S, F i t ^ 2 + G i t ^ 2) +
          2 * (∫ t in Ici S, F₀ t ^ 2 + G₀ t ^ 2) := by
      have hh := integral_mono hiE ((hiA.const_mul 2).add (hiB.const_mul 2)) (fun t => by
        change (F i t - F₀ t) ^ 2 + (G i t - G₀ t) ^ 2 ≤
          2 * (F i t ^ 2 + G i t ^ 2) + 2 * (F₀ t ^ 2 + G₀ t ^ 2)
        nlinarith only [sq_nonneg (F i t + F₀ t), sq_nonneg (G i t + G₀ t)])
      change (∫ t in Ici S, E i t) ≤
        ∫ t in Ici S, 2 * (F i t ^ 2 + G i t ^ 2) + 2 * (F₀ t ^ 2 + G₀ t ^ 2) at hh
      simpa only [integral_add (hiA.const_mul 2) (hiB.const_mul 2), integral_const_mul] using hh
    have hsplit := intervalIntegral.integral_Ici_sub_Ici' (hEi i) hiE
    change (∫ t in Ici l, E i t) < ε
    change (∫ t in l..S, E i t) < ε / 2 at hhist
    linarith only [hbound, hsplit, hi, hhist, hSB]

end CauchyHorizon
