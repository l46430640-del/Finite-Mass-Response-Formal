import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Hom.Set

/-! The inverse of a positive decreasing arrival curve, including its zero-end limit. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

theorem exists_arrival_inverse_closed {g : ℝ → ℝ} {t₀ : ℝ}
    (hc : ContinuousOn g (Ici t₀)) (ha : StrictAntiOn g (Ici t₀))
    (hl : Tendsto g atTop (𝓝 0)) (hp : ∀ t ∈ Ici t₀, 0 < g t)
    (hd : ∀ t ∈ Ici t₀, DifferentiableAt ℝ g t ∧ deriv g t < 0) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Ioo 0 (g t₀)) ∧ Tendsto v (𝓝[>] (0 : ℝ)) atTop ∧
      (∀ u ∈ Ioo 0 (g t₀), t₀ < v u ∧ g (v u) = u ∧ HasDerivAt v (deriv g (v u))⁻¹ u) ∧
      ∀ t ∈ Ioi t₀, v (g t) = t := by
  classical
  have hbase : t₀ ∈ Ici t₀ := by simp only [mem_Ici, le_refl]
  have hmem {t : ℝ} (ht : t ∈ Ioi t₀) : t ∈ Ici t₀ := by
    change t₀ ≤ t
    exact (show t₀ < t from ht).le
  let F : (Ioi t₀)ᵒᵈ → Ioo 0 (g t₀) := fun t =>
    ⟨g t.val, hp t.val (hmem t.property), ha hbase (hmem t.property) t.property⟩
  have hmono : StrictMono F := by
    intro t w htw
    exact ha (hmem w.property) (hmem t.property) htw
  have hsurj : Function.Surjective F := by
    intro u
    obtain ⟨R, hR⟩ := eventually_atTop.1 (hl.eventually_lt_const u.property.1)
    let W := max R t₀
    have hW : t₀ ≤ W := le_max_right _ _
    have hcW := hc.mono (show Icc t₀ W ⊆ Ici t₀ from fun _ ht => ht.1)
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hW hcW
      (show (u : ℝ) ∈ Icc (g W) (g t₀) from ⟨(hR W (le_max_left _ _)).le, u.property.2.le⟩)
    have hts : t₀ < t := by
      by_contra h
      have ht' : t = t₀ := le_antisymm (not_lt.1 h) ht.1
      rw [ht'] at he
      linarith only [he, u.property.2]
    exact ⟨⟨t, hts⟩, Subtype.ext he⟩
  let e : (Ioi t₀)ᵒᵈ ≃o Ioo 0 (g t₀) := hmono.orderIsoOfSurjective F hsurj
  let v := fun u : ℝ => if hu : u ∈ Ioo 0 (g t₀) then (e.symm ⟨u, hu⟩).val else t₀
  have hv (u : Ioo 0 (g t₀)) : v u = (e.symm u).val := by
    dsimp only [v]
    rw [dif_pos u.property]
  have hcsub : Continuous (fun u : Ioo 0 (g t₀) => (e.symm u).val) :=
    continuous_subtype_val.comp e.symm.continuous
  have hcv : ContinuousOn v (Ioo 0 (g t₀)) := continuousOn_iff_continuous_domRestrict.2
    (hcsub.congr (fun u => (hv u).symm))
  have hdom (u : ℝ) (hu : u ∈ Ioo 0 (g t₀)) : t₀ < v u := by
    rw [hv ⟨u, hu⟩]
    exact (e.symm ⟨u, hu⟩).property
  have hright (u : ℝ) (hu : u ∈ Ioo 0 (g t₀)) : g (v u) = u := by
    rw [hv ⟨u, hu⟩]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨u, hu⟩)
  have hleft (t : ℝ) (ht : t₀ < t) : v (g t) = t := by
    have hu : g t ∈ Ioo 0 (g t₀) := ⟨hp t ht.le, ha hbase ht.le ht⟩
    exact ha.injOn (hdom _ hu).le ht.le (hright _ hu)
  have hlim : Tendsto v (𝓝[>] (0 : ℝ)) atTop := by
    apply tendsto_atTop.2
    intro R
    let W := max R t₀ + 1
    have hWt : t₀ < W := by dsimp only [W]; linarith only [le_max_right R t₀]
    have hWR : R < W := by dsimp only [W]; linarith only [le_max_left R t₀]
    have hsmall : ∀ᶠ u in 𝓝[>] (0 : ℝ), u < g W :=
      (eventually_lt_nhds (hp W hWt.le)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with u hu huW
    have hum : u ∈ Ioo 0 (g t₀) := ⟨hu, huW.trans (ha hbase hWt.le hWt)⟩
    have hWv : W < v u := by
      by_contra hnot
      have hh := ha.antitoneOn (hdom u hum).le hWt.le (not_lt.1 hnot)
      rw [hright u hum] at hh
      exact (not_le_of_gt huW) hh
    exact (hWR.trans hWv).le
  refine ⟨v, hcv, hlim, ?_, hleft⟩
  intro u hu
  have htu := (hdom u hu).le
  have hdg := hd (v u) htu
  refine ⟨hdom u hu, hright u hu, hdg.1.hasDerivAt.of_local_left_inverse
    ((hcv u hu).continuousAt (isOpen_Ioo.mem_nhds hu)) hdg.2.ne ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds hu] with y hy
  exact hright y hy

theorem exists_arrival_inverse {g : ℝ → ℝ} {T t₀ : ℝ}
    (hc : ContinuousOn g (Ioi T)) (ha : StrictAntiOn g (Ioi T))
    (hl : Tendsto g atTop (𝓝 0)) (hp : ∀ t ∈ Ioi T, 0 < g t)
    (hd : ∀ t ∈ Ioi T, DifferentiableAt ℝ g t ∧ deriv g t < 0) (ht₀ : T < t₀) :
    ∃ v : ℝ → ℝ, ContinuousOn v (Ioo 0 (g t₀)) ∧ Tendsto v (𝓝[>] (0 : ℝ)) atTop ∧
      (∀ u ∈ Ioo 0 (g t₀), t₀ < v u ∧ g (v u) = u ∧ HasDerivAt v (deriv g (v u))⁻¹ u) ∧
      ∀ t ∈ Ioi t₀, v (g t) = t := by
  have hsub : Ici t₀ ⊆ Ioi T := fun _ ht => ht₀.trans_le ht
  exact exists_arrival_inverse_closed (hc.mono hsub) (ha.mono hsub) hl
    (fun t ht => hp t (hsub ht)) (fun t ht => hd t (hsub ht))

theorem arrival_inverse_jacobian_bounds {g v : ℝ → ℝ} {u α η C : ℝ}
    (hu : 0 < u) (hα : 0 ≤ α) (hη : 0 < η)
    (hg : g (v u) = u) (hd : HasDerivAt v (deriv g (v u))⁻¹ u)
    (hlo : η ≤ -deriv g (v u) / g (v u))
    (hhi : -deriv g (v u) / g (v u) ≤ C) :
    α / (C * u) ≤ -deriv (fun x => α * v x) u ∧
      -deriv (fun x => α * v x) u ≤ α / (η * u) := by
  rw [hg] at hlo hhi
  have hl := (le_div_iff₀ hu).1 hlo
  have hh := (div_le_iff₀ hu).1 hhi
  have hp : 0 < -deriv g (v u) := (mul_pos hη hu).trans_le hl
  have he : -deriv (fun x => α * v x) u = α / (-deriv g (v u)) := by
    rw [(hd.const_mul α).deriv, div_eq_mul_inv, inv_neg]
    ring
  rw [he]
  exact ⟨div_le_div_of_nonneg_left hα hp hh,
    div_le_div_of_nonneg_left hα (mul_pos hη hu) hl⟩

end CauchyHorizon
