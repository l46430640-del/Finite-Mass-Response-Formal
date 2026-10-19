import CauchyHorizon.Reduced.RegularIncomingConstraint
import CauchyHorizon.Analysis.IntervalRebase
import CauchyHorizon.Analysis.AbsoluteContinuityRebase

/-! The actual incoming constraint survives restriction, translation and evaluation on a ray. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

set_option maxHeartbeats 800000 in
theorem IsIncomingRadialConstraint.rebase {a b c ε U : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    {z : C(Icc a b, C(Icc ε U, WaveVector))}
    {d : Lp C(Icc ε U, WaveVector) 2 (volume.restrict (Icc a b))}
    (h : IsIncomingRadialConstraint (hac.trans hcb) z d)
    {d' : Lp C(Icc ε U, WaveVector) 2 (volume.restrict (Icc 0 (c - a)))}
    (hd' : d' =ᵐ[volume.restrict (Icc 0 (c - a))] fun t => d (a + t)) (u : Icc ε U) :
    let hV := sub_nonneg.2 hac
    let ev : C(Icc ε U, WaveVector) →L[ℝ] WaveVector := ContinuousMap.evalCLM ℝ u
    let zIn := ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 (c - a)) ev (z.comp (intervalRebase hcb))
    let uIn := ev.compLpL 2 (volume.restrict (Icc 0 (c - a))) d'
    ∃ n : C(Icc 0 (c - a), ℝ),
      (∀ᵐ t ∂volume.restrict (Icc 0 (c - a)), uIn t 0 = n (projIcc 0 (c - a) hV t)) ∧
      AbsolutelyContinuousOnInterval (intervalExtension hV n) 0 (c - a) ∧
      ∀ᵐ t ∂volume.restrict (Icc 0 (c - a)),
        HasDerivWithinAt (intervalExtension hV n)
          (uIn t 2 * n (projIcc 0 (c - a) hV t) - zIn (projIcc 0 (c - a) hV t) 0 * (uIn t 1) ^ 2)
          (Icc 0 (c - a)) t := by
  dsimp only
  let hV := sub_nonneg.2 hac
  let ev : C(Icc ε U, WaveVector) →L[ℝ] WaveVector := ContinuousMap.evalCLM ℝ u
  let uIn := ev.compLpL 2 (volume.restrict (Icc 0 (c - a))) d'
  obtain ⟨n, hn, hAC, hder⟩ := h u
  let n' := n.comp (intervalRebase hcb)
  have hm : MeasurePreserving (fun t : ℝ => a + t) (volume.restrict (Icc 0 (c - a)))
      (volume.restrict (Icc a c)) := by
    simpa only [add_sub_cancel] using intervalTranslate_measure a (c - a)
  have hs : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb
  have hna := hm.quasiMeasurePreserving.ae (ae_mono (Measure.restrict_mono hs le_rfl) hn)
  have hda := hm.quasiMeasurePreserving.ae (ae_mono (Measure.restrict_mono hs le_rfl) hder)
  have hvel : ∀ᵐ t ∂volume.restrict (Icc 0 (c - a)), uIn t = d (a + t) u := by
    filter_upwards [ev.coeFn_compLpL d', hd'] with t he ht
    exact he.trans (congrArg ev ht)
  have hmap (t : ℝ) (ht : t ∈ Icc 0 (c - a)) : a + t ∈ Icc a b :=
    ⟨le_add_of_nonneg_right ht.1, by linarith [ht.2]⟩
  have he (t : ℝ) (ht : t ∈ Icc 0 (c - a)) :
      intervalExtension hV n' t = intervalExtension (hac.trans hcb) n (a + t) := by
    simp only [intervalExtension_apply, projIcc_of_mem hV ht,
      projIcc_of_mem (hac.trans hcb) (hmap t ht)]
    rfl
  refine ⟨n', ?_, ?_, ?_⟩
  · filter_upwards [hvel, hna, ae_restrict_mem measurableSet_Icc] with t hv hn ht
    change uIn t 0 = intervalExtension hV n' t
    rw [hv, he t ht]
    exact hn
  · apply absolutelyContinuous_of_dist_le (absolutelyContinuous_rebase hac hcb hAC) (K := 1) zero_le_one
    intro s hs t ht
    rw [uIcc_of_le hV] at hs ht
    rw [he s hs, he t ht, one_mul]
  · filter_upwards [hvel, hda, ae_restrict_mem measurableSet_Icc] with t hv hd ht
    have hshift := (hasDerivAt_id t).const_add a
    have hh := hd.comp t hshift.hasDerivWithinAt (fun x hx => hmap x hx)
    simp only [mul_one] at hh
    apply (hh.congr_of_mem (fun x hx => he x hx) ht).congr_deriv
    change d (a + t) u 2 * n (projIcc a b (hac.trans hcb) (a + t)) -
      z (projIcc a b (hac.trans hcb) (a + t)) u 0 * (d (a + t) u 1) ^ 2 = _
    rw [projIcc_of_mem (hac.trans hcb) (hmap t ht), projIcc_of_mem hV ht, hv]
    rfl

end CauchyHorizon
