import CauchyHorizon.Analysis.LogarithmicEnergy
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Time energy on a radius arrival curve, using its logarithmic Jacobian. -/

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology ENNReal

namespace CauchyHorizon

theorem timeChange_l2_bound {l r η : ℝ} {τ τ' F : ℝ → ℝ}
    (hlr : l ≤ r) (hη : 0 < η) (hc : ContinuousOn τ (Icc l r))
    (hd : ∀ t ∈ Icc l r, HasDerivAt τ (τ' t) t)
    (hb : ∀ t ∈ Icc l r, η ≤ τ' t) (hF : Continuous F)
    (hi : Integrable (fun t => F t ^ 2)) :
    (∫ t in l..r, F (τ t) ^ 2) ≤ (∫ t, F t ^ 2) / η := by
  let P := fun y => ∫ z in (0 : ℝ)..y, F z ^ 2
  have hPd (y : ℝ) : HasDerivAt P (F y ^ 2) y :=
    intervalIntegral.integral_hasDerivAt_right ((hF.pow 2).intervalIntegrable _ _)
      ((hF.pow 2).stronglyMeasurableAtFilter volume _) (hF.pow 2).continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.2 (fun y => (hPd y).continuousAt)
  have hFc : ContinuousOn (fun t => F (τ t) ^ 2) (Icc l r) :=
    (hF.pow 2).comp_continuousOn hc
  have hmono : MonotoneOn τ (Icc l r) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hc
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    exact fun t ht => hη.le.trans (hb t (interior_subset ht))
  have horder := hmono (left_mem_Icc.2 hlr) (right_mem_Icc.2 hlr) hlr
  have hh := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hlr
    (hPc.comp_continuousOn hc)
    (fun t ht => ((hPd (τ t)).comp t (hd t ⟨ht.1.le, ht.2.le⟩)).hasDerivWithinAt)
    ((hFc.const_mul η).integrableOn_Icc)
    (fun t ht => by
      nlinarith only [mul_le_mul_of_nonneg_left (hb t ⟨ht.1.le, ht.2.le⟩) (sq_nonneg (F (τ t)))])
  rw [intervalIntegral.integral_const_mul] at hh
  dsimp only [P, Function.comp_def] at hh
  rw [intervalIntegral.integral_interval_sub_left (f := fun t => F t ^ 2) ((hF.pow 2).intervalIntegrable _ _)
    ((hF.pow 2).intervalIntegrable _ _), intervalIntegral.integral_of_le horder] at hh
  have htotal := setIntegral_le_integral (s := Ioc (τ l) (τ r)) hi
    (Filter.Eventually.of_forall (fun t => sq_nonneg (F t)))
  apply (le_div_iff₀ hη).2
  simpa only [mul_comm η] using hh.trans htotal

theorem timeChange_l2_halfline {l η : ℝ} {τ τ' F : ℝ → ℝ}
    (hη : 0 < η) (hc : ContinuousOn τ (Ici l))
    (hd : ∀ t ∈ Ici l, HasDerivAt τ (τ' t) t)
    (hb : ∀ t ∈ Ici l, η ≤ τ' t) (hF : Continuous F)
    (hi : Integrable (fun t => F t ^ 2)) :
    MemLp (fun t => F (τ t)) 2 (volume.restrict (Ici l)) ∧
      (∫ t in Ici l, F (τ t) ^ 2) ≤ (∫ t, F t ^ 2) / η := by
  have hFc : ContinuousOn (fun t => F (τ t)) (Ici l) := hF.comp_continuousOn hc
  have hfinite (v : ℝ) (hv : l ≤ v) :
      (∫ t in l..v, F (τ t) ^ 2) ≤ (∫ t, F t ^ 2) / η :=
    timeChange_l2_bound hv hη (hc.mono Icc_subset_Ici_self)
      (fun t ht => hd t ht.1) (fun t ht => hb t ht.1) hF hi
  have hlocal (v : ℝ) : IntegrableOn (fun t => F (τ t) ^ 2) (Ioc l v) := by
    by_cases hv : l ≤ v
    · exact (((hFc.pow 2).mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · rw [Ioc_eq_empty (not_lt.2 (le_of_not_ge hv))]
      exact integrableOn_empty
  have htail : IntegrableOn (fun t => F (τ t) ^ 2) (Ioi l) :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded ((∫ t, F t ^ 2) / η) l hlocal tendsto_id (by
      filter_upwards [eventually_ge_atTop l] with t ht
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hfinite t ht)
  have htail' := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 htail
  change Integrable (fun t => F (τ t) ^ 2) (volume.restrict (Ici l)) at htail'
  refine ⟨(memLp_two_iff_integrable_sq_norm (hFc.aestronglyMeasurable measurableSet_Ici)).2 ?_, ?_⟩
  · simpa only [Real.norm_eq_abs, sq_abs] using htail'
  · rw [integral_Ici_eq_integral_Ioi]
    exact le_of_tendsto (intervalIntegral_tendsto_integral_Ioi (μ := volume) l htail tendsto_id)
      ((eventually_ge_atTop l).mono (fun t ht => hfinite t ht))

theorem logarithmicIncoming_trace_energy {l r r₀ a b k D η ℓ : ℝ} {g : ℝ → ℝ}
    (hlr : l ≤ r) (hb : 0 < b) (hD : 0 < D) (hη : 0 < η) (hcrit : k = a * b)
    (hg : ContinuousOn g (Icc l r)) (hd : ∀ t ∈ Icc l r, DifferentiableAt ℝ g t)
    (hgp : ∀ t ∈ Icc l r, 0 < g t) (hgr : ∀ t ∈ Icc l r, g t ≤ r₀)
    (hscale : ∀ t ∈ Icc l r, g t * Real.exp (a * t) ≤ D)
    (hspeed : ∀ t ∈ Icc l r, η ≤ -deriv g t / g t)
    (B : ℝ →ᵇ ℝ) (hB : Integrable (fun t => B t ^ 2)) :
    (∫ t in l..r, (g t * Real.exp (k * t) * (r₀ - g t) * logarithmicIncoming b ℓ B (g t)) ^ 2) ≤
      (b * r₀ * D ^ b) ^ 2 / η * ∫ t, B t ^ 2 := by
  let τ := fun t => ℓ - Real.log (g t)
  have hτc : ContinuousOn τ (Icc l r) :=
    continuousOn_const.sub (hg.log (fun t ht => (hgp t ht).ne'))
  have hτd (t : ℝ) (ht : t ∈ Icc l r) : HasDerivAt τ (-deriv g t / g t) t := by
    simpa only [neg_div] using ((hd t ht).hasDerivAt.log (hgp t ht).ne').const_sub ℓ
  have htime := timeChange_l2_bound hlr hη hτc hτd hspeed B.continuous hB
  let A := fun t => b * (r₀ - g t) * (g t * Real.exp (a * t)) ^ b
  have hr₀ : 0 < r₀ := (hgp l (left_mem_Icc.2 hlr)).trans_le (hgr l (left_mem_Icc.2 hlr))
  have hAc : ContinuousOn A (Icc l r) := by
    have hp := (hg.mul (show Continuous (fun t => Real.exp (a * t)) by fun_prop).continuousOn).rpow_const
      (fun _ _ => Or.inr hb.le)
    exact (continuousOn_const.mul (continuousOn_const.sub hg)).mul hp
  have hAb (t : ℝ) (ht : t ∈ Icc l r) : 0 ≤ A t ∧ A t ≤ b * r₀ * D ^ b := by
    have hp : 0 ≤ (g t * Real.exp (a * t)) ^ b := Real.rpow_nonneg (by positivity [hgp t ht]) _
    refine ⟨mul_nonneg (mul_nonneg hb.le (sub_nonneg.2 (hgr t ht))) hp, ?_⟩
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (sub_le_self r₀ (hgp t ht).le) hb.le)
      (Real.rpow_le_rpow (by positivity [hgp t ht]) (hscale t ht) hb.le) hp (mul_nonneg hb.le hr₀.le)
  have hEq (t : ℝ) (ht : t ∈ Icc l r) :
      g t * Real.exp (k * t) * (r₀ - g t) * logarithmicIncoming b ℓ B (g t) = A t * B (τ t) := by
    have he : Real.exp (a * t) ^ b = Real.exp (k * t) := by
      rw [← Real.exp_mul, hcrit]
      congr 1
      ring
    dsimp only [A, τ, logarithmicIncoming]
    rw [Real.mul_rpow (hgp t ht).le (Real.exp_pos _).le, he,
      Real.rpow_sub (hgp t ht), Real.rpow_one]
    field_simp [(hgp t ht).ne']
  have hleft : ContinuousOn (fun t => (A t * B (τ t)) ^ 2) (Icc l r) :=
    (hAc.mul (B.continuous.comp_continuousOn hτc)).pow 2
  have hright : ContinuousOn (fun t => (b * r₀ * D ^ b) ^ 2 * B (τ t) ^ 2) (Icc l r) :=
    ((B.continuous.comp_continuousOn hτc).pow 2).const_mul _
  have hh := intervalIntegral.integral_mono_on (μ := volume) hlr
    (hleft.intervalIntegrable_of_Icc hlr) (hright.intervalIntegrable_of_Icc hlr) (fun t ht => by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (hAb t ht).1 (by positivity)).2 (hAb t ht).2) (sq_nonneg _))
  rw [intervalIntegral.integral_const_mul] at hh
  have hchange : (∫ t in l..r,
      (g t * Real.exp (k * t) * (r₀ - g t) * logarithmicIncoming b ℓ B (g t)) ^ 2) =
        ∫ t in l..r, (A t * B (τ t)) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlr] at ht
    dsimp only
    rw [hEq t ht]
  rw [hchange]
  exact (hh.trans (mul_le_mul_of_nonneg_left htime (sq_nonneg _))).trans_eq (by ring)

end CauchyHorizon
