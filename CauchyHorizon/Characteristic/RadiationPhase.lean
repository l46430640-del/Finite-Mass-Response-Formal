import CauchyHorizon.Characteristic.RadiationComparison

/-! Fixed profile phases do not change the full-time nonlinear radiation limit. -/

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace CauchyHorizon

set_option maxHeartbeats 1000000 in
theorem radiation_comparison_phase {U ε k c a ℓ : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (P Q : ℕ → ℝ →ᵇ ℝ)
    (hd : ∀ n x, HasDerivAt (P n) (Q n x) x)
    (hQi : ∀ n, Integrable (fun x => Q n x ^ 2))
    (hQlim : Tendsto (fun n => ∫ x, Q n x ^ 2) atTop (𝓝 0))
    (hF : (∀ n, MemLp (radiationComparisonRow hε k c X (fun n v => P n (a * v + ℓ)) n)
        2 (volume.restrict (Ici 0))) ∧
      Tendsto (fun n => ∫ v in Ici (0 : ℝ),
        ‖radiationComparisonRow hε k c X (fun n v => P n (a * v + ℓ)) n v‖ ^ 2)
        atTop (𝓝 0)) (d : ℝ) :
    (∀ n, MemLp (radiationComparisonRow hε k c X (fun n v => P n (a * v + d)) n)
        2 (volume.restrict (Ici 0))) ∧
      Tendsto (fun n => ∫ v in Ici (0 : ℝ),
        ‖radiationComparisonRow hε k c X (fun n v => P n (a * v + d)) n v‖ ^ 2)
        atTop (𝓝 0) := by
  let F := radiationComparisonRow hε k c X (fun n v => P n (a * v + ℓ))
  let G := radiationComparisonRow hε k c X (fun n v => P n (a * v + d))
  let D := fun n v => P n (a * v + ℓ) - P n (a * v + d)
  have hphase (n : ℕ) : MemLp (D n) 2 (volume.restrict (Ici 0)) ∧
      (∫ v in Ici (0 : ℝ), D n v ^ 2) ≤ |ℓ - d| ^ 2 / a * ∫ x, Q n x ^ 2 :=
    phaseChange_l2_halfline (l := 0) (φ' := fun _ => a) (ψ' := fun _ => a)
    ha (abs_nonneg (ℓ - d))
    (show ContinuousOn (fun v => a * v + d) (Ici 0) by fun_prop)
    (show ContinuousOn (fun v => a * v + ℓ) (Ici 0) by fun_prop)
    (fun v _ => by simpa using ((hasDerivAt_id v).const_mul a).add_const d)
    (fun v _ => by simpa using ((hasDerivAt_id v).const_mul a).add_const ℓ)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun v _ => by rw [show a * v + ℓ - (a * v + d) = ℓ - d by ring])
    (P n).continuous (Q n).continuous (hd n) (hQi n)
  have hsplit (n : ℕ) (v : ℝ) : G n v = F n v + ContinuousMap.const _ (c * D n v) := by
    ext u
    simp only [G, F, D, radiationComparisonRow, ContinuousMap.sub_apply,
      ContinuousMap.add_apply, ContinuousMap.const_apply]
    ring
  have hGi (n : ℕ) : MemLp (G n) 2 (volume.restrict (Ici 0)) := by
    have hFn : MemLp (F n) 2 (volume.restrict (Ici 0)) := hF.1 n
    have hC : MemLp (fun v => ContinuousMap.const (Icc ε U) (c * D n v)) 2
        (volume.restrict (Ici 0)) :=
      (ContinuousLinearMap.const ℝ (Icc ε U) : ℝ →L[ℝ] C(Icc ε U, ℝ)).comp_memLp'
        ((hphase n).1.const_mul c)
    have hadd : MemLp (fun v => F n v + ContinuousMap.const (Icc ε U) (c * D n v))
        2 (volume.restrict (Ici 0)) := by
      simpa only [Pi.sub_apply, Pi.neg_apply, sub_neg_eq_add] using! hFn.sub hC.neg
    exact MemLp.ae_eq (Eventually.of_forall fun v => (hsplit n v).symm) hadd
  have hFi (n : ℕ) : IntegrableOn (fun v => ‖F n v‖ ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq_norm (hF.1 n).1).1 (hF.1 n)
  have hDi (n : ℕ) : IntegrableOn (fun v => D n v ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq (hphase n).1.1).1 (hphase n).1
  have hbound (n : ℕ) : (∫ v in Ici (0 : ℝ), ‖G n v‖ ^ 2) ≤
      2 * (∫ v in Ici (0 : ℝ), ‖F n v‖ ^ 2) +
        (2 * c ^ 2 * (|ℓ - d| ^ 2 / a)) * ∫ x, Q n x ^ 2 := by
    have hh := integral_mono ((memLp_two_iff_integrable_sq_norm (hGi n).1).1 (hGi n))
      (((hFi n).const_mul 2).add ((hDi n).const_mul (2 * c ^ 2))) (fun v => by
        change ‖G n v‖ ^ 2 ≤ 2 * ‖F n v‖ ^ 2 + (2 * c ^ 2) * D n v ^ 2
        have hn : ‖G n v‖ ≤ ‖F n v‖ + ‖c * D n v‖ := by
          rw [hsplit]
          have hc : ‖ContinuousMap.const (Icc ε U) (c * D n v)‖ ≤ ‖c * D n v‖ :=
            (ContinuousMap.norm_le _ (norm_nonneg _)).2 (fun _ => le_rfl)
          exact (norm_add_le _ _).trans (add_le_add le_rfl hc)
        have hs : ‖G n v‖ ^ 2 ≤ 2 * ‖F n v‖ ^ 2 + 2 * ‖c * D n v‖ ^ 2 :=
          (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (by
            nlinarith only [sq_nonneg (‖F n v‖ - ‖c * D n v‖)])
        simpa only [norm_mul, mul_pow, Real.norm_eq_abs, sq_abs, mul_assoc] using hs)
    change (∫ v in Ici (0 : ℝ), ‖G n v‖ ^ 2) ≤
      ∫ v in Ici (0 : ℝ), 2 * ‖F n v‖ ^ 2 + (2 * c ^ 2) * D n v ^ 2 at hh
    rw [integral_add ((hFi n).const_mul 2) ((hDi n).const_mul _),
      integral_const_mul, integral_const_mul] at hh
    exact hh.trans (add_le_add le_rfl
      ((mul_le_mul_of_nonneg_left (hphase n).2 (by positivity)).trans_eq (by ring)))
  refine ⟨hGi, squeeze_zero (fun n => integral_nonneg (fun _ => sq_nonneg _)) hbound ?_⟩
  simpa only [mul_zero, add_zero] using
    (hF.2.const_mul 2).add (hQlim.const_mul (2 * c ^ 2 * (|ℓ - d| ^ 2 / a)))

end CauchyHorizon
