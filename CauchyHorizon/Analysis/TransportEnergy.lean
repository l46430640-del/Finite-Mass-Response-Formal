import CauchyHorizon.Analysis.IntegratingFactor
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.ProjIcc

/-! Finite-window transport energy, retaining the lower time-boundary inflow. -/

open Set MeasureTheory Filter
open scoped Topology

namespace CauchyHorizon

theorem continuousOn_rectangle_integral {a b T S : ℝ} (hab : a ≤ b) (hTS : T ≤ S)
    {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F (Icc a b ×ˢ Icc T S)) :
    ContinuousOn (fun x => ∫ t in T..S, F (x, t)) (Icc a b) := by
  let E := fun x t => F (projIcc a b hab x, projIcc T S hTS t)
  have hE : Continuous (Function.uncurry E) :=
    hF.comp_continuous (by fun_prop) (fun z => ⟨(projIcc a b hab z.1).property, (projIcc T S hTS z.2).property⟩)
  have hc := continuous_parametric_integral_of_continuous (μ := volume) (s := Icc T S) hE isCompact_Icc
  apply hc.continuousOn.congr
  intro x hx
  change (∫ t in T..S, F (x, t)) = ∫ t in Icc T S, E x t
  rw [intervalIntegral.integral_of_le hTS, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  simp only [E, projIcc_of_mem hab hx, projIcc_of_mem hTS ht]

set_option maxHeartbeats 800000 in
theorem transport_energy_identity {a b T S : ℝ} (hab : a ≤ b) (hTS : T ≤ S)
    {p q c A B d f g qv cv : ℝ × ℝ → ℝ}
    (hp : ContinuousOn p (Icc a b ×ˢ Icc T S))
    (hq : ContinuousOn q (Icc a b ×ˢ Icc T S))
    (hc : ContinuousOn c (Icc a b ×ˢ Icc T S))
    (hA : ContinuousOn A (Icc a b ×ˢ Icc T S))
    (hB : ContinuousOn B (Icc a b ×ˢ Icc T S))
    (hd : ContinuousOn d (Icc a b ×ˢ Icc T S))
    (hf : ContinuousOn f (Icc a b ×ˢ Icc T S))
    (hg : ContinuousOn g (Icc a b ×ˢ Icc T S))
    (hqv : ContinuousOn qv (Icc a b ×ˢ Icc T S))
    (hcv : ContinuousOn cv (Icc a b ×ˢ Icc T S))
    (hpx : ∀ x ∈ Ioo a b, ∀ t ∈ Icc T S,
      HasDerivAt (fun y => p (y, t)) (A (x, t) * q (x, t) + f (x, t)) x)
    (hqx : ∀ x ∈ Ioo a b, ∀ t ∈ Icc T S,
      HasDerivAt (fun y => q (y, t))
        (B (x, t) * p (x, t) + d (x, t) * q (x, t) + g (x, t) - c (x, t) * qv (x, t)) x)
    (hqt : ∀ x ∈ Icc a b, ∀ t ∈ Icc T S,
      HasDerivWithinAt (fun v => q (x, v)) (qv (x, t)) (Icc T S) t)
    (hct : ∀ x ∈ Icc a b, ∀ t ∈ Icc T S,
      HasDerivWithinAt (fun v => c (x, v)) (cv (x, t)) (Icc T S) t) :
    let N := fun x => ∫ t in T..S, p (x, t) ^ 2 + q (x, t) ^ 2
    ContinuousOn N (Icc a b) ∧ ∀ x ∈ Ioo a b,
      HasDerivAt N
        ((∫ t in T..S, 2 * (A (x, t) + B (x, t)) * p (x, t) * q (x, t) +
          (2 * d (x, t) + cv (x, t)) * q (x, t) ^ 2 +
          2 * f (x, t) * p (x, t) + 2 * g (x, t) * q (x, t)) +
          c (x, T) * q (x, T) ^ 2 - c (x, S) * q (x, S) ^ 2) x := by
  intro N
  let E := fun z => p z ^ 2 + q z ^ 2
  let D := fun z => 2 * p z * (A z * q z + f z) +
    2 * q z * (B z * p z + d z * q z + g z - c z * qv z)
  have hE : ContinuousOn E (Icc a b ×ˢ Icc T S) := (hp.pow 2).add (hq.pow 2)
  have hD : ContinuousOn D (Icc a b ×ˢ Icc T S) := by dsimp only [D]; fun_prop
  refine ⟨continuousOn_rectangle_integral hab hTS hE, ?_⟩
  intro x hx
  have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
  have hslice {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F (Icc a b ×ˢ Icc T S))
      {y : ℝ} (hy : y ∈ Icc a b) : ContinuousOn (fun t => F (y, t)) (Icc T S) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hy, ht⟩)
  have hint {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F (Icc a b ×ˢ Icc T S))
      {y : ℝ} (hy : y ∈ Icc a b) : IntervalIntegrable (fun t => F (y, t)) volume T S :=
    (hslice hF hy).intervalIntegrable_of_Icc hTS
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hD
  have hder (y : ℝ) (hy : y ∈ Ioo a b) (t : ℝ) (ht : t ∈ Icc T S) :
      HasDerivAt (fun w => E (w, t)) (D (y, t)) y := by
    simpa only [E, D, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_def, Pi.add_def] using!
      ((hpx y hy t ht).pow 2).add ((hqx y hy t ht).pow 2)
  have hN := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y t => E (y, t)) (F' := fun y t => D (y, t))
    (bound := fun _ => K) (isOpen_Ioo.mem_nhds hx)
    (by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      rw [uIoc_of_le hTS]
      exact ((hslice hE ⟨hy.1.le, hy.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (hint hE hx')
    (by
      rw [uIoc_of_le hTS]
      exact ((hslice hD hx').mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (by
      filter_upwards [] with t ht y hy
      exact hK (y, t) ⟨⟨hy.1.le, hy.2.le⟩, by simpa only [uIcc_of_le hTS] using uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const
    (by
      filter_upwards [] with t ht y hy
      exact hder y hy t (by simpa only [uIcc_of_le hTS] using uIoc_subset_uIcc ht))).2
  let J := fun z => 2 * (A z + B z) * p z * q z + (2 * d z + cv z) * q z ^ 2 +
    2 * f z * p z + 2 * g z * q z
  let F := fun z => cv z * q z ^ 2 + c z * (2 * q z * qv z)
  have hJ : ContinuousOn J (Icc a b ×ˢ Icc T S) := by dsimp only [J]; fun_prop
  have hF : ContinuousOn F (Icc a b ×ˢ Icc T S) := by dsimp only [F]; fun_prop
  have hflux := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hTS
    ((hslice hc hx').mul ((hslice hq hx').pow 2))
    (fun t ht => show HasDerivAt (fun v => c (x, v) * q (x, v) ^ 2) (F (x, t)) t from by
      simpa only [F, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_def, Pi.mul_def] using!
        ((hct x hx' t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).mul
          (((hqt x hx' t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).pow 2))
    (hint hF hx')
  change (∫ t in T..S, F (x, t)) = c (x, S) * q (x, S) ^ 2 - c (x, T) * q (x, T) ^ 2 at hflux
  apply hN.congr_deriv
  have heq : (∫ t in T..S, D (x, t)) = (∫ t in T..S, J (x, t)) - ∫ t in T..S, F (x, t) := by
    rw [← intervalIntegral.integral_sub (hint hJ hx') (hint hF hx')]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [D, J, F]
    ring
  rw [heq, hflux]
  dsimp only [J]
  ring

end CauchyHorizon
