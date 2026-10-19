import CauchyHorizon.Reduced.RegularOpticalConstraint
import CauchyHorizon.Analysis.ConstantContinuation

/-! The actual continued characteristic data satisfy the radial constraint through regular time zero. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

def IsIncomingRadialConstraint {a b ε U : ℝ} (hab : a ≤ b)
    (z : C(Icc a b, C(Icc ε U, WaveVector)))
    (d : Lp C(Icc ε U, WaveVector) 2 (volume.restrict (Icc a b))) : Prop :=
  ∀ u : Icc ε U, ∃ n : C(Icc a b, ℝ),
    (∀ᵐ w ∂volume.restrict (Icc a b), d w u 0 = n (projIcc a b hab w)) ∧
    AbsolutelyContinuousOnInterval (intervalExtension hab n) a b ∧
    ∀ᵐ w ∂volume.restrict (Icc a b),
      HasDerivWithinAt (intervalExtension hab n)
        (d w u 2 * n (projIcc a b hab w) - z (projIcc a b hab w) u 0 * (d w u 1) ^ 2)
        (Icc a b) w

set_option maxHeartbeats 1000000 in
theorem IsRegularContinuationData.incoming_radial_constraint {U ε T b : ℝ}
    (hε : 0 ≤ ε) (hεU : ε ≤ U) (hT : 0 < T) (hb : 0 ≤ b)
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {O : C(Icc ε U, ℝ)}
    (hO : IsRegularOpticalConstraint hε hεU X χ Z O)
    {z : C(Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b, C(Icc ε U, WaveVector))}
    {d : Lp C(Icc ε U, WaveVector) 2
      (volume.restrict (Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b))}
    (hz : IsRegularContinuationData hε hεU X χ Z O T b z d) :
    IsIncomingRadialConstraint ((hχ.2.2.2.2.2.1 T).le.trans hb) z d := by
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  let a := V T
  have ha : a < 0 := hχ.2.2.2.2.2.1 T
  have hab : a ≤ b := ha.le.trans hb
  have hVa : V 0 < a := hχ.2.2.2.1 hT
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let Q := fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)
  intro u
  let f := fun w => compactifiedOpticalRow hε X χ O w u
  let F := fun w => f (min w 0)
  let ze := intervalExtension hab z
  let g := fun w => ze w u 0 * Real.exp (-ze w u 2) * (Q w u 1) ^ 2
  have hpast (w : ℝ) (hw : w ∈ Icc a 0) : ze w = Ψ w := by
    rw [intervalExtension_apply, projIcc_of_mem hab ⟨hw.1, hw.2.trans hb⟩]
    exact hz.2.1 _ hw.2
  have hfc : ContinuousOn f (Icc a 0) := (hO u).1.mono
    (fun w hw => ⟨hVa.trans_le hw.1, hw.2⟩)
  have hfd (w : ℝ) (hw : w ∈ Ioo a 0) : HasDerivAt f (g w) w := by
    dsimp only [g]
    rw [hpast w ⟨hw.1.le, hw.2.le⟩]
    exact ((hO u).2 w ⟨hVa.trans hw.1, hw.2⟩).1
  let ev : C(Icc ε U, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (1 : Fin 3)).comp (ContinuousMap.evalCLM ℝ u)
  have hq : MemLp (fun w => Q w u 1) 2 (volume.restrict (Icc a 0)) :=
    ((ev.comp_memLp' (Lp.memLp d)).mono_measure
      (Measure.restrict_mono (Icc_subset_Icc le_rfl hb) le_rfl)).ae_eq
        (hz.2.2.2.1.mono (fun _ hh => congrArg (fun z => z u 1) hh))
  have hg : IntervalIntegrable g volume a 0 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le ha.le).2
    exact IntegrableOn.continuousOn_mul (by dsimp only [ze]; fun_prop)
      ((memLp_two_iff_integrable_sq hq.1).1 hq) isCompact_Icc
  have hFAC : AbsolutelyContinuousOnInterval F a b :=
    constant_continuation_absolutelyContinuous ha.le hb hfc hfd hg
  have hFc : ContinuousOn F (Icc a b) := by
    simpa only [uIcc_of_le hab] using hFAC.continuousOn
  let n : C(Icc a b, ℝ) := ⟨fun w => -Real.exp (z w u 2) * F w,
    (by
      have hc : Continuous (fun w : Icc a b => F w) := continuousOn_iff_continuous_domRestrict.mp hFc
      exact (by fun_prop : Continuous (fun w : Icc a b => -Real.exp (z w u 2))).mul hc)⟩
  have hne (w : ℝ) : intervalExtension hab n w = -Real.exp (ze w u 2) * F (projIcc a b hab w) := rfl
  have hnmem (w : ℝ) (hw : w ∈ Icc a b) :
      intervalExtension hab n w = -Real.exp (ze w u 2) * F w := by
    rw [hne, projIcc_of_mem hab hw]
  have hfuture (w : ℝ) (hw : w ∈ Icc a b) (hw0 : 0 ≤ w) :
      ze w u 2 = Ψ 0 u 2 ∧ F w = O u := by
    rw [intervalExtension_apply, projIcc_of_mem hab hw, hz.2.2.1 _ hw0]
    constructor
    · change Ψ 0 u 2 + w * (0 : ℝ) = Ψ 0 u 2
      ring
    · simp only [F, min_eq_right hw0, f, compactifiedOpticalRow, Function.update_self]
  have hqe : radialHorizonVelocity hεU Z O u 0 = -Real.exp (Ψ 0 u 2) * O u := by
    change -(Real.exp (-Z ⟨U, hεU, le_rfl⟩ 2) * Real.exp (Z u 2)) * O u = _
    simp only [Ψ, compactifiedWaveRow, Function.update_self, waveNormalize_apply, Pi.sub_apply, ite_true]
    rw [Real.exp_sub, Real.exp_neg]
    ring
  have hpa := (ae_restrict_iff' measurableSet_Icc).1 hz.2.2.2.1
  have hfu := (ae_restrict_iff' measurableSet_Ioc).1 hz.2.2.2.2.1
  have hn : ∀ᵐ w ∂volume.restrict (Icc a b), d w u 0 = n (projIcc a b hab w) := by
    filter_upwards [ae_restrict_of_ae hpa, ae_restrict_of_ae hfu,
      ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc a b)).ae_ne 0] with w hp hf hw hw0
    change d w u 0 = intervalExtension hab n w
    rw [hnmem w hw]
    by_cases hwneg : w < 0
    · rw [hp ⟨hw.1, hwneg.le⟩, hpast w ⟨hw.1, hwneg.le⟩]
      change Q w u 0 = -Real.exp (Ψ w u 2) * f (min w 0)
      rw [min_eq_left hwneg.le]
      exact ((hO u).2 w ⟨hVa.trans_le hw.1, hwneg⟩).2
    · have hwpos : 0 < w := lt_of_le_of_ne (le_of_not_gt hwneg) (Ne.symm hw0)
      rw [hf ⟨hwpos, hw.2⟩, (hfuture w hw hwpos.le).1, (hfuture w hw hwpos.le).2, hqe]
  have hzAC : AbsolutelyContinuousOnInterval ze a b := by
    change AbsolutelyContinuousOnInterval (intervalExtension hab z) a b
    rw [hz.1.choose_spec, map_add]
    exact horizontalPrimitive_absolutelyContinuous hab d (Ψ a)
  let E : C(Icc ε U, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ u)
  have heAC : AbsolutelyContinuousOnInterval (fun w => -Real.exp (ze w u 2)) a b :=
    absolutelyContinuous_comp_contDiffAt hzAC (g := fun x => -Real.exp (E x))
      (fun _ _ => (Real.contDiff_exp.contDiffAt.comp _ E.contDiff.contDiffAt).neg)
  have hnAC : AbsolutelyContinuousOnInterval (intervalExtension hab n) a b := by
    apply absolutelyContinuous_of_dist_le (heAC.mul hFAC) (K := 1) zero_le_one
    intro s hs t ht
    rw [uIcc_of_le hab] at hs ht
    rw [hnmem s hs, hnmem t ht, one_mul]
    exact le_rfl
  have hzd : ∀ᵐ w ∂volume.restrict (Icc a b), HasDerivWithinAt ze (d w) (Icc a b) w := by
    rw [show ze = intervalExtension hab z from rfl, hz.1.choose_spec, map_add]
    filter_upwards [horizontalPrimitive_ae_hasDerivWithinAt hab d] with w hw
    exact hw.const_add (Ψ a)
  refine ⟨n, hn, hnAC, ?_⟩
  filter_upwards [hzd, ae_restrict_of_ae hpa, ae_restrict_of_ae hfu,
    ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc a b)).ae_ne a,
    (volume.restrict (Icc a b)).ae_ne 0] with w hd hp hf hw hwa hw0
  have hdell := E.hasFDerivAt.comp_hasDerivWithinAt w hd
  have hdf : HasDerivAt F (ze w u 0 * Real.exp (-ze w u 2) * (d w u 1) ^ 2) w := by
    by_cases hwneg : w < 0
    · rw [hp ⟨hw.1, hwneg.le⟩]
      apply (hfd w ⟨lt_of_le_of_ne hw.1 (Ne.symm hwa), hwneg⟩).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds hwneg] with x hx
      exact congrArg f (min_eq_left hx.le)
    · have hwpos : 0 < w := lt_of_le_of_ne (le_of_not_gt hwneg) (Ne.symm hw0)
      rw [hf ⟨hwpos, hw.2⟩]
      change HasDerivAt F (ze w u 0 * Real.exp (-ze w u 2) * (0 : ℝ) ^ 2) w
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
      apply (hasDerivAt_const w (f 0)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hwpos] with x hx
      exact congrArg f (min_eq_right hx.le)
  have hh := (hdell.exp.neg.mul hdf.hasDerivWithinAt).congr_of_mem (f₁ := intervalExtension hab n)
    (fun x hx => hnmem x hx) hw
  apply hh.congr_deriv
  change - (Real.exp (ze w u 2) * (d w u 2)) * F w +
    (-Real.exp (ze w u 2)) * (ze w u 0 * Real.exp (-ze w u 2) * (d w u 1) ^ 2) = _
  change _ = d w u 2 * intervalExtension hab n w - ze w u 0 * (d w u 1) ^ 2
  rw [hnmem w hw, Real.exp_neg]
  field_simp
  ring

end CauchyHorizon
