import CauchyHorizon.Reduced.RegularContinuationData
import CauchyHorizon.Analysis.PrimitiveContinuity

/-! The optical constraint in regular time retains its actual continuous horizon value. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def compactifiedOpticalRow {U ε : ℝ} (hε : 0 ≤ ε)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ) (O : C(Icc ε U, ℝ)) :
    ℝ → C(Icc ε U, ℝ) := Function.update (fun w => opticalRow hε X (χ w)) 0 O

def IsRegularOpticalConstraint {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ)) : Prop :=
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let Q := fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)
  let D := compactifiedOpticalRow hε X χ O
  ∀ u : Icc ε U, ContinuousOn (fun w => D w u) (Ioc (V 0) 0) ∧
    ∀ w ∈ Ioo (V 0) 0,
      HasDerivAt (fun s => D s u) (Ψ w u 0 * Real.exp (-Ψ w u 2) * (Q w u 1) ^ 2) w ∧
      Q w u 0 = -Real.exp (Ψ w u 2) * D w u

set_option maxHeartbeats 1000000 in
theorem regular_optical_constraint {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hderiv : ∀ (S : Ici (0 : ℝ)) (v : ℝ) (hv : v ∈ Icc 0 (S : ℝ)),
      HasDerivWithinAt (intervalExtension S.property (flipRectangle (X S).1))
        (flipRectangle (X S).2.1 ⟨v, hv⟩) (Icc 0 (S : ℝ)) v)
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {Du : ℝ → C(Icc ε U, WaveVector)} {Duh : C(Icc ε U, WaveVector)}
    (hB : IsRegularWaveBoundary hε hεU X χ Z Du Duh)
    {O : C(Icc ε U, ℝ)} (hO : Tendsto (opticalRow hε X) atTop (𝓝 O))
    (hflux : ∀ (S : Ici (0 : ℝ)) (u : Icc 0 U) (v : Icc 0 (S : ℝ)),
      (X S).2.1 u v 0 * Real.exp (-(X S).1 u v 2) =
        (X S).2.1 u ⟨0, le_rfl, S.property⟩ 0 * Real.exp (-(X S).1 u ⟨0, le_rfl, S.property⟩ 2) -
          ∫ t in (0 : ℝ)..v, intervalExtension S.property ((X S).1 u) t 0 *
            Real.exp (-intervalExtension S.property ((X S).1 u) t 2) *
              (intervalExtension S.property ((X S).2.1 u) t 1) ^ 2) :
    IsRegularOpticalConstraint hε hεU X χ Z O := by
  let a := anchoringLapse (hε.trans hεU) X
  let V := regularTime a
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let Q := fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)
  let D := compactifiedOpticalRow hε X χ O
  have hv := (regular_wave_derivative hε hεU X hX hderiv hχ).1
  intro u
  have hlocal (w : ℝ) (hw : w ∈ Ioo (V 0) 0) :
      HasDerivAt (fun s => D s u) (Ψ w u 0 * Real.exp (-Ψ w u 2) * (Q w u 1) ^ 2) w ∧
      Q w u 0 = -Real.exp (Ψ w u 2) * D w u := by
    obtain ⟨ht, he, hdχ⟩ := hχ.2.2.2.2.2.2.2.2.2.2.1 w hw
    let S : Ici (0 : ℝ) := ⟨χ w + 1, by change 0 ≤ χ w + 1; linarith⟩
    have htS : χ w < S := lt_add_one _
    let v : Icc 0 (S : ℝ) := ⟨χ w, ht.le, htS.le⟩
    let j : Icc 0 U := ⟨u, hε.trans u.property.1, u.property.2⟩
    let z := (X S).1 j v
    let p := (X S).2.1 j v
    let F : C(Icc 0 (S : ℝ), ℝ) := ⟨fun t => (X S).1 j t 0 *
      Real.exp (-(X S).1 j t 2) * ((X S).2.1 j t 1) ^ 2, by fun_prop⟩
    let C := -(X S).2.1 j ⟨0, le_rfl, S.property⟩ 0 *
      Real.exp (-(X S).1 j ⟨0, le_rfl, S.property⟩ 2)
    have hprim (t : ℝ) (ht : t ∈ Icc 0 (S : ℝ)) :
        opticalRow hε X t u = C + intervalExtension S.property (continuousPrimitive S.property F) t := by
      rw [opticalRow_apply hε X hX S ht.1 ht.2 u]
      change -(X S).2.1 j ⟨t, ht⟩ 0 / Real.exp ((X S).1 j ⟨t, ht⟩ 2) =
        C + continuousPrimitive S.property F (projIcc 0 (S : ℝ) S.property t)
      rw [projIcc_of_mem S.property ht]
      have hh := hflux S j ⟨t, ht⟩
      change _ = C + ∫ s in (0 : ℝ)..t, intervalExtension S.property F s
      change (X S).2.1 j ⟨t, ht⟩ 0 * Real.exp (-(X S).1 j ⟨t, ht⟩ 2) =
        (X S).2.1 j ⟨0, le_rfl, S.property⟩ 0 * Real.exp (-(X S).1 j ⟨0, le_rfl, S.property⟩ 2) -
        ∫ s in (0 : ℝ)..t, intervalExtension S.property F s at hh
      dsimp only [C]
      simp only [Real.exp_neg, ← div_eq_mul_inv, neg_div] at hh ⊢
      linarith only [hh]
    have hd := ((continuousPrimitive_hasDerivWithinAt S.property F v.property).const_add C).hasDerivAt
      (Icc_mem_nhds ht htS)
    have hraw : HasDerivAt (fun t => opticalRow hε X t u) (F v) (χ w) := by
      apply hd.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds ht, eventually_lt_nhds htS] with t ht htS
      exact hprim t ⟨ht.le, htS.le⟩
    have hD : D w u = -p 0 / Real.exp (z 2) := by
      change compactifiedOpticalRow hε X χ O w u = _
      rw [compactifiedOpticalRow, Function.update_of_ne hw.2.ne]
      exact opticalRow_apply hε X hX S ht.le htS.le u
    have ha : a (χ w) = Real.exp ((X S).1 ⟨U, hε.trans hεU, le_rfl⟩ v 2) := by
      dsimp only [a, anchoringLapse]
      rw [max_eq_right ht.le, renormalizedWaveRow_apply (hε.trans hεU) X hX S ht.le htS.le
        ⟨U, le_rfl, le_rfl⟩ 2]
      simp only [ite_true, mul_zero, zero_mul, add_zero]
      rfl
    have hΨ := hB.1 S (χ w) ht htS.le u
    rw [he] at hΨ
    have hz0 : Ψ w u 0 = z 0 := by
      simpa only [Pi.sub_apply, if_neg (by decide : (0 : Fin 3) ≠ 2), sub_zero] using
        congrArg (fun z : WaveVector => z 0) hΨ
    have hze : Real.exp (Ψ w u 2) = Real.exp (z 2) / a (χ w) := by
      have hh := congrArg (fun z : WaveVector => z 2) hΨ
      simp only [Pi.sub_apply, ite_true] at hh
      rw [hh, Real.exp_sub, ha]
    have hq (i : Fin 3) (hi : i ≠ 2) : Q w u i = p i / a (χ w) := by
      change waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w) u i = _
      rw [waveNormalize_apply]
      simp only [Pi.sub_apply, if_neg hi, sub_zero]
      have hh := hv S (χ w) ht htS.le u i
      rw [he] at hh
      exact hh
    constructor
    · have hh := (hraw.comp w hdχ).congr_of_eventuallyEq (f₁ := fun s => D s u) (by
        filter_upwards [eventually_lt_nhds hw.2] with s hs
        change compactifiedOpticalRow hε X χ O s u = opticalRow hε X (χ s) u
        rw [compactifiedOpticalRow, Function.update_of_ne hs.ne])
      apply hh.congr_deriv
      rw [hz0, Real.exp_neg, hze, hq 1 (by decide)]
      change (z 0 * Real.exp (-z 2) * (p 1) ^ 2) * (1 / a (χ w)) = _
      rw [Real.exp_neg]
      field_simp [(hχ.2.1 (χ w)).ne']
    · rw [hq 0 (by decide), hze, hD]
      field_simp
  refine ⟨?_, hlocal⟩
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    have he : (fun w => D w u) = Function.update (fun w => opticalRow hε X (χ w) u) 0 (O u) := by
      funext w
      by_cases hw : w = 0 <;> simp [D, compactifiedOpticalRow, hw]
    rw [he]
    have hc : ContinuousWithinAt (Function.update (fun w => opticalRow hε X (χ w) u) 0 (O u))
        (Iic 0) 0 := by
      rw [continuousWithinAt_update_same, Iic_sdiff_right]
      exact ((ContinuousMap.evalCLM ℝ u : C(Icc ε U, ℝ) →L[ℝ] ℝ).continuous.tendsto O).comp
        (hO.comp hχ.2.2.2.2.2.2.2.2.2.1)
    exact hc.mono Ioc_subset_Iic_self
  · exact (hlocal w ⟨hw.1, lt_of_le_of_ne hw.2 hw0⟩).1.continuousAt.continuousWithinAt

end CauchyHorizon
