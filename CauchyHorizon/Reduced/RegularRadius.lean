import CauchyHorizon.Reduced.RegularWave
import CauchyHorizon.Reduced.OpticalBoundary
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! The physical radius is differentiable in regular time, including its one-sided horizon trace. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def waveRadius {K : Type*} [TopologicalSpace K] [CompactSpace K] :
    C(K, WaveVector) →L[ℝ] C(K, ℝ) :=
  ContinuousLinearMap.compLeftContinuous ℝ K (ContinuousLinearMap.proj (0 : Fin 3))

noncomputable def compactifiedRadiusRow {U ε : ℝ} (hε : 0 ≤ ε)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ) (Rh : C(Icc ε U, ℝ)) :
    ℝ → C(Icc ε U, ℝ) :=
  Function.update (fun w => waveRadius (renormalizedWaveRow hε 0 X (χ w))) 0 Rh

def IsRegularRadiusBoundary {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (k : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, ℝ)) : Prop :=
  let a := anchoringLapse (hε.trans hεU) X
  let R := compactifiedRadiusRow hε X χ (waveRadius Z)
  let Rv := -(anchoredAmplitude ⟨U, hεU, le_rfl⟩ Z) * Dh
  (∀ (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (u : Icc ε U),
    R (regularTime a t) u = (X T).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht.le, htT⟩ 0) ∧
  (∀ w ∈ Ioo (regularTime a 0) 0,
    HasDerivAt R (lapseNormalizedRadialRow hε hεU k X (χ w)) w) ∧
  Tendsto R (𝓝[<] (0 : ℝ)) (𝓝 (waveRadius Z)) ∧
  HasDerivWithinAt R Rv (Iic 0) 0 ∧
  Tendsto (deriv R) (𝓝[<] (0 : ℝ)) (𝓝 Rv) ∧
  ContinuousOn R (Ioc (regularTime a 0) 0) ∧
  ContinuousOn (Function.update (deriv R) 0 Rv) (Ioc (regularTime a 0) 0)

set_option maxHeartbeats 800000 in
theorem regular_radius_boundary {U ε k : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hderiv : ∀ (T : Ici (0 : ℝ)) (v : ℝ) (hv : v ∈ Icc 0 (T : ℝ)),
      HasDerivWithinAt (intervalExtension T.property (flipRectangle (X T).1))
        (flipRectangle (X T).2.1 ⟨v, hv⟩) (Icc 0 (T : ℝ)) v)
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, ℝ)}
    (hZ : Tendsto (renormalizedWaveRow hε k X) atTop (𝓝 Z))
    (hD : Tendsto (opticalRow hε X) atTop (𝓝 Dh)) :
    IsRegularRadiusBoundary hε hεU k X χ Z Dh := by
  let a := anchoringLapse (hε.trans hεU) X
  let R := compactifiedRadiusRow hε X χ (waveRadius Z)
  let Rv := -(anchoredAmplitude ⟨U, hεU, le_rfl⟩ Z) * Dh
  obtain ⟨hfinite, hwd, hwc⟩ := regular_wave_derivative hε hεU X hX hderiv hχ
  obtain ⟨_hac, _hapos, _hai, _hmono, _hVd, hVneg, _hVtop, _himage,
    _hχc, hχtop, hχright, hχleft⟩ := hχ
  have hvelocity (w : ℝ) (hw : w ∈ Ioo (regularTime a 0) 0) :
      waveRadius (regularWaveVelocityRow hε hεU X χ w) = lapseNormalizedRadialRow hε hεU k X (χ w) := by
    obtain ⟨ht, he, _hdχ⟩ := hχright w hw
    let T : Ici (0 : ℝ) := ⟨χ w, ht.le⟩
    have ha : a (χ w) = Real.exp ((X T).1 ⟨U, hε.trans hεU, le_rfl⟩ ⟨χ w, ht.le, le_rfl⟩ 2) := by
      dsimp only [a, anchoringLapse]
      rw [max_eq_right ht.le,
        renormalizedWaveRow_apply (hε.trans hεU) X hX T ht.le le_rfl ⟨U, le_rfl, le_rfl⟩ 2]
      simp only [ite_true, mul_zero, zero_mul, add_zero]
    ext u
    have hh := hfinite T (χ w) ht le_rfl u 0
    rw [he] at hh
    change regularWaveVelocityRow hε hεU X χ w u 0 = _
    rw [hh, (lapse_normalized_radial_limit hε hεU X hX hZ hD).1 T (χ w) ht.le le_rfl u]
    change _ / a (χ w) = _
    rw [ha]
  have hR (w : ℝ) (hw : w ≠ 0) :
      R w = waveRadius (renormalizedWaveRow hε 0 X (χ w)) :=
    Function.update_of_ne hw _ _
  have hRd (w : ℝ) (hw : w ∈ Ioo (regularTime a 0) 0) :
      HasDerivAt R (lapseNormalizedRadialRow hε hεU k X (χ w)) w := by
    have hd := waveRadius.hasFDerivAt.comp_hasDerivAt w (hwd w hw)
    have he : R =ᶠ[𝓝 w] fun z => waveRadius (renormalizedWaveRow hε 0 X (χ z)) := by
      filter_upwards [eventually_lt_nhds hw.2] with z hz
      exact hR z hz.ne
    exact (hd.congr_of_eventuallyEq he).congr_deriv (hvelocity w hw)
  have hdcont (w : ℝ) (hw : w ∈ Ioo (regularTime a 0) 0) : ContinuousAt (deriv R) w := by
    have hc : ContinuousAt (fun z => waveRadius (regularWaveVelocityRow hε hεU X χ z)) w :=
      waveRadius.continuous.continuousAt.comp ((hwc w hw).continuousAt (isOpen_Ioo.mem_nhds hw))
    apply hc.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hw] with z hz
    rw [(hRd z hz).deriv, hvelocity z hz]
  have hRlimit : Tendsto R (𝓝[<] (0 : ℝ)) (𝓝 (waveRadius Z)) := by
    have hh := ((waveRadius.continuous.tendsto Z).comp hZ).comp hχtop
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hR w (show w ≠ 0 from (show w < 0 from hw).ne)]
    ext u
    change renormalizedWaveRow hε k X (χ w) u 0 = renormalizedWaveRow hε 0 X (χ w) u 0
    simp only [renormalizedWaveRow, ContinuousMap.coe_mk, Pi.add_apply,
      if_neg (by decide : (0 : Fin 3) ≠ 2)]
  have hdomain : Ioo (regularTime a 0) 0 ∈ 𝓝[<] (0 : ℝ) :=
    Ioo_mem_nhdsLT (hVneg 0)
  have hRderivLimit : Tendsto (deriv R) (𝓝[<] (0 : ℝ)) (𝓝 Rv) := by
    apply ((lapse_normalized_radial_limit hε hεU X hX hZ hD).2.comp hχtop).congr'
    filter_upwards [hdomain] with w hw
    exact (hRd w hw).deriv.symm
  have hRhd : HasDerivWithinAt R Rv (Iic 0) 0 := by
    apply hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun w hw => (hRd w hw).differentiableAt.differentiableWithinAt) _ hdomain hRderivLimit
    have hc : ContinuousWithinAt R (Iio 0) 0 := by
      change Tendsto R (𝓝[<] (0 : ℝ)) (𝓝 (R 0))
      simpa only [R, compactifiedRadiusRow, Function.update_self] using hRlimit
    exact hc.mono Ioo_subset_Iio_self
  refine ⟨?_, hRd, hRlimit, hRhd, hRderivLimit, ?_, ?_⟩
  · intro T t ht htT u
    change R (regularTime a t) u = _
    rw [hR _ (hVneg t).ne, hχleft t ht]
    change renormalizedWaveRow hε 0 X t u 0 = _
    rw [renormalizedWaveRow_apply hε X hX T ht.le htT u 0]
    simp only [if_neg (by decide : (0 : Fin 3) ≠ 2), add_zero]
  · intro w hw
    by_cases hw0 : w = 0
    · subst w
      exact hRhd.continuousWithinAt.mono Ioc_subset_Iic_self
    · exact (hRd w ⟨hw.1, lt_of_le_of_ne hw.2 hw0⟩).continuousAt.continuousWithinAt
  · intro w hw
    by_cases hw0 : w = 0
    · subst w
      have hc : ContinuousWithinAt (Function.update (deriv R) 0 Rv) (Iic 0) 0 := by
        rw [continuousWithinAt_update_same, Iic_sdiff_right]
        exact hRderivLimit
      exact hc.mono Ioc_subset_Iic_self
    · apply ContinuousAt.continuousWithinAt
      rw [continuousAt_update_of_ne hw0]
      exact hdcont w ⟨hw.1, lt_of_le_of_ne hw.2 hw0⟩

end CauchyHorizon
