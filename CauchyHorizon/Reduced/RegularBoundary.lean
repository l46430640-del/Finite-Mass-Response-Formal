import CauchyHorizon.Reduced.TransverseContinuity
import CauchyHorizon.Reduced.RegularWave

/-! The normalized field and its actual transverse derivative extend continuously to regular time zero. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def waveNormalize {K : Type*} [TopologicalSpace K] [CompactSpace K] (u₀ : K) :
    C(K, WaveVector) →L[ℝ] C(K, WaveVector) :=
  ContinuousLinearMap.id ℝ _ - (ContinuousLinearMap.const ℝ K).comp
    (ContinuousLinearMap.pi (fun i : Fin 3 => if i = 2 then
      (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).comp
        (ContinuousMap.evalCLM ℝ u₀ : C(K, WaveVector) →L[ℝ] WaveVector) else 0))

@[simp] theorem waveNormalize_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (u₀ : K) (Z : C(K, WaveVector)) (u : K) :
    waveNormalize u₀ Z u = Z u - (fun i => if i = 2 then Z u₀ 2 else 0) := by
  ext i
  by_cases hi : i = 2 <;> simp [waveNormalize, hi]

noncomputable def compactifiedWaveRow {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ) (Z : C(Icc ε U, WaveVector)) :
    ℝ → C(Icc ε U, WaveVector) :=
  Function.update (fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (renormalizedWaveRow hε 0 X (χ w)))
    0 (waveNormalize ⟨U, hεU, le_rfl⟩ Z)

noncomputable def compactifiedTransverseRow {U ε : ℝ} (χ : ℝ → ℝ)
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector)) :
    ℝ → C(Icc ε U, WaveVector) := Function.update (fun w => D (χ w)) 0 Dh

def IsRegularWaveBoundary {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector)) : Prop :=
  let a := anchoringLapse (hε.trans hεU) X
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let W := compactifiedTransverseRow χ D Dh
  (∀ (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (u : Icc ε U),
    Ψ (regularTime a t) u =
      (X T).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht.le, htT⟩ -
        (fun i => if i = 2 then (X T).1 ⟨U, hε.trans hεU, le_rfl⟩ ⟨t, ht.le, htT⟩ 2 else 0)) ∧
  (∀ w ∈ Ioo (regularTime a 0) 0,
    HasDerivAt Ψ (waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)) w) ∧
  ContinuousOn Ψ (Ioc (regularTime a 0) 0) ∧
  ContinuousOn W (Ioc (regularTime a 0) 0) ∧
  ∀ w ∈ Ioc (regularTime a 0) 0, ∀ u : Icc ε U,
    HasDerivWithinAt (intervalExtension hεU (Ψ w)) (W w u) (Icc ε U) u

set_option maxHeartbeats 1000000 in
theorem regular_wave_boundary {U ε k : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hderiv : ∀ (T : Ici (0 : ℝ)) (v : ℝ) (hv : v ∈ Icc 0 (T : ℝ)),
      HasDerivWithinAt (intervalExtension T.property (flipRectangle (X T).1))
        (flipRectangle (X T).2.1 ⟨v, hv⟩) (Icc 0 (T : ℝ)) v)
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hZ : Tendsto (renormalizedWaveRow hε k X) atTop (𝓝 Z))
    (hB : IsTransverseWaveBoundary (hε.trans hεU) hεU X χ Z D Dh)
    (hDc : ContinuousOn D (Ici 0)) : IsRegularWaveBoundary hε hεU X χ Z D Dh := by
  let a := anchoringLapse (hε.trans hεU) X
  let N := waveNormalize (⟨U, hεU, le_rfl⟩ : Icc ε U)
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let W := compactifiedTransverseRow χ D Dh
  obtain ⟨_hfiniteVel, hwd, _hwc⟩ := regular_wave_derivative hε hεU X hX hderiv hχ
  obtain ⟨_hac, _hp, _hi, _hm, _hd, hneg, _hVtop, _himage, hχc, hχtop, hright, hleft⟩ := hχ
  have hΨ (w : ℝ) (hw : w ≠ 0) : Ψ w = N (renormalizedWaveRow hε 0 X (χ w)) :=
    Function.update_of_ne hw _ _
  have hW (w : ℝ) (hw : w ≠ 0) : W w = D (χ w) := Function.update_of_ne hw _ _
  have hfinite (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (u : Icc ε U) :
      Ψ (regularTime a t) u =
        (X T).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht.le, htT⟩ -
          (fun i => if i = 2 then (X T).1 ⟨U, hε.trans hεU, le_rfl⟩ ⟨t, ht.le, htT⟩ 2 else 0) := by
    rw [hΨ _ (hneg t).ne, hleft t ht]
    simp only [N, waveNormalize_apply]
    ext i
    change renormalizedWaveRow hε 0 X t u i -
      (if i = 2 then renormalizedWaveRow hε 0 X t ⟨U, hεU, le_rfl⟩ 2 else 0) = _
    rw [renormalizedWaveRow_apply hε X hX T ht.le htT u i,
      renormalizedWaveRow_apply hε X hX T ht.le htT ⟨U, hεU, le_rfl⟩ 2]
    simp only [mul_zero, zero_mul, ite_self, add_zero, Pi.sub_apply]
  have hΨd (w : ℝ) (hw : w ∈ Ioo (regularTime a 0) 0) :
      HasDerivAt Ψ (N (regularWaveVelocityRow hε hεU X χ w)) w := by
    apply (N.hasFDerivAt.comp_hasDerivAt w (hwd w hw)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hw.2] with z hz
    exact hΨ z hz.ne
  have hcancel (t : ℝ) : N (renormalizedWaveRow hε k X t) = N (renormalizedWaveRow hε 0 X t) := by
    apply ContinuousMap.ext
    intro u
    simp only [N, waveNormalize_apply]
    ext i
    change renormalizedWaveRow hε k X t u i -
      (if i = 2 then renormalizedWaveRow hε k X t ⟨U, hεU, le_rfl⟩ 2 else 0) =
      renormalizedWaveRow hε 0 X t u i -
        (if i = 2 then renormalizedWaveRow hε 0 X t ⟨U, hεU, le_rfl⟩ 2 else 0)
    simp only [renormalizedWaveRow, ContinuousMap.coe_mk, Pi.add_apply,
      ite_true, mul_zero, zero_mul, ite_self, add_zero]
    split_ifs <;> ring
  have hlim : Tendsto (fun w => N (renormalizedWaveRow hε 0 X (χ w))) (𝓝[<] (0 : ℝ)) (𝓝 (N Z)) :=
    (((N.continuous.tendsto Z).comp hZ).comp hχtop).congr' (Eventually.of_forall (fun w => hcancel (χ w)))
  have hΨzero : ContinuousWithinAt Ψ (Iic 0) 0 := by
    change ContinuousWithinAt (Function.update _ 0 (N Z)) (Iic 0) 0
    rw [continuousWithinAt_update_same, Iic_sdiff_right]
    exact hlim
  have hWzero : ContinuousWithinAt W (Iic 0) 0 := by
    change ContinuousWithinAt (Function.update _ 0 Dh) (Iic 0) 0
    rw [continuousWithinAt_update_same, Iic_sdiff_right]
    exact hB.2.2.1
  have hWc : ContinuousOn (fun w => D (χ w)) (Ioo (regularTime a 0) 0) :=
    hDc.comp hχc (fun w hw => (hright w hw).1.le)
  refine ⟨hfinite, hΨd, ?_, ?_, ?_⟩
  · intro w hw
    by_cases hw0 : w = 0
    · subst w
      exact hΨzero.mono Ioc_subset_Iic_self
    · exact (hΨd w ⟨hw.1, lt_of_le_of_ne hw.2 hw0⟩).continuousAt.continuousWithinAt
  · intro w hw
    by_cases hw0 : w = 0
    · subst w
      exact hWzero.mono Ioc_subset_Iic_self
    · apply ContinuousAt.continuousWithinAt
      change ContinuousAt (Function.update _ 0 Dh) w
      rw [continuousAt_update_of_ne hw0]
      exact (hWc w ⟨hw.1, lt_of_le_of_ne hw.2 hw0⟩).continuousAt
        (isOpen_Ioo.mem_nhds ⟨hw.1, lt_of_le_of_ne hw.2 hw0⟩)
  · intro w hw u
    change HasDerivWithinAt (intervalExtension hεU (Ψ w)) (W w u) (Icc ε U) u
    by_cases hw0 : w = 0
    · subst w
      simp only [Ψ, W, compactifiedWaveRow, compactifiedTransverseRow, Function.update_self]
      change HasDerivWithinAt (fun x => waveNormalize ⟨U, hεU, le_rfl⟩ Z
        (projIcc ε U hεU x)) (Dh u) (Icc ε U) u
      simpa only [intervalExtension_apply, waveNormalize_apply] using
        (hB.2.2.2 u).sub_const (fun i => if i = 2 then Z ⟨U, hεU, le_rfl⟩ 2 else 0)
    · have hw' : w ∈ Ioo (regularTime a 0) 0 := ⟨hw.1, lt_of_le_of_ne hw.2 hw0⟩
      have ht := (hright w hw').1
      let T : Ici (0 : ℝ) := ⟨χ w, ht.le⟩
      rw [hW w hw0]
      have hd := ((hB.1 T (χ w) ht.le le_rfl u).sub_const
        (fun i => if i = 2 then (X T).1 ⟨U, hε.trans hεU, le_rfl⟩ ⟨χ w, ht.le, le_rfl⟩ 2 else 0)).mono
          (Icc_subset_Icc hε le_rfl)
      apply hd.congr_of_mem _ u.property
      intro x hx
      have hfield := hfinite T (χ w) ht le_rfl ⟨x, hx⟩
      rw [(hright w hw').2.1] at hfield
      rw [intervalExtension_apply, projIcc_of_mem hεU hx, hfield]
      rw [intervalExtension_apply, projIcc_of_mem (hε.trans hεU)
        (show x ∈ Icc 0 U from ⟨hε.trans hx.1, hx.2⟩)]

end CauchyHorizon
