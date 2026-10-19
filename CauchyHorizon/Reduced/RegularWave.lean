import CauchyHorizon.Reduced.RegularTime
import CauchyHorizon.Reduced.LongitudinalFlux

/-! The actual longitudinal derivative in regular time, in the continuous incoming norm. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def regularWaveVelocityRow {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ) (w : ℝ) : C(Icc ε U, WaveVector) :=
  let T : Ici (0 : ℝ) := ⟨max 0 (χ w), le_max_left (0 : ℝ) (χ w)⟩
  (1 / anchoringLapse (hε.trans hεU) X (χ w)) •
    ⟨fun u => (X T).2.1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨T, T.property, le_rfl⟩, by fun_prop⟩

set_option maxHeartbeats 800000 in
theorem regular_wave_derivative {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hderiv : ∀ (T : Ici (0 : ℝ)) (v : ℝ) (hv : v ∈ Icc 0 (T : ℝ)),
      HasDerivWithinAt (intervalExtension T.property (flipRectangle (X T).1))
        (flipRectangle (X T).2.1 ⟨v, hv⟩) (Icc 0 (T : ℝ)) v)
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ) :
    let a := anchoringLapse (hε.trans hεU) X
    (∀ (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (u : Icc ε U) (i : Fin 3),
      regularWaveVelocityRow hε hεU X χ (regularTime a t) u i =
        (X T).2.1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht.le, htT⟩ i / a t) ∧
    (∀ w ∈ Ioo (regularTime a 0) 0,
      HasDerivAt (fun z => renormalizedWaveRow hε 0 X (χ z)) (regularWaveVelocityRow hε hεU X χ w) w) ∧
    ContinuousOn (regularWaveVelocityRow hε hεU X χ) (Ioo (regularTime a 0) 0) := by
  let a := anchoringLapse (hε.trans hεU) X
  let J : C(Icc ε U, Icc 0 U) := ⟨fun u => ⟨u, hε.trans u.property.1, u.property.2⟩, by fun_prop⟩
  let Q : C(Icc 0 U, WaveVector) →L[ℝ] C(Icc ε U, WaveVector) := ContinuousMap.compCLM ℝ WaveVector J
  obtain ⟨hac, hp, _hi, _hm, _hd, _hn, _hl, _himage, _hχc, _hχl, hright, hleft⟩ := hχ
  have hv (T : Ici (0 : ℝ)) {w : ℝ} (ht : 0 ≤ χ w) (htT : χ w ≤ T) :
      regularWaveVelocityRow hε hεU X χ w =
        (1 / a (χ w)) • Q (intervalExtension T.property (flipRectangle (X T).2.1) (χ w)) := by
    ext u i
    have he := congrArg (fun x : WaveState U (max 0 (χ w)) =>
      x.2.1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨max 0 (χ w), le_max_left (0 : ℝ) (χ w), le_rfl⟩ i)
      (hX ⟨max 0 (χ w), le_max_left (0 : ℝ) (χ w)⟩ T (max_le T.property htT))
    change (X T).2.1 ⟨0 + (u : ℝ), by simpa using hε.trans u.property.1, by simpa using u.property.2⟩
        ⟨0 + max 0 (χ w), by simp, by simpa using max_le T.property htT⟩ i =
      (X ⟨max 0 (χ w), le_max_left (0 : ℝ) (χ w)⟩).2.1
        ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨max 0 (χ w), le_max_left (0 : ℝ) (χ w), le_rfl⟩ i at he
    simp only [zero_add, max_eq_right ht] at he
    change (1 / a (χ w)) * (X ⟨max 0 (χ w), le_max_left (0 : ℝ) (χ w)⟩).2.1
        ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨max 0 (χ w), le_max_left (0 : ℝ) (χ w), le_rfl⟩ i =
      (1 / a (χ w)) * (X T).2.1 (J u) (projIcc 0 (T : ℝ) T.property (χ w)) i
    simp only [max_eq_right ht, projIcc_of_mem T.property (show χ w ∈ Icc 0 (T : ℝ) from ⟨ht, htT⟩)]
    exact congrArg (fun y => (1 / a (χ w)) * y) he.symm
  have hraw (T : Ici (0 : ℝ)) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
      renormalizedWaveRow hε 0 X t = Q (intervalExtension T.property (flipRectangle (X T).1) t) := by
    ext u i
    change renormalizedWaveRow hε 0 X t u i = (X T).1 (J u) (projIcc 0 (T : ℝ) T.property t) i
    rw [renormalizedWaveRow_apply hε X hX T ht htT u i,
      projIcc_of_mem T.property (show t ∈ Icc 0 (T : ℝ) from ⟨ht, htT⟩)]
    simp only [mul_zero, zero_mul, ite_self, add_zero]
    rfl
  have hlocal (w : ℝ) (hw : w ∈ Ioo (regularTime a 0) 0) :
      HasDerivAt (fun z => renormalizedWaveRow hε 0 X (χ z)) (regularWaveVelocityRow hε hεU X χ w) w ∧
        ContinuousAt (regularWaveVelocityRow hε hεU X χ) w := by
    obtain ⟨ht, _he, hdχ⟩ := hright w hw
    let T : Ici (0 : ℝ) := ⟨χ w + 1, by change 0 ≤ χ w + 1; linarith only [ht]⟩
    have htT : χ w < T := lt_add_one _
    have hnear : ∀ᶠ z in 𝓝 w, χ z ∈ Ioo 0 (T : ℝ) :=
      hdχ.continuousAt.preimage_mem_nhds (Ioo_mem_nhds ht htT)
    constructor
    · have hh := (Q.hasFDerivAt.comp_hasDerivAt (χ w)
        ((hderiv T (χ w) ⟨ht.le, htT.le⟩).hasDerivAt (Icc_mem_nhds ht htT))).scomp w hdχ
      have he : (fun z => renormalizedWaveRow hε 0 X (χ z)) =ᶠ[𝓝 w]
          fun z => Q (intervalExtension T.property (flipRectangle (X T).1) (χ z)) :=
        hnear.mono (fun z hz => hraw T hz.1.le hz.2.le)
      apply (hh.congr_of_eventuallyEq he).congr_deriv
      rw [hv T ht.le htT.le]
      change _ = (1 / a (χ w)) • Q (flipRectangle (X T).2.1 (projIcc 0 (T : ℝ) T.property (χ w)))
      rw [projIcc_of_mem T.property (show χ w ∈ Icc 0 (T : ℝ) from ⟨ht.le, htT.le⟩)]
    · have hc : ContinuousAt (fun z =>
          (1 / a (χ z)) • Q (intervalExtension T.property (flipRectangle (X T).2.1) (χ z))) w :=
        (continuousAt_const.div (hac.continuousAt.comp hdχ.continuousAt) (hp _).ne').smul
          (Q.continuous.continuousAt.comp
            ((intervalExtension T.property (flipRectangle (X T).2.1)).continuous.continuousAt.comp hdχ.continuousAt))
      exact hc.congr_of_eventuallyEq (hnear.mono (fun z hz => hv T hz.1.le hz.2.le))
  refine ⟨?_, (fun w hw => (hlocal w hw).1), fun w hw => (hlocal w hw).2.continuousWithinAt⟩
  intro T t ht htT u i
  have hχt := hleft t ht
  rw [hv T (by simpa only [hχt] using ht.le) (by simpa only [hχt] using htT), hχt]
  change (1 / a t) * (X T).2.1 (J u) (projIcc 0 (T : ℝ) T.property t) i = _
  rw [projIcc_of_mem T.property (show t ∈ Icc 0 (T : ℝ) from ⟨ht.le, htT⟩)]
  simp only [J, ContinuousMap.coe_mk, div_eq_mul_inv, one_mul, mul_comm]
  rfl

end CauchyHorizon
