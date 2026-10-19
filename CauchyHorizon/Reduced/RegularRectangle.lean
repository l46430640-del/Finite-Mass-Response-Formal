import CauchyHorizon.Reduced.RegularEvolution
import CauchyHorizon.Reduced.ClassicalIntegral

/-! Actual regular-chart fields on a finite negative-time rectangle satisfy the local integral system. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def waveWindow {U ε A L : ℝ} (hεU : ε ≤ U) (a ua : ℝ)
    (f : ℝ → C(Icc ε U, WaveVector)) (hc : ContinuousOn f (Icc a (a + A))) : WaveRectangle A L :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 A)
    (ContinuousMap.compCLM ℝ WaveVector
      (⟨fun s : Icc 0 L => projIcc ε U hεU (ua + s), by fun_prop⟩ : C(Icc 0 L, Icc ε U)))
    ⟨fun t => f (a + t), hc.comp_continuous (by fun_prop)
      (fun t => ⟨le_add_of_nonneg_right t.property.1, add_le_add_right t.property.2 a⟩)⟩

set_option maxHeartbeats 800000 in
theorem exists_regular_wave_rectangle {U ε e Λ a ua A L : ℝ}
    (hε : 0 ≤ ε) (hεU : ε ≤ U) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) {χ : ℝ → ℝ}
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh)
    (hE : IsRegularWaveEvolution hε hεU e Λ X χ Z D Dh)
    (hQ : ContinuousOn (regularWaveVelocityRow hε hεU X χ)
      (Ioo (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0))
    (hr : ∀ (T : Ici (0 : ℝ)) u v, 0 < (X T).1 u v 0)
    (ha : regularTime (anchoringLapse (hε.trans hεU) X) 0 < a) (haA : a + A < 0)
    (hua : ε < ua) (huaL : ua + L < U) :
    ∃ z p q : WaveRectangle A L,
      (∀ t s, z t s = compactifiedWaveRow hε hεU X χ Z (a + t) (projIcc ε U hεU (ua + s))) ∧
      (∀ t s, p t s = waveNormalize ⟨U, hεU, le_rfl⟩
        (regularWaveVelocityRow hε hεU X χ (a + t)) (projIcc ε U hεU (ua + s))) ∧
      (∀ t s, q t s = compactifiedTransverseRow χ D Dh (a + t) (projIcc ε U hεU (ua + s))) ∧
      IsWaveIntegral hA hL e Λ (flipRectangle z ⟨0, le_rfl, hL⟩) (q ⟨0, le_rfl, hA⟩)
        (intervalToLp hA 2 (flipRectangle p ⟨0, le_rfl, hL⟩)) (z, q, intervalToLp hA 2 p) ∧
      flipRectangle z ⟨0, le_rfl, hL⟩ = ContinuousMap.const (Icc 0 A)
        (z ⟨0, le_rfl, hA⟩ ⟨0, le_rfl, hL⟩) +
        horizontalPrimitive hA (intervalToLp hA 2 (flipRectangle p ⟨0, le_rfl, hL⟩)) ∧
      ∀ t s, 0 < z t s 0 := by
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let W := compactifiedTransverseRow χ D Dh
  let N := waveNormalize (⟨U, hεU, le_rfl⟩ : Icc ε U)
  let Q := fun w => N (regularWaveVelocityRow hε hεU X χ w)
  let J := Ioo (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0
  have hsub : Icc a (a + A) ⊆ J := fun _ hw => ⟨ha.trans_le hw.1, hw.2.trans_lt haA⟩
  have hΨc : ContinuousOn Ψ (Icc a (a + A)) :=
    hB.2.2.1.mono (fun w hw => ⟨(hsub hw).1, (hsub hw).2.le⟩)
  have hWc : ContinuousOn W (Icc a (a + A)) :=
    hB.2.2.2.1.mono (fun w hw => ⟨(hsub hw).1, (hsub hw).2.le⟩)
  have hQc : ContinuousOn Q (Icc a (a + A)) := by
    intro w hw
    exact N.continuous.continuousAt.comp_continuousWithinAt ((hQ.mono hsub) w hw)
  let z := waveWindow (L := L) hεU a ua Ψ hΨc
  let p := waveWindow (L := L) hεU a ua Q hQc
  let q := waveWindow (L := L) hεU a ua W hWc
  have ht (t : Icc 0 A) : a + (t : ℝ) ∈ J :=
    hsub ⟨le_add_of_nonneg_right t.property.1, add_le_add_right t.property.2 a⟩
  have hs (s : Icc 0 L) : ua + (s : ℝ) ∈ Ioo ε U :=
    ⟨hua.trans_le (le_add_of_nonneg_right s.property.1),
      (add_le_add_right s.property.2 ua).trans_lt huaL⟩
  have hzpos (t : Icc 0 A) (s : Icc 0 L) : 0 < z t s 0 := by
    obtain ⟨hv, he, _hd⟩ := hχ.2.2.2.2.2.2.2.2.2.2.1 (a + t) (ht t)
    let T : Ici (0 : ℝ) := ⟨χ (a + t), hv.le⟩
    let u := projIcc ε U hεU (ua + s)
    have hf := congrArg (fun w : WaveVector => w 0) (hB.1 T (χ (a + t)) hv le_rfl u)
    rw [he] at hf
    simp only [Pi.sub_apply, if_neg (by decide : (0 : Fin 3) ≠ 2), sub_zero] at hf
    change 0 < Ψ (a + t) u 0
    exact hf.symm ▸ hr T _ _
  let S : WaveRectangle A L := (⟨fun ts : Icc 0 A × Icc 0 L =>
    waveSource e Λ (z ts.1 ts.2) (p ts.1 ts.2) (q ts.1 ts.2), by
      simp_rw [waveSource_affine]
      exact (wavePotentialField e Λ z.uncurry (fun ts => (hzpos ts.1 ts.2).ne')).continuous.add
        ((waveLinearField z.uncurry q.uncurry (fun ts => (hzpos ts.1 ts.2).ne')).continuous.clm_apply
          p.uncurry.continuous)⟩ : C(Icc 0 A × Icc 0 L, WaveVector)).curry
  have hspace (f : C(Icc ε U, WaveVector)) (d : WaveVector) (s : Icc 0 L)
      (hd : HasDerivWithinAt (intervalExtension hεU f) d (Icc ε U)
        (projIcc ε U hεU (ua + s))) :
      HasDerivWithinAt (fun r => f (projIcc ε U hεU (ua + (projIcc 0 L hL r : ℝ)))) d
        (Icc 0 L) s := by
    have hi : ua + (s : ℝ) ∈ Icc ε U := ⟨(hs s).1.le, (hs s).2.le⟩
    rw [projIcc_of_mem hεU hi] at hd
    have hh := (hd.hasDerivAt (Icc_mem_nhds (hs s).1 (hs s).2)).scomp
      (s : ℝ) ((hasDerivAt_id (s : ℝ)).const_add ua)
    simp only [one_smul] at hh
    apply hh.hasDerivWithinAt.congr_of_mem _ s.property
    intro r hr
    rw [projIcc_of_mem hL hr]
    rfl
  have hz (t : Icc 0 A) (s : Icc 0 L) :
      HasDerivWithinAt (intervalExtension hL (z t)) (q t s) (Icc 0 L) s :=
    hspace (Ψ (a + t)) _ s (hB.2.2.2.2 (a + t) ⟨(ht t).1, (ht t).2.le⟩ _)
  have hp (t : Icc 0 A) (s : Icc 0 L) :
      HasDerivWithinAt (intervalExtension hL (p t)) (S t s) (Icc 0 L) s :=
    hspace (Q (a + t)) _ s (hE (a + t) (ht t) _).2
  have hq (s : Icc 0 L) (t : Icc 0 A) :
      HasDerivWithinAt (intervalExtension hA (flipRectangle q s)) (S t s) (Icc 0 A) t := by
    have hh := (hE (a + t) (ht t) (projIcc ε U hεU (ua + s))).1.scomp
      (t : ℝ) ((hasDerivAt_id (t : ℝ)).const_add a)
    simp only [one_smul] at hh
    apply hh.hasDerivWithinAt.congr_of_mem _ t.property
    intro r hr
    rw [intervalExtension_apply, projIcc_of_mem hA hr]
    rfl
  have hinit (t : Icc 0 A) :
      HasDerivWithinAt (intervalExtension hA (flipRectangle z ⟨0, le_rfl, hL⟩))
        (p t ⟨0, le_rfl, hL⟩) (Icc 0 A) t := by
    have hh := ((ContinuousMap.evalCLM ℝ (projIcc ε U hεU (ua + 0))).hasFDerivAt.comp_hasDerivAt
      (a + t) (hB.2.1 (a + t) (ht t))).scomp (t : ℝ) ((hasDerivAt_id (t : ℝ)).const_add a)
    simp only [one_smul] at hh
    apply hh.hasDerivWithinAt.congr_of_mem _ t.property
    intro r hr
    rw [intervalExtension_apply, projIcc_of_mem hA hr]
    rfl
  have hi := wave_integral_of_continuous_derivatives hA hL e Λ z p q S
    (fun t s => (hzpos t s).ne') (fun _ _ => rfl) hz hp hq hinit
  exact ⟨z, p, q, (fun _ _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl), hi.1, hi.2, hzpos⟩

end CauchyHorizon
