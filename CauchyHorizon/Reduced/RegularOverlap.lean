import CauchyHorizon.Reduced.RegularRectangle
import CauchyHorizon.Reduced.FiniteUniqueness
import CauchyHorizon.Characteristic.PrefixData
import CauchyHorizon.Analysis.PrimitiveInjectivity

/-! Positive-radius uniqueness identifies the new solution with the original regular-chart fields. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

set_option maxHeartbeats 1000000 in
theorem regular_wave_prefix_eq {U ε e Λ a ua A B L : ℝ}
    (hε : 0 ≤ ε) (hεU : ε ≤ U) (hA : 0 < A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hAB : A ≤ B)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) {χ : ℝ → ℝ}
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hregular : IsRegularWaveBoundary hε hεU X χ Z D Dh)
    (hE : IsRegularWaveEvolution hε hεU e Λ X χ Z D Dh)
    (hQ : ContinuousOn (regularWaveVelocityRow hε hεU X χ)
      (Ioo (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0))
    (hr : ∀ (T : Ici (0 : ℝ)) u v, 0 < (X T).1 u v 0)
    (ha : regularTime (anchoringLapse (hε.trans hεU) X) 0 < a) (haA : a + A < 0)
    (hua : ε < ua) (huaL : ua + L < U)
    {zIn : C(Icc 0 B, WaveVector)} {vOut : C(Icc 0 L, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 B))} {y : WaveState B L}
    (hy : IsWaveIntegral hB hL e Λ zIn vOut uIn y)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hB uIn)
    (hpast : ∀ t : Icc 0 B, a + (t : ℝ) ≤ 0 →
      zIn t = compactifiedWaveRow hε hεU X χ Z (a + t) (projIcc ε U hεU ua))
    (hout : ∀ s, vOut s = compactifiedTransverseRow χ D Dh a (projIcc ε U hεU (ua + s)))
    (hyr : ∀ t s, 0 < y.1 t s 0) :
    let ht : 0 + A ≤ B := by simpa only [zero_add] using hAB
    let hs : 0 + L ≤ L := by simp
    (∀ (t : Icc 0 A) s,
      y.1 (intervalTranslate (a := 0) le_rfl ht t) s =
        compactifiedWaveRow hε hεU X χ Z (a + t) (projIcc ε U hεU (ua + s))) ∧
    (∀ (t : Icc 0 A) s,
      y.2.1 (intervalTranslate (a := 0) le_rfl ht t) s =
        compactifiedTransverseRow χ D Dh (a + t) (projIcc ε U hεU (ua + s))) ∧
    ∀ᵐ t ∂volume.restrict (Icc 0 A), ∀ s : Icc 0 L,
      transverseTranslate (a := 0) (b := 0) le_rfl ht le_rfl hs y.2.2 t s =
        waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ (a + t))
          (projIcc ε U hεU (ua + s)) := by
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let W := compactifiedTransverseRow χ D Dh
  have ht : 0 + A ≤ B := by simpa only [zero_add] using hAB
  have hs : 0 + L ≤ L := by simp
  let ι := intervalTranslate (a := 0) le_rfl ht
  let κ := intervalTranslate (a := 0) le_rfl hs
  have hι (t : Icc 0 A) : (ι t : ℝ) = t := zero_add _
  have hκ (s : Icc 0 L) : κ s = s := Subtype.ext (zero_add _)
  let yp := waveTranslate (a := 0) (b := 0) le_rfl ht le_rfl hs y
  have hpzero : horizontalPrimitive hB uIn ⟨0, le_rfl, hB⟩ = 0 := intervalIntegral.integral_same
  obtain ⟨z, p, q, hz, hp, hq, hi, hprim, hzpos⟩ :=
    exists_regular_wave_rectangle hε hεU hA.le hL X hχ hregular hE hQ hr ha haA hua huaL
  have hzIn : zIn.comp ι = flipRectangle z ⟨0, le_rfl, hL⟩ := by
    apply ContinuousMap.ext
    intro t
    change zIn (ι t) = z t ⟨0, le_rfl, hL⟩
    rw [hpast (ι t) (by rw [hι]; exact ((add_le_add_right t.property.2 a).trans_lt haA).le), hz]
    simp only [hι, add_zero]
  have hvOut : vOut.comp κ = q ⟨0, le_rfl, hA.le⟩ := by
    apply ContinuousMap.ext
    intro s
    change vOut (κ s) = q ⟨0, le_rfl, hA.le⟩ s
    rw [hκ, hout, hq]
    simp only [add_zero]
  have hc : c = z ⟨0, le_rfl, hA.le⟩ ⟨0, le_rfl, hL⟩ := by
    have he := congrArg (fun f : C(Icc 0 A, WaveVector) => f ⟨0, le_rfl, hA.le⟩) hzIn
    rw [hzin] at he
    change c + horizontalPrimitive hB uIn (ι ⟨0, le_rfl, hA.le⟩) = _ at he
    have hzero : ι ⟨0, le_rfl, hA.le⟩ = ⟨0, le_rfl, hB⟩ := Subtype.ext (zero_add _)
    rw [hzero, hpzero, add_zero] at he
    exact he
  have huIn : intervalTranslateLp (a := 0) le_rfl ht uIn =
      intervalToLp hA.le 2 (flipRectangle p ⟨0, le_rfl, hL⟩) := by
    apply horizontalPrimitive_injective hA
    apply ContinuousMap.ext
    intro t
    have he := congrArg (fun f : C(Icc 0 A, WaveVector) => f t) hzIn
    rw [hzin, hprim] at he
    change c + horizontalPrimitive hB uIn (ι t) =
      z ⟨0, le_rfl, hA.le⟩ ⟨0, le_rfl, hL⟩ + _ at he
    rw [hc] at he
    rw [horizontalPrimitive_translate hB hA.le le_rfl ht uIn t]
    have hzero : intervalTranslate (a := 0) le_rfl ht ⟨0, le_rfl, hA.le⟩ =
        ⟨0, le_rfl, hB⟩ := Subtype.ext (zero_add _)
    rw [hzero, hpzero, sub_zero]
    exact add_left_cancel he
  have hyp := hy.prefix hA.le hL hAB le_rfl
  change IsWaveIntegral hA.le hL e Λ (zIn.comp ι) (vOut.comp κ)
    (intervalTranslateLp (a := 0) le_rfl ht uIn) yp at hyp
  rw [hzIn, hvOut, huIn] at hyp
  have heq : yp = (z, q, intervalToLp hA.le 2 p) :=
    hyp.unique_of_positive_radius hi (fun t s => hyr (ι t) (κ s)) hzpos
  refine ⟨?_, ?_, ?_⟩
  · intro t s
    have he := congrArg (fun x : WaveState A L => x.1 t s) heq
    change y.1 (ι t) (κ s) = z t s at he
    rw [hκ] at he
    exact he.trans (hz t s)
  · intro t s
    have he := congrArg (fun x : WaveState A L => x.2.1 t s) heq
    change y.2.1 (ι t) (κ s) = q t s at he
    rw [hκ] at he
    exact he.trans (hq t s)
  · have he := congrArg (fun x : WaveState A L => x.2.2) heq
    change transverseTranslate (a := 0) (b := 0) le_rfl ht le_rfl hs y.2.2 =
      intervalToLp hA.le 2 p at he
    rw [he]
    filter_upwards [intervalToLp_ae hA.le 2 p, ae_restrict_mem measurableSet_Icc] with t hd hm
    intro s
    rw [hd, projIcc_of_mem hA.le hm]
    exact hp ⟨t, hm⟩ s

end CauchyHorizon
