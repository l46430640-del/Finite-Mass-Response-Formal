import CauchyHorizon.Reduced.TransverseEvolution
import CauchyHorizon.Reduced.RegularBoundary
import CauchyHorizon.Reduced.WaveCovariance

/-! The original development obeys the mixed wave equation in the normalized regular chart. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

def IsRegularWaveEvolution {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (e Λ : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector))
    (Dh : C(Icc ε U, WaveVector)) : Prop :=
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let W := compactifiedTransverseRow χ D Dh
  let Q := fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)
  ∀ w ∈ Ioo (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0, ∀ u : Icc ε U,
    HasDerivAt (fun s => W s u) (waveSource e Λ (Ψ w u) (Q w u) (W w u)) w ∧
    HasDerivWithinAt (intervalExtension hεU (Q w))
      (waveSource e Λ (Ψ w u) (Q w u) (W w u)) (Icc ε U) u

set_option maxHeartbeats 1000000 in
theorem regular_wave_evolution {U ε e Λ : ℝ} (hU : 0 < U) (hε : 0 < ε) (hεU : ε ≤ U)
    (zIn : C(Icc 0 U, WaveVector))
    (vOut : (T : Ici (0 : ℝ)) → C(Icc 0 (T : ℝ), WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ T, IsWaveIntegral hU.le T.property e Λ zIn (vOut T) uIn (X T))
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU.le uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse hU.le X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hB : IsTransverseWaveBoundary hU.le hεU X χ Z D Dh)
    (hregular : IsRegularWaveBoundary hε.le hεU X χ Z D Dh) :
    IsRegularWaveEvolution hε.le hεU e Λ X χ Z D Dh := by
  let a := anchoringLapse hU.le X
  let Ψ := compactifiedWaveRow hε.le hεU X χ Z
  let W := compactifiedTransverseRow χ D Dh
  have hvdata := (regular_wave_derivative hε.le hεU X hcompat
    (fun T t ht => (hX T).longitudinal_section_derivative ht) hχ).1
  intro w hw u
  obtain ⟨ht, he, hdχ⟩ := hχ.2.2.2.2.2.2.2.2.2.2.1 w hw
  let T : Ici (0 : ℝ) := ⟨χ w + 1, by change 0 ≤ χ w + 1; linarith only [ht]⟩
  have htT : χ w < T := lt_add_one _
  let v : Icc 0 (T : ℝ) := ⟨χ w, ht.le, htT.le⟩
  let J : Icc ε U → Icc 0 U := fun s => ⟨s, hε.le.trans s.property.1, s.property.2⟩
  let z := fun s : Icc ε U => (X T).1 (J s) v
  let q := fun s : Icc ε U => (X T).2.1 (J s) v
  let anchor : Icc ε U := ⟨U, hεU, le_rfl⟩
  have hlapse : a (χ w) = Real.exp (z anchor 2) := by
    dsimp only [a, anchoringLapse]
    rw [max_eq_right ht.le,
      renormalizedWaveRow_apply hU.le X hcompat T ht.le htT.le ⟨U, le_rfl, le_rfl⟩ 2]
    simp only [ite_true, mul_zero, zero_mul, add_zero]
    rfl
  have hz : Ψ w u = z u - ![0, 0, Real.log (a (χ w))] := by
    have hh := hregular.1 T (χ w) ht htT.le u
    rw [he] at hh
    rw [hh, hlapse, Real.log_exp]
    ext i
    fin_cases i <;> rfl
  have hv (s : Icc ε U) : regularWaveVelocityRow hε.le hεU X χ w s = (a (χ w))⁻¹ • q s := by
    ext i
    have hh := hvdata T (χ w) ht htT.le s i
    rw [he] at hh
    change regularWaveVelocityRow hε.le hεU X χ w s i = (a (χ w))⁻¹ * q s i
    exact hh.trans (by change q s i / a (χ w) = _; rw [div_eq_mul_inv, mul_comm])
  have hnormalized (s : Icc ε U) : waveNormalize anchor (regularWaveVelocityRow hε.le hεU X χ w) s =
      (a (χ w))⁻¹ • (q s - ![0, 0, q anchor 2]) := by
    rw [waveNormalize_apply, hv s, hv anchor]
    ext i
    fin_cases i <;> simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail]
    ring
  have hW : W w u = D (χ w) u := by
    change compactifiedTransverseRow χ D Dh w u = D (χ w) u
    rw [compactifiedTransverseRow, Function.update_of_ne hw.2.ne]
  have hraw := hB.mixed_derivatives hU hε zIn vOut uIn X hX hzin hinu hF hif T (χ w) ht htT u
  have hsource : (a (χ w))⁻¹ • waveSource e Λ (z u) (D (χ w) u) (q u) =
      waveSource e Λ (Ψ w u)
        (waveNormalize anchor (regularWaveVelocityRow hε.le hεU X χ w) u) (W w u) := by
    rw [hz, hnormalized u, hW, waveSource_regular_swap e Λ (z u) (D (χ w) u) (q u)
      (hχ.2.1 (χ w)) (q anchor 2)]
  have hactual : HasDerivAt (fun s => W s u)
      ((1 / a (χ w)) • waveSource e Λ (z u) (D (χ w) u) (q u)) w := by
    apply (hraw.1.scomp w hdχ).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hw.2] with s hs
    change compactifiedTransverseRow χ D Dh s u = D (χ s) u
    rw [compactifiedTransverseRow, Function.update_of_ne hs.ne]
  constructor
  · exact hactual.congr_deriv (by simpa only [one_div] using hsource)
  · have hd := ((hraw.2.sub_const ![0, 0, q anchor 2]).const_smul (a (χ w))⁻¹).mono
      (Icc_subset_Icc hε.le le_rfl)
    have he : HasDerivWithinAt
        (intervalExtension hεU (waveNormalize anchor (regularWaveVelocityRow hε.le hεU X χ w)))
        ((a (χ w))⁻¹ • waveSource e Λ (z u) (D (χ w) u) (q u)) (Icc ε U) u := by
      apply hd.congr_of_mem _ u.property
      intro s hs
      rw [intervalExtension_apply, projIcc_of_mem hεU hs, hnormalized ⟨s, hs⟩]
      exact congrArg (fun k : Icc 0 U => (a (χ w))⁻¹ • ((X T).2.1 k v - ![0, 0, q anchor 2]))
        (projIcc_of_mem hU.le (show s ∈ Icc 0 U from ⟨hε.le.trans hs.1, hs.2⟩)).symm
    exact he.congr_deriv hsource

end CauchyHorizon
