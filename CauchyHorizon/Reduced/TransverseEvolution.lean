import CauchyHorizon.Reduced.ContinuousWave
import CauchyHorizon.Reduced.BoundaryDerivative

/-! The actual transverse derivative satisfies the wave equation at every positive incoming point. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

set_option maxHeartbeats 1000000 in
theorem IsTransverseWaveBoundary.mixed_derivatives {U ε e Λ : ℝ}
    (hU : 0 < U) (hε : 0 < ε) {hεU : ε ≤ U}
    (zIn : C(Icc 0 U, WaveVector))
    (vOut : (T : Ici (0 : ℝ)) → C(Icc 0 (T : ℝ), WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ T, IsWaveIntegral hU.le T.property e Λ zIn (vOut T) uIn (X T))
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU.le uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F)
    {χ : ℝ → ℝ} {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)}
    {Dh : C(Icc ε U, WaveVector)} (hB : IsTransverseWaveBoundary hU.le hεU X χ Z D Dh)
    (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 < t) (htT : t < T) (u : Icc ε U) :
    HasDerivAt (fun s => D s u)
      (waveSource e Λ ((X T).1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht.le, htT.le⟩)
        (D t u) ((X T).2.1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht.le, htT.le⟩)) t ∧
    HasDerivWithinAt (fun s => intervalExtension hU.le (X T).2.1 s ⟨t, ht.le, htT.le⟩)
      (waveSource e Λ ((X T).1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht.le, htT.le⟩)
        (D t u) ((X T).2.1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht.le, htT.le⟩))
      (Icc 0 U) u := by
  obtain ⟨d, _hdc, _hdae, hder⟩ :=
    (hX T).exists_continuous_wave_derivatives hzin hinu hF hif
  have hu : 0 < (u : ℝ) := hε.trans_le u.property.1
  have hfinite (s : ℝ) (hs : 0 ≤ s) (hsT : s ≤ T) : D s u = d u ⟨s, hs, hsT⟩ := by
    have hd := (ContinuousMap.evalCLM ℝ (⟨s, hs, hsT⟩ : Icc 0 (T : ℝ))).hasFDerivAt.comp_hasDerivWithinAt
      (u : ℝ) (hder u ⟨hu, u.property.2⟩).1
    exact ((hB.1 T s hs hsT u).derivWithin (uniqueDiffOn_Icc hU u ⟨hu.le, u.property.2⟩)).symm.trans
      (hd.derivWithin (uniqueDiffOn_Icc hU u ⟨hu.le, u.property.2⟩))
  let v : Icc 0 (T : ℝ) := ⟨t, ht.le, htT.le⟩
  have hraw := (hder u ⟨hu, u.property.2⟩).2 v
  have hsvalue : waveSource e Λ (intervalExtension hU.le (X T).1 u v)
      (d u v) (intervalExtension hU.le (X T).2.1 u v) = waveSource e Λ
      ((X T).1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ v) (D t u)
      ((X T).2.1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ v) := by
    simp only [intervalExtension_apply,
      projIcc_of_mem hU.le (show (u : ℝ) ∈ Icc 0 U from ⟨hu.le, u.property.2⟩)]
    rw [← hfinite t ht.le htT.le]
  constructor
  · have hd := hraw.1.hasDerivAt (Icc_mem_nhds ht htT)
    have he : (fun s => D s u) =ᶠ[𝓝 t] intervalExtension T.property (d u) := by
      filter_upwards [eventually_gt_nhds ht, eventually_lt_nhds htT] with s hs hsT
      exact (hfinite s hs.le hsT.le).trans (congrArg (d u)
        (projIcc_of_mem T.property (show s ∈ Icc 0 (T : ℝ) from ⟨hs.le, hsT.le⟩)).symm)
    exact (hd.congr_of_eventuallyEq he).congr_deriv hsvalue
  · exact hraw.2.congr_deriv hsvalue

end CauchyHorizon
