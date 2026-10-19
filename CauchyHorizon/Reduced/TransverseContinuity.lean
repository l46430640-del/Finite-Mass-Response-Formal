import CauchyHorizon.Reduced.BoundaryDerivative
import CauchyHorizon.Reduced.TransverseRegularity

/-! Actual transverse derivative rows inherit finite-time continuity from positive-u representatives. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

theorem IsTransverseWaveBoundary.continuousOn {U ε e Λ : ℝ}
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
    {Dh : C(Icc ε U, WaveVector)} (hB : IsTransverseWaveBoundary hU.le hεU X χ Z D Dh) :
    ContinuousOn D (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  let T : Ici (0 : ℝ) := ⟨t + 1, by change 0 ≤ t + 1; linarith only [ht]⟩
  obtain ⟨d, _S, hdc, _hSc, _hdae, _hSae, hd⟩ :=
    (hX T).exists_continuous_horizontal_derivatives hzin hinu hF hif
  let R : C(Icc ε U, C(Icc 0 (T : ℝ), WaveVector)) :=
    ⟨fun u => d u, hdc.comp_continuous continuous_subtype_val (fun u => hε.trans_le u.property.1)⟩
  let H : C(Icc 0 (T : ℝ), C(Icc ε U, WaveVector)) :=
    (R.uncurry.comp ⟨Prod.swap, continuous_swap⟩).curry
  have he (w : ℝ) (hw : 0 ≤ w) (hwT : w ≤ T) : D w = intervalExtension T.property H w := by
    apply ContinuousMap.ext
    intro u
    let v : Icc 0 (T : ℝ) := ⟨w, hw, hwT⟩
    have hdrep := (ContinuousMap.evalCLM ℝ v).hasFDerivAt.comp_hasDerivWithinAt (u : ℝ)
      (hd u ⟨hε.trans_le u.property.1, u.property.2⟩).1
    have hUD := uniqueDiffOn_Icc hU (u : ℝ) ⟨hε.le.trans u.property.1, u.property.2⟩
    have hh := ((hB.1 T w hw hwT u).derivWithin hUD).symm.trans (hdrep.derivWithin hUD)
    change D w u = H (projIcc 0 (T : ℝ) T.property w) u
    rw [projIcc_of_mem T.property (show w ∈ Icc 0 (T : ℝ) from ⟨hw, hwT⟩)]
    exact hh
  apply (intervalExtension T.property H).continuous.continuousWithinAt.congr_of_eventuallyEq_of_mem
    (g := D) ?_ ht
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (show t < (T : ℝ) from lt_add_one t))] with w hw hwT
  exact he w hw hwT.le

end CauchyHorizon
