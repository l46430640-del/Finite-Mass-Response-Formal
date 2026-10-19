import CauchyHorizon.Reduced.TransverseRegularity

/-! Positive-u representatives retain the exact vertical primitive, including its incoming term. -/

open Set MeasureTheory

namespace CauchyHorizon

theorem IsWaveIntegral.exists_continuous_transverse_primitive
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F) :
    ∃ D S : ℝ → C(Icc 0 V, WaveVector),
      ContinuousOn D (Ioi 0) ∧ ContinuousOn S (Ioi 0) ∧
      x.2.2 =ᵐ[volume.restrict (Icc 0 U)] D ∧
      rectangleSource hU e Λ x hx.choose =ᵐ[volume.restrict (Icc 0 U)] S ∧
      (∀ u, D u = ContinuousMap.const _ (F u) + continuousPrimitiveL hV (S u)) ∧
      ∀ u ∈ Ioc 0 U,
        HasDerivWithinAt (intervalExtension hU x.1) (D u) (Icc 0 U) u ∧
        HasDerivWithinAt (intervalExtension hU x.2.1) (S u) (Icc 0 U) u := by
  obtain ⟨_, S, _, hSc, _, hSae, hder⟩ :=
    hx.exists_continuous_horizontal_derivatives hzin hinu hF hif
  let D := fun u => ContinuousMap.const (Icc 0 V) (F u) + continuousPrimitiveL hV (S u)
  have hDc : ContinuousOn D (Ioi 0) := by dsimp only [D]; fun_prop
  have hDae : x.2.2 =ᵐ[volume.restrict (Icc 0 U)] D := by
    filter_upwards [hx.transverse_identity hx.choose, hif, hSae] with u hu hf hs
    simpa only [D, hf, hs, continuousPrimitiveL_apply] using hu
  refine ⟨D, S, hDc, hSc, hDae, hSae, (fun _ => rfl), fun u hu => ⟨?_, (hder u hu).2⟩⟩
  have hd := horizontalPrimitive_hasDerivWithinAt_of_continuous hU x.2.2 hDc hDae hu
  rw [hx.horizontal_identity hzin, map_add]
  exact hd.const_add _

end CauchyHorizon
