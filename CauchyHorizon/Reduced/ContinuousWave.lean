import CauchyHorizon.Reduced.TransversePrimitive
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Both mixed derivatives use the same continuous positive-u transverse representative. -/

open Set MeasureTheory

namespace CauchyHorizon

theorem IsWaveIntegral.exists_continuous_wave_derivatives
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F) :
    ∃ D : ℝ → C(Icc 0 V, WaveVector), ContinuousOn D (Ioi 0) ∧
      x.2.2 =ᵐ[volume.restrict (Icc 0 U)] D ∧
      ∀ u ∈ Ioc 0 U,
        HasDerivWithinAt (intervalExtension hU x.1) (D u) (Icc 0 U) u ∧
        ∀ v : Icc 0 V,
          HasDerivWithinAt (intervalExtension hV (D u))
            (waveSource e Λ (intervalExtension hU x.1 u v) (D u v)
              (intervalExtension hU x.2.1 u v)) (Icc 0 V) v ∧
          HasDerivWithinAt (fun s => intervalExtension hU x.2.1 s v)
            (waveSource e Λ (intervalExtension hU x.1 u v) (D u v)
              (intervalExtension hU x.2.1 u v)) (Icc 0 U) u := by
  obtain ⟨D, S, hDc, hSc, hDae, hSae, hprim, hder⟩ :=
    hx.exists_continuous_transverse_primitive hzin hinu hF hif
  refine ⟨D, hDc, hDae, fun u hu => ⟨(hder u hu).1, fun v => ?_⟩⟩
  let z := fun s : ℝ => intervalExtension hU x.1 s v
  let q := fun s : ℝ => intervalExtension hU x.2.1 s v
  let J := Icc (u / 2) U
  have hJ : J ⊆ Ioi (0 : ℝ) := fun _ hs => (half_pos hu.1).trans_le hs.1
  have hpc : ContinuousOn (fun s => D s v) J :=
    (ContinuousMap.evalCLM ℝ v).continuous.comp_continuousOn (hDc.mono hJ)
  have hsc : ContinuousOn (fun s => S s v) J :=
    (ContinuousMap.evalCLM ℝ v).continuous.comp_continuousOn (hSc.mono hJ)
  have hzc : Continuous z := by fun_prop
  have hqc : Continuous q := by fun_prop
  have hpot : Continuous (fun s => wavePotential e Λ (z s)) := continuous_iff_continuousAt.2
    (fun s => (wavePotential_contDiffAt (z := z s)
      (hx.choose (projIcc 0 U hU s) v) e Λ).continuousAt.comp hzc.continuousAt)
  have hlin : Continuous (fun s => waveLinear (z s) (q s)) := by
    apply continuous_iff_continuousAt.2
    intro s
    exact ContinuousAt.comp (f := fun s : ℝ => (z s, q s))
      (g := fun p : WaveVector × WaveVector => waveLinear p.1 p.2)
      (waveLinear_contDiffAt (p := (z s, q s))
        (hx.choose (projIcc 0 U hU s) v)).continuousAt (hzc.prodMk hqc).continuousAt
  have hsrc : ContinuousOn (fun s => waveSource e Λ (z s) (D s v) (q s)) J := by
    simp_rw [waveSource_affine]
    exact hpot.continuousOn.add (hlin.continuousOn.clm_apply hpc)
  have hae : (fun s => S s v) =ᵐ[volume.restrict J]
      fun s => waveSource e Λ (z s) (D s v) (q s) := by
    have he : (fun s => S s v) =ᵐ[volume.restrict (Icc 0 U)]
        fun s => waveSource e Λ (z s) (D s v) (q s) := by
      filter_upwards [hSae, hDae, rectangleSource_ae hU e Λ x hx.choose] with s hs hd hsrc
      rw [← hs, hsrc v, hd]
      rfl
    exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc (half_pos hu.1).le le_rfl) he
  have hsource := Measure.eqOn_Icc_of_ae_eq volume
    ((half_lt_self hu.1).trans_le hu.2).ne hae hsc hsrc
    (show u ∈ J from ⟨half_le_self hu.1.le, hu.2⟩)
  constructor
  · have hd : HasDerivWithinAt (intervalExtension hV (D u)) (S u v) (Icc 0 V) v := by
      rw [hprim u, map_add]
      exact (continuousPrimitive_hasDerivWithinAt hV (S u) v.property).const_add (F u)
    exact hd.congr_deriv hsource
  · exact ((ContinuousMap.evalCLM ℝ v).hasFDerivAt.comp_hasDerivWithinAt
      u (hder u hu).2).congr_deriv hsource

end CauchyHorizon
