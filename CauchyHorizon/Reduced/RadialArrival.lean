import CauchyHorizon.Reduced.RadialCoordinates
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Local radius levels and their Jacobian from the actual continuous radial derivatives. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

theorem IsWaveIntegral.exists_radial_level_chart {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ∈ Ioo 0 U) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hν : radialNuField hV e Λ zIn x.1 hr u v ≠ 0) :
    let ν := radialNuField hV e Λ zIn x.1 hr
    ∃ ψ : ℝ → ℝ, ψ v = u ∧ HasStrictDerivAt ψ (-x.2.1 u v 0 / ν u v) v ∧
      ∀ᶠ t in 𝓝 (v : ℝ), ψ t ∈ Ioo 0 U ∧ t ∈ Ioo 0 V ∧
        intervalExtension hV (intervalExtension hU x.1 (ψ t)) t 0 = x.1 u v 0 := by
  obtain ⟨ψ, hself, hd, hnear⟩ := hx.exists_radial_coordinate_chart hr hzin hinu u v hu hv hν
  refine ⟨fun t => ψ (x.1 u v 0, t), hself, ?_, ?_⟩
  · have hh := hd.comp_hasStrictDerivAt (v : ℝ)
      ((hasStrictDerivAt_const (v : ℝ) (x.1 u v 0)).prodMk (hasStrictDerivAt_id (v : ℝ)))
    simpa only [Function.comp_def, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, zero_mul, one_mul, zero_sub, neg_div] using hh
  · exact (continuous_const.prodMk continuous_id).continuousAt hnear

end CauchyHorizon
