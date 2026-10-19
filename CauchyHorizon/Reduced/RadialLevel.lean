import CauchyHorizon.Reduced.RadialRegularity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! The actual radius is strictly decreasing on every horizontal characteristic. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.radial_strictAnti {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (v : Icc 0 V) (hν : ∀ u, radialNuField hV e Λ zIn x.1 hr u v < 0) :
    StrictAnti (fun u => x.1 u v 0) := by
  have hc : Continuous (fun t => intervalExtension hU x.1 t v 0) := by fun_prop
  have ha : StrictAntiOn (fun t => intervalExtension hU x.1 t v 0) (Icc 0 U) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [((hx.radial_hasDerivWithinAt hr hzin hinu v ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).deriv]
    exact hν ⟨t, ht.1.le, ht.2.le⟩
  intro u w huw
  simpa only [intervalExtension_apply, projIcc_of_mem hU u.property,
    projIcc_of_mem hU w.property] using ha u.property w.property huw

end CauchyHorizon
