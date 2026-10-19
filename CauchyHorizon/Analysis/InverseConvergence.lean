import Mathlib.Topology.ContinuousMap.Compact

/-! Uniform stability of continuous inverse coordinates on a compact domain. -/

open Filter
open scoped Topology

namespace CauchyHorizon

theorem continuous_inverse_coordinates_tendsto {ι A K E : Type*}
    [TopologicalSpace A] [CompactSpace A] [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E]
    {l : Filter ι} {R : ι → C(A, E)} {R₀ : C(A, E)}
    (hR : Function.Injective R₀) (hlim : Tendsto R l (𝓝 R₀))
    {χ : ι → C(K, A)} {χ₀ : C(K, A)}
    (hhit : ∀ i w, R i (χ i w) = R₀ (χ₀ w)) : Tendsto χ l (𝓝 χ₀) := by
  apply (R₀.isInducing_postcomp (R₀.continuous.isClosedEmbedding hR).isEmbedding.isInducing).tendsto_nhds_iff.2
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hzero : Tendsto (fun i => ‖R₀ - R i‖) l (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using ((tendsto_const_nhds (x := R₀)).sub hlim).norm
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hzero
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro w
  change ‖R₀ (χ i w) - R₀ (χ₀ w)‖ ≤ ‖R₀ - R i‖
  rw [← hhit i w]
  exact ContinuousMap.norm_coe_le_norm (R₀ - R i) (χ i w)

end CauchyHorizon
