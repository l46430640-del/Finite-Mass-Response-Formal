import CauchyHorizon.Reduced.LocalWeakExtension

open Set Filter MeasureTheory
open scoped Topology Manifold

namespace CauchyHorizon.Tests

-- Positive null-coordinate velocities alone do not make a four-dimensional curve causal.
example (w : SphereAmbient) (hw : 1 < ‖w‖ ^ 2) :
    ¬IsFutureCausalVelocity 1 1 ((1, 1), w) := by
  intro h
  have hh := h.2
  dsimp [sphericalVelocitySquare] at hh
  linarith

-- The dependence set quantifies over all locally Lipschitz causal curves, not just radial ones.
example {va vb ua ub : ℝ} (H R : SphericalSpacetime → ℝ)
    {p : SphericalSpacetime} (hp : p ∈ sphericalOpenRectangle va vb ua ub)
    (hpV : 0 ≤ p.1.1) :
    ∃ γ : ℝ → SphericalSpacetime,
      IsPastInextendibleCausalCurve (sphericalOpenRectangle va vb ua ub) H R γ ∧
      γ 0 = p ∧ ∀ t ≤ 0, γ t ∉ sphericalOpenRectangle va 0 ua ub := by
  obtain ⟨γ, hγ, hs, hV⟩ := exists_past_radial_null_curve H R hp
  refine ⟨γ, hγ, hs, ?_⟩
  intro t _ht hm
  have hn := hm.1.1.2
  rw [hV] at hn
  exact (not_lt_of_ge hpV) hn

-- The causal certificate concerns the same weak solution and the actual embedding image.
example {U ε e Λ T₀ u₀ : ℝ} {hε : 0 ≤ ε} {hεU : ε ≤ U}
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    (h : HasLocalSphericalWeakExtension hε hεU e Λ X χ T₀ u₀) :
    let V := regularTime (anchoringLapse (hε.trans hεU) X)
    ∃ ua L T b : ℝ, ∃ hW : 0 ≤ b - V T, ∃ hL : 0 ≤ L,
    ∃ y : WaveState (b - V T) L,
    ∃ E : OpenPartialHomeomorph SphericalSpacetime SphericalSpacetime,
      HasSphericalWeakSolution hW hL e Λ y ∧
      IsRegularSpacetimeEmbedding (anchoringLapse (hε.trans hεU) X) χ T ua (ua + L) E ∧
      let M := sphericalOpenRectangle (V T) b ua (ua + L)
      let z := crossingSpacetimeField hW hL y (V T) ua
      let H := fun q => Real.exp (z q 2)
      let R := fun q => z q 0 ^ 2
      futureDomainOfDependence M H R E.target = E.target ∧
      futureCauchyHorizon M H R E.target = ({0} ×ˢ Ioo ua (ua + L)) ×ˢ univ ∧
      ∀ p : UnitSphere, ((0, u₀), p) ∈ futureCauchyHorizon M H R E.target := by
  obtain ⟨_hχ, ua, L, T, b, _hea, ham, hmr, _hrU, _hT₀, _hT, _hn, _hb,
    hL, hW, y, hy, _himage, E, hE, _hdomain, _hfrontier, hcausal, _hchar, _hcharts, _hpast⟩ := h
  refine ⟨ua, L, T, b, hW, hL, y, E, hy, hE, ?_⟩
  dsimp only [HasSphericalCauchyHorizon] at hcausal
  rw [add_sub_cancel] at hcausal
  refine ⟨hcausal.1, hcausal.2, ?_⟩
  intro p
  rw [hcausal.2]
  exact ⟨⟨rfl, ham, hmr⟩, mem_univ p⟩

end CauchyHorizon.Tests
