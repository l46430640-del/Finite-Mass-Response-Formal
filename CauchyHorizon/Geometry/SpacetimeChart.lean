import CauchyHorizon.Geometry.SphericalChart
import CauchyHorizon.Analysis.ProductWeakDerivative
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Algebra.Group.Basic

/-! Actual spacetime charts with translated null coordinates and an open rectangular target. -/

open Set
open scoped Manifold

namespace CauchyHorizon

noncomputable def sphericalSpacetimeChart (a b : ℝ × ℝ)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) :
    OpenPartialHomeomorph ((ℝ × ℝ) × UnitSphere) ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Homeomorph.subRight a).toOpenPartialHomeomorph.prod
    (c.trans (Homeomorph.subRight b).toOpenPartialHomeomorph)

noncomputable def sphericalRectangleChart (W L A B : ℝ) (a b : ℝ × ℝ)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) :
    OpenPartialHomeomorph ((ℝ × ℝ) × UnitSphere) ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((sphericalSpacetimeChart a b c).symm.restr (openRectangleProduct W L A B)).symm

theorem sphericalRectangleChart_apply (W L A B : ℝ) (a b : ℝ × ℝ)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (w : (ℝ × ℝ) × UnitSphere) :
    sphericalRectangleChart W L A B a b c w = (w.1 - a, c w.2 - b) := rfl

theorem sphericalRectangleChart_symm_apply (W L A B : ℝ) (a b : ℝ × ℝ)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    (sphericalRectangleChart W L A B a b c).symm w = (w.1 + a, c.symm (w.2 + b)) := rfl

theorem sphericalRectangleChart_target (W L A B : ℝ) (a b : ℝ × ℝ)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : ∀ y ∈ openRectangle A B, y + b ∈ c.target) :
    (sphericalRectangleChart W L A B a b c).target = openRectangleProduct W L A B := by
  change ((sphericalSpacetimeChart a b c).symm.restr (openRectangleProduct W L A B)).source = _
  rw [OpenPartialHomeomorph.restr_source' _ _ (openRectangleProduct W L A B).isOpen]
  apply inter_eq_right.2
  intro w hw
  change w.1 ∈ Set.univ ∧ w.2 ∈ (c.trans (Homeomorph.subRight b).toOpenPartialHomeomorph).target
  exact ⟨Set.mem_univ _, Set.mem_univ _, hc w.2 hw.2⟩

theorem sphericalRectangleChart_mem_source (W L A B : ℝ) (a b : ℝ × ℝ)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : ∀ y ∈ openRectangle A B, y + b ∈ c.target)
    {w : (ℝ × ℝ) × UnitSphere} (hp : w.2 ∈ c.source)
    (hw : (w.1 - a, c w.2 - b) ∈ openRectangleProduct W L A B) :
    w ∈ (sphericalRectangleChart W L A B a b c).source := by
  have h := (sphericalRectangleChart W L A B a b c).map_target
    (by rw [sphericalRectangleChart_target W L A B a b c hc]; exact hw)
  simpa only [sphericalRectangleChart_symm_apply, sub_add_cancel, c.left_inv hp, Prod.mk.eta] using h

theorem sphericalRectangleChart_null_line {vT b ua L u₀ δ : ℝ}
    (hδ : 0 < δ) (hua : ua < u₀) (huL : u₀ < ua + L)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) {p : UnitSphere}
    (hp : p ∈ c.source) (hcenter : c p = (Real.pi / 2, Real.pi / 2))
    (hbox : ∀ s ∈ Icc 0 (2 * δ), ∀ t ∈ Icc 0 (2 * δ),
      (Real.pi / 2 - δ + s, Real.pi / 2 - δ + t) ∈ c.target) :
    let C := sphericalRectangleChart (b - vT) L (2 * δ) (2 * δ) (vT, ua)
      (Real.pi / 2 - δ, Real.pi / 2 - δ) c
    C.target = openRectangleProduct (b - vT) L (2 * δ) (2 * δ) ∧
      ∀ v ∈ Ioo vT b, ((v, u₀), p) ∈ C.source := by
  have hc : ∀ y ∈ openRectangle (2 * δ) (2 * δ),
      y + (Real.pi / 2 - δ, Real.pi / 2 - δ) ∈ c.target := by
    intro y hy
    simpa only [Prod.add_def, add_comm] using
      hbox y.1 ⟨hy.1.1.le, hy.1.2.le⟩ y.2 ⟨hy.2.1.le, hy.2.2.le⟩
  refine ⟨sphericalRectangleChart_target _ _ _ _ _ _ c hc, ?_⟩
  intro v hv
  apply sphericalRectangleChart_mem_source _ _ _ _ _ _ c hc hp
  rw [hcenter]
  change ((0 < v - vT ∧ v - vT < b - vT) ∧ (0 < u₀ - ua ∧ u₀ - ua < L)) ∧
    (0 < Real.pi / 2 - (Real.pi / 2 - δ) ∧ Real.pi / 2 - (Real.pi / 2 - δ) < 2 * δ) ∧
    (0 < Real.pi / 2 - (Real.pi / 2 - δ) ∧ Real.pi / 2 - (Real.pi / 2 - δ) < 2 * δ)
  exact ⟨⟨⟨by linarith [hv.1], by linarith [hv.2]⟩, ⟨by linarith, by linarith⟩⟩,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem sphereSpacetimeMetric_time_change {H H' R a : ℝ} (hH : H' * a = H)
    (p : UnitSphere) (ξ η : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphereSpacetimeMetric H' R p ((a * ξ.1.1, ξ.1.2), ξ.2) ((a * η.1.1, η.1.2), η.2) =
      sphereSpacetimeMetric H R p ξ η := by
  simp only [sphereSpacetimeMetric]
  rw [← hH]
  ring

end CauchyHorizon
