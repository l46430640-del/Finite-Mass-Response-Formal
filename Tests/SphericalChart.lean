import CauchyHorizon.Geometry.SphericalChart
import CauchyHorizon.Reduced.SphericalGeometry

open CauchyHorizon Set
open scoped Manifold ContDiff

example (p : UnitSphere) :
    ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient, ∃ c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ),
      p ∈ c.source ∧ c p = (Real.pi / 2, Real.pi / 2) ∧
      EqOn c.symm (rotatedSphericalMap A) c.target ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω c c.source ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target ∧
      c.target ⊆ Ioo 0 Real.pi ×ˢ Ioo 0 Real.pi :=
  exists_regular_spherical_chart p

-- The entire compact angular rectangle lies in a genuine chart; its center is interior.
example (p : UnitSphere) :
    ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient, ∃ c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ),
      p ∈ c.source ∧ c p = (Real.pi / 2, Real.pi / 2) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / 2 ∧
        ∀ s ∈ Icc 0 (2 * δ), ∀ t ∈ Icc 0 (2 * δ),
          (Real.pi / 2 - δ + s, Real.pi / 2 - δ + t) ∈ c.target ∧
          c.symm (Real.pi / 2 - δ + s, Real.pi / 2 - δ + t) =
            rotatedSphericalMap A (Real.pi / 2 - δ + s, Real.pi / 2 - δ + t) := by
  obtain ⟨A, c, hp, hcenter, hparam, _hc, _hi, _hs⟩ := exists_regular_spherical_chart p
  have hct : (Real.pi / 2, Real.pi / 2) ∈ c.target := hcenter ▸ c.map_source hp
  obtain ⟨δ, hδ, hδπ, hbox⟩ := spherical_chart_rectangle c hct
  refine ⟨A, c, hp, hcenter, δ, hδ, hδπ, ?_⟩
  intro s hs t ht
  have hmem := hbox (show (Real.pi / 2 - δ + s, Real.pi / 2 - δ + t) ∈
      Icc (Real.pi / 2 - δ) (Real.pi / 2 + δ) ×ˢ Icc (Real.pi / 2 - δ) (Real.pi / 2 + δ) from
      ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩)
  exact ⟨hmem, hparam hmem⟩

example (p q : UnitSphere) :
    ∃ c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ), p ∈ c.source ∧ q ∈ d.source ∧
      ContDiffOn ℝ ω (c.symm.trans d) (c.symm.trans d).source ∧
      ContDiffOn ℝ ω (d.symm.trans c) (d.symm.trans c).source ∧
      ∀ y ∈ (c.symm.trans d).source, (c.symm.trans d).symm ((c.symm.trans d) y) = y := by
  obtain ⟨_A, c, hp, _hpc, _hpa, hc, hci, _hcb⟩ := exists_regular_spherical_chart p
  obtain ⟨_B, d, hq, _hqc, _hqa, hd, hdi, _hdb⟩ := exists_regular_spherical_chart q
  exact ⟨c, d, hp, hq, spherical_chart_transition c d hci hd,
    spherical_chart_transition d c hdi hc, fun _ hy => (c.symm.trans d).left_inv hy⟩

example {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hw : (θ + w.2.1, φ + w.2.2) ∈ c.target) (a b : Fin 4 → ℝ) :
    sphereSpacetimeMetric
      (Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2))
      (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2)
      (c.symm (θ + w.2.1, φ + w.2.2))
      ((a 0, a 1), mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) c.symm (θ + w.2.1, φ + w.2.2) (a 2, a 3))
      ((b 0, b 1), mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) c.symm (θ + w.2.1, φ + w.2.2) (b 2, b 3)) =
        ∑ i, ∑ j, coordinateMetric hU hV x θ w i j * a i * b j :=
  coordinateMetric_spherical_chart_pullback hU hV x θ φ w A c hc hw a b
