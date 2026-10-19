import CauchyHorizon.Reduced.SphericalGeometry
import CauchyHorizon.Reduced.RegularCrossing

open CauchyHorizon Set
open scoped InnerProductSpace Manifold ContDiff

example (y : ℝ × ℝ) : sphericalPoint y ∈ Metric.sphere (0 : SphereAmbient) 1 :=
  sphericalPoint_mem y

example (y a b : ℝ × ℝ) :
    unitSphereMetric (sphericalMap y)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) sphericalMap y a)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) sphericalMap y b) =
        a.1 * b.1 + Real.sin y.1 ^ 2 * a.2 * b.2 :=
  unitSphereMetric_pullback y a b

-- The same regular parameter value reaches every sphere point after an orthogonal change of axes.
example (p : UnitSphere) :
    ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient,
      rotatedSphericalMap A (Real.pi / 2, 0) = p ∧
      Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (rotatedSphericalMap A) (Real.pi / 2, 0)) :=
  rotatedSphericalMap_regular_cover p 0

example (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (rotatedSphericalMap A) :=
  rotatedSphericalMap_contMDiff A

example {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V)
    (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (a b : Fin 4 → ℝ) :
    sphereSpacetimeMetric
      (Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2))
      (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2)
      (rotatedSphericalMap A (θ + w.2.1, w.2.2))
      (sphericalSpacetimeDifferential A (θ + w.2.1, w.2.2) a)
      (sphericalSpacetimeDifferential A (θ + w.2.1, w.2.2) b) =
        ∑ i, ∑ j, coordinateMetric hU hV x θ w i j * a i * b j :=
  coordinateMetric_spherical_pullback hU hV x θ w A a b

-- Apply the pointwise geometric identity to the same positive-radius crossing solution.
example {U ε e Λ T₀ u₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    {Z : C(Icc ε U, WaveVector)} {O : C(Icc ε U, ℝ)}
    {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀) :
    ∃ L W : ℝ, ∃ hL : 0 ≤ L, ∃ hW : 0 ≤ W, ∃ y : WaveState W L,
      (∀ t s, 0 < y.1 t s 0) ∧
      ∀ (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (a b : Fin 4 → ℝ),
        sphereSpacetimeMetric
          (Real.exp (y.1 (projIcc 0 W hW w.1.1) (projIcc 0 L hL w.1.2) 2))
          (y.1 (projIcc 0 W hW w.1.1) (projIcc 0 L hL w.1.2) 0 ^ 2)
          (rotatedSphericalMap A (θ + w.2.1, w.2.2))
          (sphericalSpacetimeDifferential A (θ + w.2.1, w.2.2) a)
          (sphericalSpacetimeDifferential A (θ + w.2.1, w.2.2) b) =
            ∑ i, ∑ j, coordinateMetric hW hL y θ w i j * a i * b j := by
  obtain ⟨_ua, L, T, b, _hea, _ham, _hmr, _hrU, _hT₀, _hT, _hn, _hb,
    hL, hW, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, _hfuture, _hout, _hxin, _hbottom,
    hr, _rest⟩ := hcross
  exact ⟨L, _, hL, hW, y, hr, coordinateMetric_spherical_pullback hW hL y⟩
