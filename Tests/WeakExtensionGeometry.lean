import CauchyHorizon.Reduced.LocalWeakExtension
import CauchyHorizon.Analysis.ProductSobolev
import CauchyHorizon.Geometry.NullHypersurface
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Set MeasureTheory
open scoped Manifold Distributions

namespace CauchyHorizon.Tests

-- Both fields have the ordinary weak derivative identity on the same solution chart.
example {W L e Λ δ : ℝ} {hW : 0 ≤ W} {hL : 0 ≤ L} {y : WaveState W L}
    (hy : HasSphericalWeakSolution hW hL e Λ y) {p : UnitSphere}
    {A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient} {c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)}
    (hc : IsSphericalSolutionChart hW hL e Λ y p A c δ) :
    let θ := Real.pi / 2 - δ
    let K := (Icc 0 W ×ˢ Icc 0 L) ×ˢ (Icc 0 (2 * δ) ×ˢ Icc 0 (2 * δ))
    (∀ i j k : Fin 4, ∀ ψ : 𝓓(openRectangleProduct W L (2 * δ) (2 * δ), ℝ),
      (∫ w in K, coordinateMetric hW hL y θ w i j * fderiv ℝ ψ w (productCoordinate k)) =
        -(∫ w in K, coordinateMetricPartial hW hL y θ k w i j * ψ w)) ∧
    (∀ k : Fin 4, ∀ ψ : 𝓓(openRectangleProduct W L (2 * δ) (2 * δ), ℝ),
      (∫ w in K, chartScalar hW hL y c θ θ w * fderiv ℝ ψ w (productCoordinate k)) =
        -(∫ w in K, chartScalarGradient hW hL y c θ θ w k * ψ w)) := by
  obtain ⟨hδ, hδπ, _hp, _hcenter, _hinv, _hc, _hci, _hbox, _he, hm⟩ := hc
  have hg := hy.2.1 (2 * δ) (2 * δ) (Real.pi / 2 - δ)
    (by positivity) (by positivity) (by linarith) (by linarith)
  exact ⟨fun i j k ψ => ((hg.2.2.1 i j).integral_identity k ψ).2.2,
    fun k ψ => (hm.1.integral_identity k ψ).2.2⟩

-- The retained L2 connection is the unique torsion-free connection for these weak derivatives.
example {W L e Λ A B θ : ℝ} {hW : 0 ≤ W} {hL : 0 ≤ L} {y : WaveState W L}
    (hy : HasSphericalWeakSolution hW hL e Λ y)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi)
    {w : (ℝ × ℝ) × (ℝ × ℝ)}
    (hw : w ∈ (Icc 0 W ×ˢ Icc 0 L) ×ˢ (Icc 0 A ×ˢ Icc 0 B))
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    IsMetricConnection (coordinateMetric hW hL y θ w)
      (fun k => coordinateMetricPartial hW hL y θ k w) Γ ↔
        Γ = coordinateChristoffel hW hL y θ w := by
  have hg := (hy.2.1 A B θ hA hB hθ hθA).2.2.2 w hw
  constructor
  · intro hΓ
    apply hΓ.eq_christoffel
    · intro i j
      exact congrFun (congrFun hg.2.2.2.1 j) i
    · exact hg.2.2.2.2.2.1
  · rintro rfl
    exact (hy.2.2.1 A B θ hA hB hθ hθA).2.2 w hw

-- Use the actual crossing solution and actual image of the original horizon point.
example {U ε e Λ T₀ u₀ : ℝ} {hε : 0 ≤ ε} {hεU : ε ≤ U}
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    (h : HasLocalSphericalWeakExtension hε hεU e Λ X χ T₀ u₀) (p : UnitSphere) :
    let V := regularTime (anchoringLapse (hε.trans hεU) X)
    ∃ ua L T b : ℝ, ∃ hW : 0 ≤ b - V T, ∃ hL : 0 ≤ L,
    ∃ y : WaveState (b - V T) L, ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient,
    ∃ c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ), ∃ δ : ℝ,
      HasSphericalWeakSolution hW hL e Λ y ∧ IsSphericalSolutionChart hW hL e Λ y p A c δ ∧
      let C := sphericalRectangleChart (b - V T) L (2 * δ) (2 * δ) (V T, ua)
        (Real.pi / 2 - δ, Real.pi / 2 - δ) c
      let w₀ := C ((0, u₀), p)
      let θ := Real.pi / 2 - δ
      ((0, u₀), p) ∈ C.source ∧
      C.target = openRectangleProduct (b - V T) L (2 * δ) (2 * δ) ∧
      w₀ = ((-V T, u₀ - ua), (δ, δ)) ∧
      (∃ ψ : 𝓓(openRectangleProduct (b - V T) L (2 * δ) (2 * δ), ℝ), ψ w₀ = 1) ∧
      coordinateMetric hW hL y θ w₀ * coordinateMetricInverse hW hL y θ w₀ = 1 ∧
      coordinateMetricInverse hW hL y θ w₀ 0 0 = 0 ∧
      coordinateMetricInverse hW hL y θ w₀ 1 0 ≠ 0 ∧
      (∀ a : Fin 4 → ℝ, a 0 = 0 →
        0 ≤ (∑ i, ∑ j, coordinateMetric hW hL y θ w₀ i j * a i * a j) ∧
        ((∑ i, ∑ j, coordinateMetric hW hL y θ w₀ i j * a i * a j) = 0 ↔ a 2 = 0 ∧ a 3 = 0)) ∧
      (∀ k i j, MemLp (fun w => coordinateChristoffel hW hL y θ w k i j) 2
        (rectangleProductMeasure (b - V T) L (2 * δ) (2 * δ))) := by
  obtain ⟨_hχ, ua, L, T, b, _hea, _ham, _hmr, _hrU, _hT₀, _hT, _hn, _hb,
    hL, hW, y, hy, _himage, _E, _hE, _hdomain, _hfrontier, _hcausal, _hchar, hcharts, _hpast⟩ := h
  obtain ⟨A, c, δ, hc, htarget, hpoint, hcenter, _hline⟩ := hcharts p
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  let C := sphericalRectangleChart (b - V T) L (2 * δ) (2 * δ) (V T, ua)
    (Real.pi / 2 - δ, Real.pi / 2 - δ) c
  let w₀ := C ((0, u₀), p)
  have hw : w₀ ∈ openRectangleProduct (b - V T) L (2 * δ) (2 * δ) := by
    have hh : w₀ ∈ C.target := C.map_source hpoint
    change C.target = (openRectangleProduct (b - V T) L (2 * δ) (2 * δ) : Set _) at htarget
    rw [htarget] at hh
    exact hh
  have hwK : w₀ ∈ (Icc 0 (b - V T) ×ˢ Icc 0 L) ×ˢ (Icc 0 (2 * δ) ×ˢ Icc 0 (2 * δ)) :=
    ⟨⟨Ioo_subset_Icc_self hw.1.1, Ioo_subset_Icc_self hw.1.2⟩,
      ⟨Ioo_subset_Icc_self hw.2.1, Ioo_subset_Icc_self hw.2.2⟩⟩
  have hδ := hc.1
  have hδπ := hc.2.1
  have hg := (hy.2.1 (2 * δ) (2 * δ) (Real.pi / 2 - δ)
    (by positivity) (by positivity) (by linarith) (by linarith)).2.2.2 w₀ hwK
  have hn (a : Fin 4 → ℝ) (ha : a 0 = 0) := nullMetric_tangent hg.1 hg.2.1 hg.2.2.1 a ha
  refine ⟨ua, L, T, b, hW, hL, y, A, c, δ, hy, hc, hpoint, htarget, hcenter,
    ?_, hg.2.2.2.2.1, (hn 0 rfl).1, (hn 0 rfl).2.1,
    (fun a ha => (hn a ha).2.2.2), ?_⟩
  · obtain ⟨f, hs, hcompact, hd, _hrange, hf⟩ := exists_contDiff_tsupport_subset (n := ⊤)
      ((openRectangleProduct (b - V T) L (2 * δ) (2 * δ)).isOpen.mem_nhds hw)
    exact ⟨⟨f, hd, hcompact, hs⟩, hf⟩
  · exact (hy.2.2.1 (2 * δ) (2 * δ) (Real.pi / 2 - δ)
      (by positivity) (by positivity) (by linarith) (by linarith)).1

end CauchyHorizon.Tests
