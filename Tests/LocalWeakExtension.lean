import CauchyHorizon.Reduced.LocalWeakExtension

open Set MeasureTheory
open scoped Manifold

namespace CauchyHorizon.Tests

example (W L A B : ℝ) (a b : ℝ × ℝ)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    (sphericalRectangleChart W L A B a b c).symm w = (w.1 + a, c.symm (w.2 + b)) :=
  sphericalRectangleChart_symm_apply W L A B a b c w

-- The horizon and explicit points on both sides belong to one open spacetime neighborhood.
example {vT b ua L u₀ δ : ℝ} (hn : vT < 0) (hb : 0 < b)
    (hδ : 0 < δ) (hua : ua < u₀) (huL : u₀ < ua + L)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) {p : UnitSphere}
    (hp : p ∈ c.source) (hcenter : c p = (Real.pi / 2, Real.pi / 2))
    (hbox : ∀ s ∈ Icc 0 (2 * δ), ∀ t ∈ Icc 0 (2 * δ),
      (Real.pi / 2 - δ + s, Real.pi / 2 - δ + t) ∈ c.target) :
    let C := sphericalRectangleChart (b - vT) L (2 * δ) (2 * δ) (vT, ua)
      (Real.pi / 2 - δ, Real.pi / 2 - δ) c
    IsOpen C.source ∧ ((0, u₀), p) ∈ C.source ∧
      ((vT / 2, u₀), p) ∈ C.source ∧ ((b / 2, u₀), p) ∈ C.source ∧
      C.target = openRectangleProduct (b - vT) L (2 * δ) (2 * δ) := by
  have h := sphericalRectangleChart_null_line (vT := vT) (b := b) hδ hua huL c hp hcenter hbox
  exact ⟨OpenPartialHomeomorph.open_source _, h.2 0 ⟨hn, hb⟩,
    h.2 (vT / 2) ⟨by linarith, by linarith⟩, h.2 (b / 2) ⟨by linarith, by linarith⟩, h.1⟩

example {a χ : ℝ → ℝ} {T : ℝ} (hχ : IsRegularTimeCoordinate a T χ) (w : ℝ × ℝ) :
    HasFDerivAt (fun v : ℝ × ℝ => (regularTime a v.1, v.2))
      (((a w.1) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) w :=
  hχ.hasFDerivAt_null_map w

example {a χ : ℝ → ℝ} {T : ℝ} (hχ : IsRegularTimeCoordinate a 0 χ) (hT : 0 ≤ T) :
    regularTime a '' Ioi T = Ioo (regularTime a T) 0 := hχ.late_image hT

-- The full sphere metric, including angular tangent vectors, is preserved by the lapse rescaling.
example (ell anchor R : ℝ) (p : UnitSphere) (ξ η : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphereSpacetimeMetric (Real.exp (ell - anchor)) R p
      ((Real.exp anchor * ξ.1.1, ξ.1.2), ξ.2) ((Real.exp anchor * η.1.1, η.1.2), η.2) =
      sphereSpacetimeMetric (Real.exp ell) R p ξ η := by
  apply sphereSpacetimeMetric_time_change
  rw [← Real.exp_add, sub_add_cancel]

example {U ε e Λ T₀ u₀ : ℝ} {hε : 0 ≤ ε} {hεU : ε ≤ U}
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    {Z : C(Icc ε U, WaveVector)} {O : C(Icc ε U, ℝ)}
    {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hrX : ∀ (S : Ici (0 : ℝ)) u v, 0 < (X S).1 u v 0)
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh) :
    HasLocalSphericalWeakExtension hε hεU e Λ X χ T₀ u₀ :=
  hcross.local_weak_extension hX hrX hχ hB

-- The solution is chosen before the sphere point, and both null intervals have positive length.
example {U ε e Λ T₀ u₀ : ℝ} {hε : 0 ≤ ε} {hεU : ε ≤ U}
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    (h : HasLocalSphericalWeakExtension hε hεU e Λ X χ T₀ u₀) :
    ∃ W L : ℝ, ∃ hW : 0 < W, ∃ hL : 0 < L, ∃ y : WaveState W L,
      HasL2CoordinateMetric hW.le hL.le y ∧ HasL2CoordinateConnection hW.le hL.le y ∧
        HasSphericalFieldEquations hW.le hL.le e Λ y := by
  obtain ⟨_hχ, ua, L, T, b, _hea, ham, hmr, _hrU, _hT₀, _hT, hn, hb,
    hL, hW, y, hy, _himage, _E, _hE, _hdomain, _hfrontier, _hcausal, _hchar, _hcharts, _hpast⟩ := h
  have hWp : 0 < b - regularTime (anchoringLapse (hε.trans hεU) X) T := by linarith
  have hLp : 0 < L := by linarith
  exact ⟨_, L, hWp, hLp, y, hy.2.1, hy.2.2.1, hy.2.2.2.2⟩

example {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ) :
    let E := regularSpacetimeEmbedding hχ hT ua ub
    Topology.IsOpenEmbedding (E.source.domRestrict E) :=
  (regularSpacetimeEmbedding hχ hT ua ub).isOpenEmbedding_restrict

example {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ)
    (w : (ℝ × ℝ) × UnitSphere) (hw : w ∈ (Ioi T ×ˢ Ioo ua ub) ×ˢ univ) :
    (regularSpacetimeEmbedding hχ hT ua ub).symm
      (regularSpacetimeEmbedding hχ hT ua ub w) = w :=
  (regularSpacetimeEmbedding hχ hT ua ub).left_inv hw

example {a χ : ℝ → ℝ} {T₀ T ua ub u₀ : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (hu : u₀ ∈ Ioo ua ub) (p : UnitSphere) :
    let E := regularSpacetimeEmbedding hχ hT ua ub
    ((0, u₀), p) ∈ frontier E.target ∧ ((0, u₀), p) ∉ E.target := by
  refine ⟨regularSpacetimeEmbedding_frontier hχ hT hu p, ?_⟩
  intro hh
  exact (lt_irrefl (0 : ℝ)) hh.1.1.2

example {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ) :
    let E := regularSpacetimeEmbedding hχ hT ua ub
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) 1 E E.source ∧
      ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) 1 E.symm E.target :=
  ⟨(regularSpacetimeEmbedding_contMDiff hχ hT ua ub).1.contMDiffOn,
    (regularSpacetimeEmbedding_contMDiff hχ hT ua ub).2⟩

example {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ)
    (w : (ℝ × ℝ) × UnitSphere) (hw : w ∈ (regularSpacetimeEmbedding hχ hT ua ub).target)
    (ξ : (ℝ × ℝ) × TangentSpace (𝓡 2) w.2) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2))
      (regularSpacetimeEmbedding hχ hT ua ub) w ξ = ((a w.1.1 * ξ.1.1, ξ.1.2), ξ.2) ∧
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2))
      (regularSpacetimeEmbedding hχ hT ua ub).symm w ξ =
        (((1 / a (χ w.1.1)) * ξ.1.1, ξ.1.2), ξ.2) :=
  ⟨regularSpacetimeEmbedding_mfderiv hχ hT ua ub w ξ,
    regularSpacetimeEmbedding_symm_mfderiv hχ hT ua ub w hw ξ⟩

-- The electric two-form retains its du wedge dV orientation under the actual time change.
example (e ell anchor r : ℝ) (p : UnitSphere) (ξ η : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphereElectricForm (e * Real.exp (ell - anchor) / (2 * r ^ 2)) p
      ![((Real.exp anchor * ξ.1.1, ξ.1.2), ξ.2), ((Real.exp anchor * η.1.1, η.1.2), η.2)] =
      sphereElectricForm (e * Real.exp ell / (2 * r ^ 2)) p ![ξ, η] := by
  apply sphereElectricForm_time_change
  calc
    _ = e * (Real.exp (ell - anchor) * Real.exp anchor) / (2 * r ^ 2) := by ring
    _ = _ := by rw [← Real.exp_add, sub_add_cancel]

example {U ε e Λ T₀ u₀ : ℝ} {hε : 0 ≤ ε} {hεU : ε ≤ U}
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    (h : HasLocalSphericalWeakExtension hε hεU e Λ X χ T₀ u₀) :
    ∃ Ω : Set ((ℝ × ℝ) × UnitSphere),
    ∃ E : OpenPartialHomeomorph ((ℝ × ℝ) × UnitSphere) ((ℝ × ℝ) × UnitSphere),
      IsOpen Ω ∧ E.target ⊆ Ω ∧ Topology.IsOpenEmbedding (E.source.domRestrict E) ∧
        ∀ p : UnitSphere, ((0, u₀), p) ∈ Ω ∩ frontier E.target := by
  obtain ⟨_hχ, ua, L, T, b, _hea, ham, hmr, _hrU, _hT₀, _hT, hn, hb,
    _hL, _hW, _y, _hy, _himage, E, _hE, hdomain, hfrontier, _hcausal, _hchar, _hcharts, _hpast⟩ := h
  refine ⟨_, E, (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_univ, hdomain,
    E.isOpenEmbedding_restrict, ?_⟩
  intro p
  exact ⟨⟨⟨⟨hn, hb⟩, ⟨ham, hmr⟩⟩, mem_univ p⟩, hfrontier p⟩

end CauchyHorizon.Tests
