import CauchyHorizon.Reduced.RegularCrossing

open CauchyHorizon Set MeasureTheory
open scoped Manifold ContDiff Distributions

-- The null component retains the scalar cross term and opposite electric/cosmological signs.
example (H r e Λ pV pu : ℝ) (p : UnitSphere) :
    sphereEinsteinSource H r e Λ pV pu p ((1, 0), 0) ((0, 1), 0) =
      2 * pV * pu + H * (e ^ 2 / r ^ 4 - Λ) / 2 := by
  simp only [sphereEinsteinSource_apply, sphereSpacetimeMetric, unitSphereMetric,
    map_zero, inner_zero_left]
  ring

-- Angular components are the round-sphere form, with no dependence on the choice of axes.
example (H r e Λ pV pu : ℝ) (p : UnitSphere) (a b : TangentSpace (𝓡 2) p) :
    sphereEinsteinSource H r e Λ pV pu p ((0, 0), a) ((0, 0), b) =
      (Λ * r ^ 2 + e ^ 2 / r ^ 2) * unitSphereMetric p a b ∧
      sphereEinsteinSource H r e Λ pV pu p ((0, 0), a) ((0, 0), b) =
        sphereEinsteinSource H r e Λ pV pu p ((0, 0), b) ((0, 0), a) := by
  exact ⟨by simp [sphereEinsteinSource_apply, sphereSpacetimeMetric],
    sphereEinsteinSource_symmetric H r e Λ pV pu p _ _⟩

example {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ) (x : WaveState U V) (v y : ℝ × ℝ)
    (hr : x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2) 0 ≠ 0)
    (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hd : EqOn d.symm (rotatedSphericalMap B) d.target)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hdf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    (hy : y ∈ (c.symm.trans d).source) (hs : Real.sin y.1 ≠ 0)
    (ht : Real.sin ((c.symm.trans d) y).1 ≠ 0) (a b : Fin 4 → ℝ) :
    let t := c.symm.trans d
    (∑ i, ∑ j, coordinateEinsteinSource hU hV e Λ x 0 (v, t y) i j *
      angularVectorChange (fderiv ℝ t y) a i * angularVectorChange (fderiv ℝ t y) b j) =
        ∑ i, ∑ j, coordinateEinsteinSource hU hV e Λ x 0 (v, y) i j * a i * b j :=
  coordinateEinsteinSource_transition hU hV e Λ x v y hr A B c d hc hd hci hdf hdi hy hs ht a b

-- Every sphere point has an actual chart on which all Ricci distributions have these L1 densities.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V} {x : WaveState U V}
    (hE : HasCoordinateEinsteinEquation hU hV e Λ x) (hr : ∀ t s, x.1 t s 0 ≠ 0) :
    HasSphericalRicci hU hV e Λ x :=
  hE.spherical_ricci hr

-- This is the same crossing solution with its original positive radius and all sphere points.
example {U ε e Λ T₀ u₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    {Z : C(Icc ε U, WaveVector)} {O : C(Icc ε U, ℝ)}
    {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀) :
    ∃ L W : ℝ, ∃ hL : 0 ≤ L, ∃ hW : 0 ≤ W, ∃ y : WaveState W L,
      (∀ t s, 0 < y.1 t s 0) ∧ HasSphericalRicci hW hL e Λ y := by
  obtain ⟨_ua, L, T, b, _hea, _ham, _hmr, _hrU, _hT₀, _hT, _hn, _hb,
    hL, hW, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, _hfuture, _hout, _hxin, _hbottom,
    hr, _hmatch, _hvelocity, _hc, _hi, _hweak, _hdistribution, _hL2, _hmetric, _hcoord, _hconnection,
    _hRicci, _hsource, _hmixed, _hangular, _hoffdiag, _hmaxwell, _heinstein, _hscalar, hsphere, _rest⟩ := hcross
  exact ⟨L, _, hL, hW, y, hr, hsphere⟩
