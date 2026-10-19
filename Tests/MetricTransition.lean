import CauchyHorizon.Reduced.MetricTransition

open CauchyHorizon Set MeasureTheory
open scoped Manifold ContDiff

-- Weak derivatives of the two metric factors can have either sign.
example (y : ℝ × ℝ) :
    nullMetricForm (-2) (-3) y ![1, 0, 0, 0] ![0, 1, 0, 0] = 1 ∧
    nullMetricForm (-2) (-3) y ![0, 0, 0, 1] ![0, 0, 0, 1] = -3 * Real.sin y.1 ^ 2 := by
  norm_num [nullMetricForm, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

-- The Hessian correction has no null component.
example (Q : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (a : Fin 4 → ℝ) :
    angularVectorVariation Q a 0 = 0 ∧ angularVectorVariation Q a 1 = 0 ∧
    angularVectorVariation Q a 2 = (Q (a 2, a 3)).1 ∧
    angularVectorVariation Q a 3 = (Q (a 2, a 3)).2 := ⟨rfl, rfl, rfl, rfl⟩

-- The angular derivative includes both differentiated vector factors.
example (H R : ℝ) (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hd : EqOn d.symm (rotatedSphericalMap B) d.target)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hdf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    {y : ℝ × ℝ} (hy : y ∈ (c.symm.trans d).source) (a b : Fin 4 → ℝ) (h : ℝ × ℝ) :
    let t := c.symm.trans d
    let J := fderiv ℝ t y
    let Q := fderiv ℝ (fderiv ℝ t) y h
    R * (2 * Real.sin y.1 * Real.cos y.1) * h.1 * a 3 * b 3 =
      R * (2 * Real.sin (t y).1 * Real.cos (t y).1) * (J h).1 *
        angularVectorChange J a 3 * angularVectorChange J b 3 +
      nullMetricForm H R (t y) (angularVectorVariation Q a) (angularVectorChange J b) +
      nullMetricForm H R (t y) (angularVectorChange J a) (angularVectorVariation Q b) :=
  nullMetricForm_transition_derivative H R A B c d hc hd hci hdf hdi hy a b h

-- The transformed coefficients are those already identified as genuine L2 weak derivatives.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {z₀ : WaveVector}
    (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (v y α β : ℝ × ℝ) (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hd : EqOn d.symm (rotatedSphericalMap B) d.target)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hdf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    (hy : y ∈ (c.symm.trans d).source) :
    HasL2CoordinateMetric hU hV x ∧
    ∀ ξ a b : Fin 4 → ℝ,
      let t := c.symm.trans d
      let J := fderiv ℝ t y
      let Q := fderiv ℝ (fderiv ℝ t) y (ξ 2, ξ 3)
      let T := angularVectorChange J
      (∑ k, ξ k * ∑ i, ∑ j, coordinateMetricPartial hU hV x α.1 k (v, y - α) i j * a i * b j) =
        (∑ k, T ξ k * ∑ i, ∑ j, coordinateMetricPartial hU hV x β.1 k (v, t y - β) i j * T a i * T b j) +
        (∑ i, ∑ j, coordinateMetric hU hV x β.1 (v, t y - β) i j * angularVectorVariation Q a i * T b j) +
        (∑ i, ∑ j, coordinateMetric hU hV x β.1 (v, t y - β) i j * T a i * angularVectorVariation Q b j) :=
  ⟨hx.coordinate_metric hzin, coordinateMetricPartial_transition hU hV x v y α β A B c d hc hd hci hdf hdi hy⟩
