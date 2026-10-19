import CauchyHorizon.Geometry.SphericalSource
import CauchyHorizon.Reduced.EinsteinEquation

/-! The Ricci distributions of the actual fields represent one intrinsic spherical source. -/

open Set Filter MeasureTheory
open scoped Manifold ContDiff Distributions

namespace CauchyHorizon

noncomputable def sphericalEinsteinSource {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (v : ℝ × ℝ) (p : UnitSphere) :
    ((ℝ × ℝ) × TangentSpace (𝓡 2) p) →ₗ[ℝ] ((ℝ × ℝ) × TangentSpace (𝓡 2) p) →ₗ[ℝ] ℝ :=
  let z := x.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2)
  sphereEinsteinSource (Real.exp (z 2)) (z 0) e Λ
    (x.2.2 v.1 (projIcc 0 V hV v.2) 1) (x.2.1 (projIcc 0 U hU v.1) (projIcc 0 V hV v.2) 1) p

noncomputable def chartEinsteinSource {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => sphericalEinsteinSource hU hV e Λ x w.1 (c.symm (θ + w.2.1, φ + w.2.2))
    (sphericalChartDifferential c (θ + w.2.1, φ + w.2.2) (Pi.single i 1))
    (sphericalChartDifferential c (θ + w.2.1, φ + w.2.2) (Pi.single j 1))

theorem coordinateEinsteinSource_spherical_pullback {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ))
    (hr : x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ≠ 0)
    (hs : Real.sin (θ + w.2.1) ≠ 0) (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hw : (θ + w.2.1, φ + w.2.2) ∈ c.target) (a b : Fin 4 → ℝ) :
    sphericalEinsteinSource hU hV e Λ x w.1 (c.symm (θ + w.2.1, φ + w.2.2))
      (sphericalChartDifferential c (θ + w.2.1, φ + w.2.2) a)
      (sphericalChartDifferential c (θ + w.2.1, φ + w.2.2) b) =
        ∑ i, ∑ j, coordinateEinsteinSource hU hV e Λ x θ w i j * a i * b j :=
  sphereEinsteinSource_chart_pullback (Real.exp_ne_zero _) hr A c hc hw hs a b

theorem coordinateEinsteinSource_spherical_chart {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ))
    (hr : x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ≠ 0)
    (hs : Real.sin (θ + w.2.1) ≠ 0) (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hw : (θ + w.2.1, φ + w.2.2) ∈ c.target) (i j : Fin 4) :
    chartEinsteinSource hU hV e Λ x c θ φ w i j = coordinateEinsteinSource hU hV e Λ x θ w i j := by
  simpa [chartEinsteinSource, Pi.single_apply] using
    coordinateEinsteinSource_spherical_pullback hU hV e Λ x θ φ w hr hs A c hc hw
      (Pi.single i 1) (Pi.single j 1)

theorem coordinateEinsteinSource_transition {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (v y : ℝ × ℝ)
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
        ∑ i, ∑ j, coordinateEinsteinSource hU hV e Λ x 0 (v, y) i j * a i * b j := by
  let t := c.symm.trans d
  have hcy : y ∈ c.target := hy.1
  have hdy : t y ∈ d.target := d.map_source hy.2
  have h₁ := coordinateEinsteinSource_spherical_pullback hU hV e Λ x 0 0 (v, y) hr
    (by simpa only [zero_add] using hs) A c hc (by simpa only [zero_add, Prod.mk.eta] using hcy) a b
  have h₂ := coordinateEinsteinSource_spherical_pullback hU hV e Λ x 0 0 (v, t y) hr
    (by simpa only [zero_add] using ht) B d hd
    (by simpa only [zero_add, Prod.mk.eta] using hdy)
    (angularVectorChange (fderiv ℝ t y) a) (angularVectorChange (fderiv ℝ t y) b)
  let source (C : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (z : ℝ × ℝ) (a b : Fin 4 → ℝ) :=
    sphericalEinsteinSource hU hV e Λ x v (C.symm z)
      (sphericalChartDifferential C z a) (sphericalChartDifferential C z b)
  have hzero (z : ℝ × ℝ) : (0 + z.1, 0 + z.2) = z := by simp
  have hC := (congrArg (fun z => source c z a b) (hzero y)).symm.trans h₁
  have hD := (congrArg (fun z => source d z (angularVectorChange (fderiv ℝ t y) a)
    (angularVectorChange (fderiv ℝ t y) b)) (hzero (t y))).symm.trans h₂
  apply hD.symm.trans
  apply Eq.trans _ hC
  exact sphereEinsteinSource_chart_transition _ _ _ _ _ _ c d hci hdf hdi hy a b

def HasSphericalRicci {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ) (x : WaveState U V) : Prop :=
  ∀ p : UnitSphere, ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient,
    ∃ c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ), ∃ δ : ℝ,
      0 < δ ∧ δ < Real.pi / 2 ∧ p ∈ c.source ∧ c p = (Real.pi / 2, Real.pi / 2) ∧
      EqOn c.symm (rotatedSphericalMap A) c.target ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω c c.source ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target ∧
      (∀ s ∈ Icc 0 (2 * δ), ∀ t ∈ Icc 0 (2 * δ),
        (Real.pi / 2 - δ + s, Real.pi / 2 - δ + t) ∈ c.target) ∧
      ∀ i j, Integrable (fun w => chartEinsteinSource hU hV e Λ x c
          (Real.pi / 2 - δ) (Real.pi / 2 - δ) w i j) (rectangleProductMeasure U V (2 * δ) (2 * δ)) ∧
        ricciDistribution U V (2 * δ) (2 * δ)
          (coordinateChristoffel hU hV x (Real.pi / 2 - δ)) i j =
            rectangleProductDistribution U V (2 * δ) (2 * δ) (fun w =>
              chartEinsteinSource hU hV e Λ x c (Real.pi / 2 - δ) (Real.pi / 2 - δ) w i j)

theorem HasCoordinateEinsteinEquation.spherical_ricci {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {x : WaveState U V} (hE : HasCoordinateEinsteinEquation hU hV e Λ x)
    (hr : ∀ t s, x.1 t s 0 ≠ 0) : HasSphericalRicci hU hV e Λ x := by
  intro p
  obtain ⟨A, c, hp, hcenter, hparam, hc, hci, _hs⟩ := exists_regular_spherical_chart p
  have hct : (Real.pi / 2, Real.pi / 2) ∈ c.target := hcenter ▸ c.map_source hp
  obtain ⟨δ, hδ, hδπ, hbox⟩ := spherical_chart_rectangle c hct
  have hmem : ∀ s ∈ Icc 0 (2 * δ), ∀ t ∈ Icc 0 (2 * δ),
      (Real.pi / 2 - δ + s, Real.pi / 2 - δ + t) ∈ c.target := by
    intro s hs t ht
    apply hbox
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  refine ⟨A, c, δ, hδ, hδπ, hp, hcenter, hparam, hc, hci, hmem, ?_⟩
  intro i j
  have hθ : 0 < Real.pi / 2 - δ := sub_pos.2 hδπ
  have hθδ : Real.pi / 2 - δ + 2 * δ < Real.pi := by linarith
  have hbase := (hE (2 * δ) (2 * δ) (Real.pi / 2 - δ) (by positivity) (by positivity) hθ hθδ).2.1 i j
  let μ := rectangleProductMeasure U V (2 * δ) (2 * δ)
  let K := (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 (2 * δ) ×ˢ Icc 0 (2 * δ))
  have hAe : ∀ᵐ w ∂μ, w ∈ K := by
    have he : μ = volume.restrict K := by
      simp only [μ, K, rectangleProductMeasure, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [he]
    exact ae_restrict_mem ((measurableSet_Icc.prod measurableSet_Icc).prod
      (measurableSet_Icc.prod measurableSet_Icc))
  have heq : (fun w => coordinateEinsteinSource hU hV e Λ x (Real.pi / 2 - δ) w i j) =ᶠ[ae μ]
      (fun w => chartEinsteinSource hU hV e Λ x c (Real.pi / 2 - δ) (Real.pi / 2 - δ) w i j) := by
    filter_upwards [hAe] with w hw
    exact (coordinateEinsteinSource_spherical_chart hU hV e Λ x _ _ w (hr _ _)
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hw.2.1.1]) (by linarith [hw.2.1.2])))
      A c hparam (hmem _ hw.2.1 _ hw.2.2) i j).symm
  have hL1 := hbase.1.congr heq
  refine ⟨hL1, hbase.2.trans ?_⟩
  ext ψ
  change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ _ ψ =
    TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ _ ψ
  rw [TestFunction.integralAgainstBilinCLM_eq_integral (hbase.1.locallyIntegrable.locallyIntegrableOn _),
    TestFunction.integralAgainstBilinCLM_eq_integral (hL1.locallyIntegrable.locallyIntegrableOn _)]
  apply integral_congr_ae
  filter_upwards [heq] with w hw
  simp only [hw]

end CauchyHorizon
