import CauchyHorizon.Geometry.SphericalMetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Local inverse maps turn the regular spherical parameterizations into genuine charts. -/

open Set Filter ChartedSpace
open scoped Manifold ContDiff Topology

namespace CauchyHorizon

theorem sphere_local_coordinates {f : ℝ × ℝ → UnitSphere} {a : ℝ × ℝ}
    (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω f)
    (hd : Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f a))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (haU : a ∈ U) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) UnitSphere,
      a ∈ e.source ∧ EqOn e f e.source ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω e e.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω e.symm e.target ∧ e.source ⊆ U := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (f a)
  have hca : f a ∈ c.source := mem_chart_source _ _
  have hc : ContMDiffAt (𝓡 2) (𝓡 2) ω c (f a) :=
    (contMDiffOn_chart (I := 𝓡 2)).contMDiffAt (c.open_source.mem_nhds hca)
  let g := c ∘ f
  have hg : ContDiffAt ℝ ω g a := (hc.comp a (hf a)).contDiffAt
  have hgb : Function.Bijective (fderiv ℝ g a) := by
    rw [← mfderiv_eq_fderiv]
    change Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (c ∘ f) a)
    rw [mfderiv_comp a (hc.mdifferentiableAt (by simp)) ((hf a).mdifferentiableAt (by simp))]
    exact ((mdifferentiable_chart (I := 𝓡 2) (f a)).mfderiv_bijective hca).comp hd
  let D : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ g a)
      (LinearMap.ker_eq_bot.2 hgb.1) (LinearMap.range_eq_top.2 hgb.2)
  have hD : HasFDerivAt g (D : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)) a :=
    (hg.differentiableAt (by simp)).hasFDerivAt
  let b := hg.toOpenPartialHomeomorph g hD (by simp)
  have hab : a ∈ b.source := hg.mem_toOpenPartialHomeomorph_source hD (by simp)
  let e := b.trans c.symm
  have hae : a ∈ e.source := ⟨hab, c.map_source hca⟩
  have heq (x : ℝ × ℝ) (hx : f x ∈ c.source) : e x = f x := c.left_inv hx
  let W := (f ⁻¹' c.source) ∩ U
  have hW : IsOpen W := (c.open_source.preimage hf.continuous).inter hU
  let e' := e.restr W
  have hae' : a ∈ e'.source := by
    rw [OpenPartialHomeomorph.restr_source' e W hW]
    exact ⟨hae, hca, haU⟩
  have heq' : EqOn e' f e'.source := by
    intro x hx
    rw [OpenPartialHomeomorph.restr_source' e W hW] at hx
    exact heq x hx.2.1
  have hfa : f a ∈ e'.target := (heq' hae') ▸ e'.map_source hae'
  have hi : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω e'.symm (f a) := by
    have hb : ContDiffAt ℝ ω b.symm (g a) := hg.to_localInverse hD (by simp)
    change ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω (b.symm ∘ c) (f a)
    exact hb.contMDiffAt.comp (f a) hc
  obtain ⟨V, hV, hVi⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hi
  obtain ⟨O, hOV, hO, hfaO⟩ := mem_nhds_iff.1 hV
  let q := (e'.symm.restr O).symm
  have hfq : f a ∈ q.target := by
    change f a ∈ (e'.symm.restr O).source
    rw [OpenPartialHomeomorph.restr_source' _ O hO]
    exact ⟨hfa, hfaO⟩
  have hqi : q.symm (f a) = a := by
    change e'.symm (f a) = a
    rw [← heq' hae']
    exact e'.left_inv hae'
  have haq : a ∈ q.source := hqi ▸ q.map_target hfq
  have hqs : q.source ⊆ e'.source := fun _ hx => hx.1
  have hqt : q.target ⊆ V := by
    intro p hp
    change p ∈ (e'.symm.restr O).source at hp
    rw [OpenPartialHomeomorph.restr_source' _ O hO] at hp
    exact hOV hp.2
  have hqf : EqOn q f q.source := fun x hx => heq' (hqs hx)
  refine ⟨q, haq, hqf, hf.contMDiffOn.congr hqf, hVi.mono hqt, ?_⟩
  intro x hx
  have hs := hqs hx
  rw [OpenPartialHomeomorph.restr_source' e W hW] at hs
  exact hs.2.2

theorem exists_regular_spherical_chart (p : UnitSphere) :
    ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient, ∃ c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ),
      p ∈ c.source ∧ c p = (Real.pi / 2, Real.pi / 2) ∧
      EqOn c.symm (rotatedSphericalMap A) c.target ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω c c.source ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target ∧
      c.target ⊆ Ioo 0 Real.pi ×ˢ Ioo 0 Real.pi := by
  obtain ⟨A, hA, hD⟩ := rotatedSphericalMap_regular_cover p (Real.pi / 2)
  obtain ⟨e, he, heq, hf, hi, hs⟩ := sphere_local_coordinates
    (rotatedSphericalMap_contMDiff (n := ω) A) hD (isOpen_Ioo.prod isOpen_Ioo)
    (show (Real.pi / 2, Real.pi / 2) ∈ Ioo 0 Real.pi ×ˢ Ioo 0 Real.pi from
      ⟨⟨by positivity, by linarith [Real.pi_pos]⟩, ⟨by positivity, by linarith [Real.pi_pos]⟩⟩)
  have hep : e (Real.pi / 2, Real.pi / 2) = p := (heq he).trans hA
  refine ⟨A, e.symm, hep ▸ e.map_source he, ?_, heq, hi, hf, hs⟩
  rw [← hep]
  exact e.left_inv he

theorem spherical_chart_transition (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hd : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source) :
    ContDiffOn ℝ ω (c.symm.trans d) (c.symm.trans d).source :=
  (hd.comp (hc.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn

theorem spherical_chart_transition_derivatives (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω c c.source)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hd : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    {y : ℝ × ℝ} (hy : y ∈ (c.symm.trans d).source) :
    let t := c.symm.trans d
    (fderiv ℝ t.symm (t y)).comp (fderiv ℝ t y) = ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
      (fderiv ℝ t y).comp (fderiv ℝ t.symm (t y)) = ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
      IsSymmSndFDerivAt ℝ t y := by
  let t := c.symm.trans d
  have hf : ContDiffAt ℝ ω t y :=
    (spherical_chart_transition c d hci hd).contDiffAt (t.open_source.mem_nhds hy)
  have hi : ContDiffAt ℝ ω t.symm (t y) :=
    (spherical_chart_transition d c hdi hc).contDiffAt (t.open_target.mem_nhds (t.map_source hy))
  have hleft : (t.symm ∘ t) =ᶠ[𝓝 y] id :=
    Filter.eventuallyEq_of_mem (t.open_source.mem_nhds hy) (fun _ hz => t.left_inv hz)
  have hright : (t ∘ t.symm) =ᶠ[𝓝 (t y)] id :=
    Filter.eventuallyEq_of_mem (t.open_target.mem_nhds (t.map_source hy)) (fun _ hz => t.right_inv hz)
  have hF := (hf.differentiableAt (by simp)).hasFDerivAt
  have hI := (hi.differentiableAt (by simp)).hasFDerivAt
  refine ⟨?_, ?_, hf.isSymmSndFDerivAt_of_omega⟩
  · have h := (hI.comp y hF).fderiv
    rw [hleft.fderiv_eq] at h
    simpa only [fderiv_id] using h.symm
  · have hF' : HasFDerivAt t (fderiv ℝ t y) (t.symm (t y)) := by
      simpa only [t.left_inv hy] using hF
    have h := (hF'.comp (t y) hI).fderiv
    rw [hright.fderiv_eq] at h
    simpa only [fderiv_id] using h.symm

noncomputable def sphericalChartDifferential (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (y : ℝ × ℝ) (a : Fin 4 → ℝ) : (ℝ × ℝ) × TangentSpace (𝓡 2) (c.symm y) :=
  ((a 0, a 1), mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) c.symm y (a 2, a 3))

def angularVectorChange (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (a : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a 0, a 1, (L (a 2, a 3)).1, (L (a 2, a 3)).2]

theorem sphericalChartDifferential_transition (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hd : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    {y : ℝ × ℝ} (hy : y ∈ (c.symm.trans d).source) (a : Fin 4 → ℝ) :
    let t := c.symm.trans d
    sphericalChartDifferential d (t y) (angularVectorChange (fderiv ℝ t y) a) =
      sphericalChartDifferential c y a := by
  let t := c.symm.trans d
  have ht : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) t y :=
    ((spherical_chart_transition c d hci hd).contDiffAt (t.open_source.mem_nhds hy)).contMDiffAt.mdifferentiableAt (by simp)
  have hD : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (𝓡 2) d.symm (t y) :=
    (hdi.contMDiffAt (d.open_target.mem_nhds (d.map_source hy.2))).mdifferentiableAt (by simp)
  have heq : (d.symm ∘ t) =ᶠ[𝓝 y] c.symm :=
    Filter.eventuallyEq_of_mem (t.open_source.mem_nhds hy) (fun _ hz => d.left_inv hz.2)
  have h := mfderiv_comp y hD ht
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at h
  change ((a 0, a 1), (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) d.symm (t y))
      (fderiv ℝ t y (a 2, a 3))) =
    ((a 0, a 1), (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) c.symm y) (a 2, a 3))
  exact congrArg (fun v : EuclideanSpace ℝ (Fin 2) => ((a 0, a 1), v))
    (congrArg (fun L => L (a 2, a 3)) h).symm

theorem spherical_chart_metric_pullback (H R : ℝ)
    (A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target) {y : ℝ × ℝ} (hy : y ∈ c.target)
    (a b : Fin 4 → ℝ) :
    sphereSpacetimeMetric H R (c.symm y)
      ((a 0, a 1), mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) c.symm y (a 2, a 3))
      ((b 0, b 1), mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) c.symm y (b 2, b 3)) =
        ∑ i, ∑ j, nullMetricMatrix H R (Real.sin y.1 ^ 2) i j * a i * b j := by
  have heq : c.symm =ᶠ[𝓝 y] rotatedSphericalMap A :=
    Filter.eventuallyEq_of_mem (c.open_target.mem_nhds hy) hc
  rw [heq.mfderiv_eq (I := 𝓘(ℝ, ℝ × ℝ)) (I' := 𝓡 2), hc hy]
  exact sphereSpacetimeMetric_pullback H R A y a b

theorem spherical_chart_rectangle (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : (Real.pi / 2, Real.pi / 2) ∈ c.target) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / 2 ∧
      Icc (Real.pi / 2 - δ) (Real.pi / 2 + δ) ×ˢ
        Icc (Real.pi / 2 - δ) (Real.pi / 2 + δ) ⊆ c.target := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 c.open_target _ hc
  let δ := min (r / 2) (Real.pi / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hδπ : δ < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  refine ⟨δ, hδ, hδπ, ?_⟩
  intro x hx
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor
  · rw [abs_lt]
    constructor <;> linarith [hx.1.1, hx.1.2]
  · rw [abs_lt]
    constructor <;> linarith [hx.2.1, hx.2.2]

end CauchyHorizon
