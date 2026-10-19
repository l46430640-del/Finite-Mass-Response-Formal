import CauchyHorizon.Analysis.RegularTime
import CauchyHorizon.Geometry.SpacetimeChart
import CauchyHorizon.Geometry.SphericalMatter
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! The original late spacetime is openly embedded in the negative regular-time region. -/

open Set
open scoped Manifold ContDiff

namespace CauchyHorizon

theorem IsRegularTimeCoordinate.hasFDerivAt_null_map {a χ : ℝ → ℝ} {T : ℝ}
    (hχ : IsRegularTimeCoordinate a T χ) (w : ℝ × ℝ) :
    HasFDerivAt (fun v : ℝ × ℝ => (regularTime a v.1, v.2))
      (((a w.1) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) w := by
  have hd := (hχ.2.2.2.2.1 w.1).hasFDerivAt.comp w (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have he : (ContinuousLinearMap.toSpanSingleton ℝ (a w.1)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ) = (a w.1) • ContinuousLinearMap.fst ℝ ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    exact mul_comm _ _
  rw [he] at hd
  exact hd.prodMk (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt

theorem IsRegularTimeCoordinate.late_image {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) :
    regularTime a '' Ioi T = Ioo (regularTime a T) 0 := by
  obtain ⟨_hc, _hp, _hi, hm, _hd, hn, _htop, _himage, _hχc, _hχtop, hinv, _hleft⟩ := hχ
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨hm ht, hn t⟩
  · intro hw
    have hh := hinv w ⟨(hm.monotone hT).trans_lt hw.1, hw.2⟩
    refine ⟨χ w, ?_, hh.2.1⟩
    exact hm.lt_iff_lt.1 (by rw [hh.2.1]; exact hw.1)

theorem IsRegularTimeCoordinate.contDiff {a χ : ℝ → ℝ} {T : ℝ}
    (hχ : IsRegularTimeCoordinate a T χ) : ContDiff ℝ 1 (regularTime a) := by
  have hd := hχ.2.2.2.2.1
  apply contDiff_one_iff_deriv.2
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  have he : deriv (regularTime a) = a := funext fun t => (hd t).deriv
  rw [he]
  exact hχ.1

theorem IsRegularTimeCoordinate.inverse_contDiffOn {a χ : ℝ → ℝ} {T : ℝ}
    (hχ : IsRegularTimeCoordinate a T χ) : ContDiffOn ℝ 1 χ (Ioo (regularTime a T) 0) := by
  obtain ⟨hc, hp, _hi, _hm, _hd, _hn, _htop, _himage, hχc, _hχtop, hinv, _hleft⟩ := hχ
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).2
  refine ⟨fun t ht => (hinv t ht).2.2.differentiableAt.differentiableWithinAt, ?_⟩
  have hcont : ContinuousOn (fun t => 1 / a (χ t)) (Ioo (regularTime a T) 0) :=
    continuousOn_const.div (hc.comp_continuousOn hχc) (fun t _ => (hp (χ t)).ne')
  apply hcont.congr
  intro t ht
  exact (hinv t ht).2.2.hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffOn t ht)

noncomputable def regularTimeChart {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) : OpenPartialHomeomorph ℝ ℝ where
  toFun := regularTime a
  invFun := χ
  source := Ioi T
  target := Ioo (regularTime a T) 0
  map_source' t ht := ⟨hχ.2.2.2.1 ht, hχ.2.2.2.2.2.1 t⟩
  map_target' t ht := by
    obtain ⟨s, hs, he⟩ := (hχ.late_image hT).symm ▸ ht
    rw [← he, hχ.2.2.2.2.2.2.2.2.2.2.2 s (hT.trans_lt hs)]
    exact hs
  left_inv' t ht := hχ.2.2.2.2.2.2.2.2.2.2.2 t (hT.trans_lt ht)
  right_inv' t ht := (hχ.2.2.2.2.2.2.2.2.2.2.1 t
    ⟨(hχ.2.2.2.1.monotone hT).trans_lt ht.1, ht.2⟩).2.1
  open_source := isOpen_Ioi
  open_target := isOpen_Ioo
  continuousOn_toFun := hχ.contDiff.continuous.continuousOn
  continuousOn_invFun := hχ.inverse_contDiffOn.continuousOn.mono
    (fun _ ht => ⟨(hχ.2.2.2.1.monotone hT).trans_lt ht.1, ht.2⟩)

noncomputable def regularSpacetimeEmbedding {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ) :
    OpenPartialHomeomorph ((ℝ × ℝ) × UnitSphere) ((ℝ × ℝ) × UnitSphere) :=
  ((regularTimeChart hχ hT).prod (OpenPartialHomeomorph.ofSet (Ioo ua ub) isOpen_Ioo)).prod
    (OpenPartialHomeomorph.refl UnitSphere)

theorem regularSpacetimeEmbedding_apply {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ)
    (w : (ℝ × ℝ) × UnitSphere) :
    regularSpacetimeEmbedding hχ hT ua ub w = ((regularTime a w.1.1, w.1.2), w.2) := rfl

theorem regularSpacetimeEmbedding_symm_apply {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ)
    (w : (ℝ × ℝ) × UnitSphere) :
    (regularSpacetimeEmbedding hχ hT ua ub).symm w = ((χ w.1.1, w.1.2), w.2) := rfl

theorem regularSpacetimeEmbedding_source {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ) :
    (regularSpacetimeEmbedding hχ hT ua ub).source = (Ioi T ×ˢ Ioo ua ub) ×ˢ univ := rfl

theorem regularSpacetimeEmbedding_target {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ) :
    (regularSpacetimeEmbedding hχ hT ua ub).target =
      (Ioo (regularTime a T) 0 ×ˢ Ioo ua ub) ×ˢ univ := rfl

theorem regularSpacetimeEmbedding_frontier {a χ : ℝ → ℝ} {T₀ T ua ub u₀ : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (hu : u₀ ∈ Ioo ua ub) (p : UnitSphere) :
    ((0, u₀), p) ∈ frontier (regularSpacetimeEmbedding hχ hT ua ub).target := by
  rw [frontier, (regularSpacetimeEmbedding hχ hT ua ub).open_target.interior_eq,
    regularSpacetimeEmbedding_target, closure_prod_eq, closure_prod_eq,
    closure_Ioo (hχ.2.2.2.2.2.1 T).ne, closure_Ioo (hu.1.trans hu.2).ne, closure_univ]
  exact ⟨⟨⟨⟨(hχ.2.2.2.2.2.1 T).le, le_rfl⟩, ⟨hu.1.le, hu.2.le⟩⟩, mem_univ _⟩,
    fun hh => (lt_irrefl (0 : ℝ)) hh.1.1.2⟩

theorem regularSpacetimeEmbedding_mfderiv {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ)
    (w : (ℝ × ℝ) × UnitSphere) (ξ : (ℝ × ℝ) × TangentSpace (𝓡 2) w.2) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2))
      (regularSpacetimeEmbedding hχ hT ua ub) w ξ = ((a w.1.1 * ξ.1.1, ξ.1.2), ξ.2) := by
  change mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2))
    (Prod.map (fun v : ℝ × ℝ => (regularTime a v.1, v.2)) (id : UnitSphere → UnitSphere)) w ξ = _
  rw [mfderiv_prodMap (hχ.hasFDerivAt_null_map w.1).hasMFDerivAt.mdifferentiableAt
    mdifferentiableAt_id, mfderiv_eq_fderiv, (hχ.hasFDerivAt_null_map w.1).fderiv, mfderiv_id]
  rfl

theorem regularSpacetimeEmbedding_contMDiff {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) 1
        (regularSpacetimeEmbedding hχ hT ua ub) ∧
      ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) 1
        (regularSpacetimeEmbedding hχ hT ua ub).symm (regularSpacetimeEmbedding hχ hT ua ub).target := by
  have hf : ContDiff ℝ 1 (fun v : ℝ × ℝ => (regularTime a v.1, v.2)) :=
    (hχ.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hχlate : ContDiffOn ℝ 1 χ (Ioo (regularTime a T) 0) :=
    hχ.inverse_contDiffOn.mono (fun _ ht => ⟨(hχ.2.2.2.1.monotone hT).trans_lt ht.1, ht.2⟩)
  have hg : ContDiffOn ℝ 1 (fun v : ℝ × ℝ => (χ v.1, v.2))
      (Ioo (regularTime a T) 0 ×ˢ Ioo ua ub) :=
    (hχlate.comp contDiff_fst.contDiffOn (fun _ hw => hw.1)).prodMk contDiff_snd.contDiffOn
  exact ⟨hf.contMDiff.prodMap contMDiff_id, hg.contMDiffOn.prodMap contMDiff_id.contMDiffOn⟩

theorem regularSpacetimeEmbedding_symm_mfderiv {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ)
    (w : (ℝ × ℝ) × UnitSphere) (hw : w ∈ (regularSpacetimeEmbedding hχ hT ua ub).target)
    (ξ : (ℝ × ℝ) × TangentSpace (𝓡 2) w.2) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2))
      (regularSpacetimeEmbedding hχ hT ua ub).symm w ξ =
        (((1 / a (χ w.1.1)) * ξ.1.1, ξ.1.2), ξ.2) := by
  have hi := (hχ.2.2.2.2.2.2.2.2.2.2.1 w.1.1
    ⟨(hχ.2.2.2.1.monotone hT).trans_lt hw.1.1.1, hw.1.1.2⟩).2.2
  have hd := hi.hasFDerivAt.prodMap w.1 (hasFDerivAt_id w.1.2)
  change mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2))
    (Prod.map (Prod.map χ id) (id : UnitSphere → UnitSphere)) w ξ = _
  rw [mfderiv_prodMap hd.hasMFDerivAt.mdifferentiableAt mdifferentiableAt_id,
    mfderiv_eq_fderiv, hd.fderiv, mfderiv_id]
  change ((ξ.1.1 * (1 / a (χ w.1.1)), ξ.1.2), ξ.2) = _
  rw [mul_comm ξ.1.1]

theorem sphereElectricForm_time_change {f f' a : ℝ} (hf : f' * a = f)
    (p : UnitSphere) (ξ η : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphereElectricForm f' p ![((a * ξ.1.1, ξ.1.2), ξ.2), ((a * η.1.1, η.1.2), η.2)] =
      sphereElectricForm f p ![ξ, η] := by
  simp only [sphereElectricForm_apply]
  rw [← hf]
  ring

def IsRegularSpacetimeEmbedding (a χ : ℝ → ℝ) (T ua ub : ℝ)
    (E : OpenPartialHomeomorph ((ℝ × ℝ) × UnitSphere) ((ℝ × ℝ) × UnitSphere)) : Prop :=
  E.source = (Ioi T ×ˢ Ioo ua ub) ×ˢ univ ∧
  E.target = (Ioo (regularTime a T) 0 ×ˢ Ioo ua ub) ×ˢ univ ∧
  (∀ w, E w = ((regularTime a w.1.1, w.1.2), w.2)) ∧
  (∀ w, E.symm w = ((χ w.1.1, w.1.2), w.2)) ∧
  ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) 1 E E.source ∧
  ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) 1 E.symm E.target ∧
  (∀ (w : (ℝ × ℝ) × UnitSphere) (ξ : (ℝ × ℝ) × TangentSpace (𝓡 2) w.2),
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) E w ξ =
      ((a w.1.1 * ξ.1.1, ξ.1.2), ξ.2)) ∧
  ∀ (w : (ℝ × ℝ) × UnitSphere), w ∈ E.target → ∀ ξ : (ℝ × ℝ) × TangentSpace (𝓡 2) w.2,
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) E.symm w ξ =
      (((1 / a (χ w.1.1)) * ξ.1.1, ξ.1.2), ξ.2)

theorem regularSpacetimeEmbedding_spec {a χ : ℝ → ℝ} {T₀ T : ℝ}
    (hχ : IsRegularTimeCoordinate a T₀ χ) (hT : T₀ ≤ T) (ua ub : ℝ) :
    IsRegularSpacetimeEmbedding a χ T ua ub (regularSpacetimeEmbedding hχ hT ua ub) :=
  ⟨rfl, rfl, regularSpacetimeEmbedding_apply hχ hT ua ub,
    regularSpacetimeEmbedding_symm_apply hχ hT ua ub,
    (regularSpacetimeEmbedding_contMDiff hχ hT ua ub).1.contMDiffOn,
    (regularSpacetimeEmbedding_contMDiff hχ hT ua ub).2,
    regularSpacetimeEmbedding_mfderiv hχ hT ua ub,
    regularSpacetimeEmbedding_symm_mfderiv hχ hT ua ub⟩

end CauchyHorizon
