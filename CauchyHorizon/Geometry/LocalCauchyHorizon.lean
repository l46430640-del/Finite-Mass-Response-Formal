import CauchyHorizon.Geometry.SphericalCausality
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The local future Cauchy horizon of the embedded original region. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

def sphericalOpenRectangle (va vb ua ub : ℝ) : Set SphericalSpacetime :=
  (Ioo va vb ×ˢ Ioo ua ub) ×ˢ univ

-- A radial null generator has a past limit on the excluded side u = ua.
theorem exists_past_radial_null_curve {va vb ua ub : ℝ}
    (H R : SphericalSpacetime → ℝ) {p : SphericalSpacetime}
    (hp : p ∈ sphericalOpenRectangle va vb ua ub) :
    ∃ γ : ℝ → SphericalSpacetime,
      IsPastInextendibleCausalCurve (sphericalOpenRectangle va vb ua ub) H R γ ∧
      γ 0 = p ∧ ∀ t, (γ t).1.1 = p.1.1 := by
  let d := p.1.2 - ua
  have hd : 0 < d := sub_pos.2 hp.1.2.1
  let γ : ℝ → SphericalSpacetime := fun t => ((p.1.1, ua + d * Real.exp t), p.2)
  have hc : Continuous γ := by dsimp [γ]; fun_prop
  have hC : ContDiff ℝ 1 (spacetimeInclusion ∘ γ) := by
    dsimp [spacetimeInclusion, γ, Function.comp_def]
    fun_prop
  have hmaps : MapsTo γ (Iic 0) (sphericalOpenRectangle va vb ua ub) := by
    intro t ht
    have hupper : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr ht
    change ((p.1.1, ua + d * Real.exp t), p.2) ∈
      (Ioo va vb ×ˢ Ioo ua ub) ×ˢ univ
    refine ⟨⟨hp.1.1, ?_⟩, mem_univ _⟩
    constructor
    · nlinarith [mul_pos hd (Real.exp_pos t)]
    · have hh := mul_le_mul_of_nonneg_left hupper hd.le
      dsimp [d] at hh
      linarith [hp.1.2.2]
  have hlim : Tendsto γ atBot (𝓝 ((p.1.1, ua), p.2)) := by
    have he : Tendsto (fun t => ua + d * Real.exp t) atBot (𝓝 ua) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.mul Real.tendsto_exp_atBot)
    simpa only [nhds_prod_eq] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => p.1.1) atBot (𝓝 p.1.1)).prodMk
        he).prodMk (tendsto_const_nhds : Tendsto (fun _ : ℝ => p.2) atBot (𝓝 p.2))
  refine ⟨γ, ⟨hc.continuousOn, hmaps, hC.locallyLipschitz.locallyLipschitzOn, ?_, ?_⟩,
    ?_, fun _ => rfl⟩
  · apply Eventually.of_forall
    intro t
    refine ⟨((0, d * Real.exp t), 0), ?_, ?_⟩
    · exact ((hasDerivAt_const t p.1.1).prodMk
        (((Real.hasDerivAt_exp t).const_mul d).const_add ua)).prodMk
          (hasDerivAt_const t (p.2 : SphereAmbient))
    · constructor
      · change 0 ≤ 0 + d * Real.exp t
        positivity
      · simp [sphericalVelocitySquare]
  · intro q hq hqend
    have he := tendsto_nhds_unique hlim hqend
    have hu := congrArg (fun z : SphericalSpacetime => z.1.2) he
    exact (ne_of_lt hq.1.2.1) hu
  · dsimp [γ, d]
    simp

theorem sphericalRectangle_future_domain {va vb ua ub : ℝ}
    (H R : SphericalSpacetime → ℝ) :
    futureDomainOfDependence (sphericalOpenRectangle va vb ua ub) H R
        (sphericalOpenRectangle va (min vb 0) ua ub) =
      sphericalOpenRectangle va (min vb 0) ua ub := by
  ext p
  constructor
  · rintro ⟨hp, hD⟩
    obtain ⟨γ, hγ, hstart, hV⟩ := exists_past_radial_null_curve H R hp
    obtain ⟨t, _ht, hS⟩ := hD γ hγ hstart
    exact ⟨⟨⟨hp.1.1.1, by simpa only [hV] using hS.1.1.2⟩, hp.1.2⟩, hp.2⟩
  · intro hp
    refine ⟨⟨⟨⟨hp.1.1.1, hp.1.1.2.trans_le (min_le_left _ _)⟩, hp.1.2⟩, hp.2⟩, ?_⟩
    intro γ _hγ hstart
    exact ⟨0, le_rfl, hstart.symm ▸ hp⟩

theorem sphericalRectangle_chronological_past {va vb ua ub : ℝ}
    {H R : SphericalSpacetime → ℝ} (hb : 0 < vb)
    (hH : ∀ p ∈ sphericalOpenRectangle va vb ua ub, 0 < H p)
    (hR : ∀ p ∈ sphericalOpenRectangle va vb ua ub, 0 ≤ R p) :
    chronologicalPast (sphericalOpenRectangle va vb ua ub) H R
        (sphericalOpenRectangle va 0 ua ub) =
      sphericalOpenRectangle va 0 ua ub := by
  ext p
  constructor
  · rintro ⟨hp, q, hq, hpq⟩
    exact ⟨⟨⟨hp.1.1.1, (hpq.regular_time_lt hH hR).trans hq.1.1.2⟩, hp.1.2⟩, hp.2⟩
  · intro hp
    let d := min (-p.1.1) (ub - p.1.2) / 2
    have hd : 0 < d := by
      exact half_pos (lt_min (neg_pos.2 hp.1.1.2) (sub_pos.2 hp.1.2.2))
    have hdV : p.1.1 + d < 0 := by
      have hh := min_le_left (-p.1.1) (ub - p.1.2)
      dsimp [d]
      linarith [hp.1.1.2]
    have hdu : p.1.2 + d < ub := by
      have hh := min_le_right (-p.1.1) (ub - p.1.2)
      dsimp [d]
      linarith [hp.1.2.2]
    let γ : ℝ → SphericalSpacetime := fun t => ((p.1.1 + t * d, p.1.2 + t * d), p.2)
    have hS : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ sphericalOpenRectangle va 0 ua ub := by
      intro t ht
      have ht0 := mul_nonneg ht.1 hd.le
      have ht1 : t * d ≤ d := by nlinarith [ht.2]
      exact ⟨⟨⟨by dsimp [γ]; linarith [hp.1.1.1],
        by dsimp [γ]; linarith⟩,
        ⟨by dsimp [γ]; linarith [hp.1.2.1], by dsimp [γ]; linarith⟩⟩, mem_univ _⟩
    have hm : MapsTo γ (Icc 0 1) (sphericalOpenRectangle va vb ua ub) := by
      intro t ht
      exact ⟨⟨⟨(hS t ht).1.1.1, (hS t ht).1.1.2.trans hb⟩, (hS t ht).1.2⟩, mem_univ _⟩
    refine ⟨⟨⟨⟨hp.1.1.1, hp.1.1.2.trans hb⟩, hp.1.2⟩, hp.2⟩,
      γ 1, hS 1 (by simp), Relation.TransGen.single ?_⟩
    refine ⟨γ, by simp [γ], rfl, ?_, hm, ?_, ?_⟩
    · exact (show Continuous γ by dsimp [γ]; fun_prop).continuousOn
    · apply ContDiff.contDiffOn
      dsimp [Function.comp_def, spacetimeInclusion, γ]
      fun_prop
    · intro t ht
      refine ⟨((d, d), 0), ?_, ?_⟩
      · have hdVt : HasDerivAt (fun x : ℝ => p.1.1 + x * d) d t := by
          simpa using ((hasDerivAt_id t).mul_const d).const_add p.1.1
        have hdut : HasDerivAt (fun x : ℝ => p.1.2 + x * d) d t := by
          simpa using ((hasDerivAt_id t).mul_const d).const_add p.1.2
        exact (hdVt.prodMk hdut).prodMk (hasDerivAt_const t (p.2 : SphereAmbient))
      · refine ⟨by dsimp; linarith, ?_⟩
        have hh := hH (γ t) (hm (Ioo_subset_Icc_self ht))
        simp only [sphericalVelocitySquare, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
          mul_zero, add_zero]
        exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hh) hd) hd

theorem sphericalRectangle_cauchy_horizon {va vb ua ub : ℝ}
    {H R : SphericalSpacetime → ℝ} (ha : va < 0) (hb : 0 < vb) (hu : ua < ub)
    (hH : ∀ p ∈ sphericalOpenRectangle va vb ua ub, 0 < H p)
    (hR : ∀ p ∈ sphericalOpenRectangle va vb ua ub, 0 ≤ R p) :
    futureDomainOfDependence (sphericalOpenRectangle va vb ua ub) H R
        (sphericalOpenRectangle va 0 ua ub) = sphericalOpenRectangle va 0 ua ub ∧
    futureCauchyHorizon (sphericalOpenRectangle va vb ua ub) H R
        (sphericalOpenRectangle va 0 ua ub) =
      ({0} ×ˢ Ioo ua ub) ×ˢ univ := by
  have hD := sphericalRectangle_future_domain (va := va) (vb := vb) (ua := ua) (ub := ub) H R
  rw [min_eq_right hb.le] at hD
  refine ⟨hD, ?_⟩
  unfold futureCauchyHorizon
  rw [hD, sphericalRectangle_chronological_past hb hH hR]
  unfold sphericalOpenRectangle
  rw [closure_prod_eq, closure_prod_eq, closure_Ioo ha.ne, closure_Ioo hu.ne, closure_univ]
  ext p
  constructor
  · rintro ⟨⟨hp, hc⟩, hn⟩
    have hz : p.1.1 = 0 := by
      by_contra hne
      exact hn ⟨⟨⟨hp.1.1.1, lt_of_le_of_ne hc.1.1.2 hne⟩, hp.1.2⟩, hp.2⟩
    exact ⟨⟨hz, hp.1.2⟩, hp.2⟩
  · rintro ⟨⟨hz, hp⟩, hs⟩
    have he : p.1.1 = 0 := hz
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, hp⟩, hs⟩, ⟨⟨⟨?_, ?_⟩, ?_⟩, hs⟩⟩, ?_⟩
    · simpa only [he] using ha
    · simpa only [he] using hb
    · simpa only [he] using ha.le
    · simp only [he, le_refl]
    · exact ⟨hp.1.le, hp.2.le⟩
    · intro hbad
      exact (ne_of_lt hbad.1.1.2) he

end CauchyHorizon
