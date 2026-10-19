import CauchyHorizon.Geometry.SphericalMetric
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Causal curves and chronological precedence for the actual spherical metric. -/

open Set Filter MeasureTheory
open scoped Manifold Topology

namespace CauchyHorizon

abbrev SphericalSpacetime := (ℝ × ℝ) × UnitSphere
abbrev SpacetimeAmbient := (ℝ × ℝ) × SphereAmbient

def spacetimeInclusion (p : SphericalSpacetime) : SpacetimeAmbient := (p.1, p.2)

noncomputable def sphericalVelocitySquare (H R : ℝ) (z : SpacetimeAmbient) : ℝ :=
  -H * z.1.1 * z.1.2 + R * ‖z.2‖ ^ 2

theorem sphericalVelocitySquare_eq_metric (H R : ℝ) (p : UnitSphere)
    (z : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphericalVelocitySquare H R
        (z.1, mvfderiv (𝓡 2) (fun q : UnitSphere => (q : SphereAmbient)) p z.2) =
      sphereSpacetimeMetric H R p z z := by
  simp only [sphericalVelocitySquare, sphereSpacetimeMetric, unitSphereMetric,
    real_inner_self_eq_norm_sq]
  ring

def IsFutureCausalVelocity (H R : ℝ) (z : SpacetimeAmbient) : Prop :=
  0 ≤ z.1.1 + z.1.2 ∧ sphericalVelocitySquare H R z ≤ 0

def IsFutureTimelikeVelocity (H R : ℝ) (z : SpacetimeAmbient) : Prop :=
  0 < z.1.1 + z.1.2 ∧ sphericalVelocitySquare H R z < 0

theorem IsFutureTimelikeVelocity.null_components_pos {H R : ℝ} {z : SpacetimeAmbient}
    (h : IsFutureTimelikeVelocity H R z) (hH : 0 < H) (hR : 0 ≤ R) :
    0 < z.1.1 ∧ 0 < z.1.2 := by
  have hp : 0 < z.1.1 * z.1.2 := by
    have hn := mul_nonneg hR (sq_nonneg ‖z.2‖)
    have hq := h.2
    dsimp [sphericalVelocitySquare] at hq
    nlinarith
  obtain hpos | hneg := (mul_pos_iff.mp hp)
  · exact hpos
  · have hs := h.1
    linarith [hneg.1, hneg.2]

-- The parameter increases towards the future and ends at zero.
-- Absence of a past endpoint is independent of an unbounded parametrization.
def IsPastInextendibleCausalCurve (M : Set SphericalSpacetime)
    (H R : SphericalSpacetime → ℝ) (γ : ℝ → SphericalSpacetime) : Prop :=
  ContinuousOn γ (Iic 0) ∧ MapsTo γ (Iic 0) M ∧
    LocallyLipschitzOn (Iic 0) (spacetimeInclusion ∘ γ) ∧
    (∀ᵐ t ∂volume.restrict (Iio (0 : ℝ)), ∃ z : SpacetimeAmbient,
      HasDerivAt (spacetimeInclusion ∘ γ) z t ∧
        IsFutureCausalVelocity (H (γ t)) (R (γ t)) z) ∧
    ∀ q ∈ M, ¬Tendsto γ atBot (𝓝 q)

def futureDomainOfDependence (M : Set SphericalSpacetime)
    (H R : SphericalSpacetime → ℝ) (S : Set SphericalSpacetime) : Set SphericalSpacetime :=
  {p | p ∈ M ∧ ∀ γ : ℝ → SphericalSpacetime,
    IsPastInextendibleCausalCurve M H R γ → γ 0 = p → ∃ t ≤ 0, γ t ∈ S}

-- Finite concatenations allow the usual piecewise C1 timelike curves.
def TimelikeSegment (M : Set SphericalSpacetime) (H R : SphericalSpacetime → ℝ)
    (p q : SphericalSpacetime) : Prop :=
  ∃ γ : ℝ → SphericalSpacetime, γ 0 = p ∧ γ 1 = q ∧
    ContinuousOn γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) M ∧
    ContDiffOn ℝ 1 (spacetimeInclusion ∘ γ) (Icc 0 1) ∧
    ∀ t ∈ Ioo 0 1, ∃ z : SpacetimeAmbient,
      HasDerivAt (spacetimeInclusion ∘ γ) z t ∧
        IsFutureTimelikeVelocity (H (γ t)) (R (γ t)) z

def ChronologicalPrecedes (M : Set SphericalSpacetime) (H R : SphericalSpacetime → ℝ) :
    SphericalSpacetime → SphericalSpacetime → Prop :=
  Relation.TransGen (TimelikeSegment M H R)

def chronologicalPast (M : Set SphericalSpacetime) (H R : SphericalSpacetime → ℝ)
    (S : Set SphericalSpacetime) : Set SphericalSpacetime :=
  {p | p ∈ M ∧ ∃ q ∈ S, ChronologicalPrecedes M H R p q}

def futureCauchyHorizon (M : Set SphericalSpacetime) (H R : SphericalSpacetime → ℝ)
    (S : Set SphericalSpacetime) : Set SphericalSpacetime :=
  (M ∩ closure (futureDomainOfDependence M H R S)) \
    chronologicalPast M H R (futureDomainOfDependence M H R S)

theorem TimelikeSegment.regular_time_lt {M : Set SphericalSpacetime}
    {H R : SphericalSpacetime → ℝ} {p q : SphericalSpacetime}
    (h : TimelikeSegment M H R p q)
    (hH : ∀ w ∈ M, 0 < H w) (hR : ∀ w ∈ M, 0 ≤ R w) :
    p.1.1 < q.1.1 := by
  obtain ⟨γ, hp, hq, hc, hm, _hC, hd⟩ := h
  have hmono : StrictMonoOn (fun t => (γ t).1.1) (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc.fst.fst
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨z, hz, hv⟩ := hd t ht
    have hz₁ : HasDerivAt (fun t => (γ t).1.1) z.1.1 t := hz.fst.fst
    rw [hz₁.deriv]
    exact (hv.null_components_pos (hH _ (hm (Ioo_subset_Icc_self ht)))
      (hR _ (hm (Ioo_subset_Icc_self ht)))).1
  simpa only [hp, hq] using hmono (by simp) (by simp) (by norm_num : (0 : ℝ) < 1)

theorem ChronologicalPrecedes.regular_time_lt {M : Set SphericalSpacetime}
    {H R : SphericalSpacetime → ℝ} {p q : SphericalSpacetime}
    (h : ChronologicalPrecedes M H R p q)
    (hH : ∀ w ∈ M, 0 < H w) (hR : ∀ w ∈ M, 0 ≤ R w) :
    p.1.1 < q.1.1 := by
  induction h with
  | single h => exact h.regular_time_lt hH hR
  | tail _ h ih => exact ih.trans (h.regular_time_lt hH hR)

end CauchyHorizon
