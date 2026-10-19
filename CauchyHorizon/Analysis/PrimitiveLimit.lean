import CauchyHorizon.Analysis.PrimitiveCompatibility

/-! Uniform limits of a field and its continuous derivative preserve the endpoint primitive. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

theorem continuous_derivative_limit {E α : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    {l : Filter α} [NeBot l] {f d : α → C(Icc a b, E)} {fh dh : C(Icc a b, E)}
    (hf : Tendsto f l (𝓝 fh)) (hd : Tendsto d l (𝓝 dh))
    (hder : ∀ᶠ n in l, ∀ u : Icc a b,
      HasDerivWithinAt (intervalExtension hab (f n)) (d n u) (Icc a b) u) :
    fh = ContinuousMap.const _ (fh ⟨a, le_rfl, hab⟩) + continuousPrimitiveL hab dh ∧
    ∀ u : Icc a b, HasDerivWithinAt (intervalExtension hab fh) (dh u) (Icc a b) u := by
  let A : C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
    (ContinuousLinearMap.const ℝ (Icc a b)).comp (ContinuousMap.evalCLM ℝ ⟨a, le_rfl, hab⟩)
  have he : f =ᶠ[l] fun n => A (f n) + continuousPrimitiveL hab (d n) := by
    filter_upwards [hder] with n hn
    ext u
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le u.property.1
      (intervalExtension hab (f n)).continuous.continuousOn (fun x hx => by
        have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.le.trans u.property.2⟩
        have hh := (hn ⟨x, hx'⟩).hasDerivAt (Icc_mem_nhds hx.1 (hx.2.trans_le u.property.2))
        simpa only [intervalExtension_apply, projIcc_of_mem hab hx'] using hh)
      ((intervalExtension hab (d n)).continuous.intervalIntegrable a u)
    simp only [intervalExtension_apply, projIcc_of_mem hab u.property,
      projIcc_of_mem hab (show a ∈ Icc a b from ⟨le_rfl, hab⟩)] at hi
    change f n u = f n ⟨a, le_rfl, hab⟩ + ∫ x in a..(u : ℝ), intervalExtension hab (d n) x
    change (∫ x in a..(u : ℝ), intervalExtension hab (d n) x) =
      f n u - f n ⟨a, le_rfl, hab⟩ at hi
    rw [hi]
    abel
  have hh : fh = A fh + continuousPrimitiveL hab dh :=
    tendsto_nhds_unique hf (((A.continuous.tendsto fh).comp hf).add
      (((continuousPrimitiveL hab).continuous.tendsto dh).comp hd) |>.congr' he.symm)
  refine ⟨hh, fun u => ?_⟩
  rw [hh, map_add]
  exact (continuousPrimitive_hasDerivWithinAt hab dh u.property).const_add _

end CauchyHorizon
