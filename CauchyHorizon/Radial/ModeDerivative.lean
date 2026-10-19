import CauchyHorizon.Radial.Mode

/-! Derivatives of the reference weight and mode in the physical radius. -/

open Set Filter

namespace CauchyHorizon.Background

theorem criticalWeight_hasDerivAt (B : Background) {r : ℝ} (hr : r ∈ Ioo B.inner B.event) :
    HasDerivAt B.criticalWeight (B.innerRate / B.F r * B.criticalWeight r) r := by
  have hz := B.z_pos hr
  have hd := (B.z_hasDerivAt hr).rpow_const (p := B.criticalExponent) (Or.inl hz.ne')
  have heq : B.criticalWeight =ᶠ[nhds r] (fun t => B.z t ^ B.criticalExponent) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
    exact B.criticalWeight_eq_z_rpow ht
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  rw [Real.rpow_sub_one hz.ne', B.criticalWeight_eq_z_rpow hr]
  dsimp [criticalExponent]
  field_simp [B.outerRate_pos.ne']

theorem radialMode_radius_hasDerivAt (B : Background) (hb : B.criticalExponent < 1)
    {r : ℝ} (hr : r ∈ Ioo B.inner B.event) :
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).1 (B.event - y)
    let V := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).2 (B.event - y)
    HasDerivAt X (-(B.outerRate * B.criticalWeight r / r * V r)) r ∧
      HasDerivAt V (-(X r / (B.outerRate * r * B.criticalWeight r))) r := by
  have hx : B.event - r ∈ Ioo 0 B.radialLength := by
    dsimp [radialLength]
    constructor <;> linarith [hr.1, hr.2]
  have hm := B.radialMode_hasDerivAt hb hx
  constructor
  · simpa only [Function.comp_def, coefficientX, sub_sub_cancel, one_mul, mul_neg,
      mul_one] using hm.1.comp r ((hasDerivAt_id r).const_sub B.event)
  · simpa only [Function.comp_def, coefficientV, sub_sub_cancel, one_mul, mul_neg,
      mul_one, div_eq_mul_inv, mul_comm, neg_one_mul] using hm.2.comp r ((hasDerivAt_id r).const_sub B.event)

end CauchyHorizon.Background
