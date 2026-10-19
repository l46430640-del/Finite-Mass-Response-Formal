import CauchyHorizon.Radial.CriticalWeight
import CauchyHorizon.Analysis.VolterraSystem

/-! The actual RN-dS radial system and its finite positive transmission amplitude. -/

open Set MeasureTheory

namespace CauchyHorizon.Background

variable (B : CauchyHorizon.Background)

noncomputable def radialLength : ℝ := B.event - B.inner

theorem radialLength_pos : 0 < B.radialLength := sub_pos.2 B.inner_lt_event

noncomputable def coefficientX (x : ℝ) : ℝ :=
  B.outerRate * B.criticalWeight (B.event - x) / (B.event - x)

noncomputable def coefficientV (x : ℝ) : ℝ :=
  1 / (B.outerRate * (B.event - x) * B.criticalWeight (B.event - x))

theorem inward_mem {x : ℝ} (hx : x ∈ Icc 0 B.radialLength) :
    B.event - x ∈ Icc B.inner B.event := by
  dsimp [radialLength] at hx
  constructor <;> linarith [hx.1, hx.2]

theorem inward_mem_interior {x : ℝ} (hx : x ∈ Ioo 0 B.radialLength) :
    B.event - x ∈ Ioo B.inner B.event := by
  dsimp [radialLength] at hx
  constructor <;> linarith [hx.1, hx.2]

theorem coefficients_integrable (hb : B.criticalExponent < 1) :
    IntervalIntegrable B.coefficientX volume 0 B.radialLength ∧
    IntervalIntegrable B.coefficientV volume 0 B.radialLength := by
  have hr0 (r : ℝ) (hr : r ∈ uIcc B.inner B.event) : r ≠ 0 := by
    rw [uIcc_of_le B.inner_lt_event.le] at hr
    exact (B.inner_pos.trans_le hr.1).ne'
  have hc : ContinuousOn (fun r => B.outerRate / r) (uIcc B.inner B.event) :=
    continuousOn_const.div continuousOn_id hr0
  have hd : ContinuousOn (fun r => (B.outerRate * r)⁻¹) (uIcc B.inner B.event) :=
    (continuousOn_const.mul continuousOn_id).inv₀ (fun r hr => mul_ne_zero B.outerRate_pos.ne' (hr0 r hr))
  have hi := (B.criticalWeight_integrable.mul_continuousOn hc).comp_sub_left B.event
  have hj := ((B.criticalWeight_inv_integrable hb).mul_continuousOn hd).comp_sub_left B.event
  constructor
  · change IntervalIntegrable (fun x => B.outerRate * B.criticalWeight (B.event - x) /
      (B.event - x)) volume 0 B.radialLength
    simpa only [sub_self, radialLength, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hi.symm
  · change IntervalIntegrable (fun x => 1 / (B.outerRate * (B.event - x) *
      B.criticalWeight (B.event - x))) volume 0 B.radialLength
    simpa only [sub_self, radialLength, one_div, mul_inv_rev] using hj.symm

theorem coefficients_continuousOn :
    ContinuousOn B.coefficientX (Ioo 0 B.radialLength) ∧
    ContinuousOn B.coefficientV (Ioo 0 B.radialLength) := by
  have hq := B.criticalWeight_continuousOn.comp (continuousOn_const.sub continuousOn_id)
    (fun x hx => B.inward_mem_interior hx)
  have hr0 (x : ℝ) (hx : x ∈ Ioo 0 B.radialLength) : B.event - x ≠ 0 :=
    (B.inner_pos.trans (B.inward_mem_interior hx).1).ne'
  constructor
  · exact (continuousOn_const.mul hq).div (continuousOn_const.sub continuousOn_id) hr0
  · exact continuousOn_const.div
      ((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).mul hq)
      (fun x hx => mul_ne_zero (mul_ne_zero B.outerRate_pos.ne' (hr0 x hx))
        (B.criticalWeight_pos (B.inward_mem_interior hx)).ne')

theorem coefficients_nonneg {x : ℝ} (hx : x ∈ Icc 0 B.radialLength) :
    0 ≤ B.coefficientX x ∧ 0 ≤ B.coefficientV x := by
  have hr := B.inward_mem hx
  have hq := B.criticalWeight_nonneg hr
  have hr0 := B.inner_pos.trans_le hr.1
  exact ⟨div_nonneg (mul_nonneg B.outerRate_pos.le hq) hr0.le,
    div_nonneg zero_le_one (mul_nonneg (mul_nonneg B.outerRate_pos.le hr0.le) hq)⟩

theorem coefficients_pos {x : ℝ} (hx : x ∈ Ioo 0 B.radialLength) :
    0 < B.coefficientX x ∧ 0 < B.coefficientV x := by
  have hr := B.inward_mem_interior hx
  have hq := B.criticalWeight_pos hr
  have hr0 := B.inner_pos.trans hr.1
  exact ⟨div_pos (mul_pos B.outerRate_pos hq) hr0,
    div_pos zero_lt_one (mul_pos (mul_pos B.outerRate_pos hr0) hq)⟩

theorem exists_unique_radialMode (hb : B.criticalExponent < 1) :
    ∃! p, IsVolterraPair B.radialLength_pos.le B.coefficientX B.coefficientV
      0 (B.event * B.criticalExponent) p := by
  have hi := B.coefficients_integrable hb
  have hc := B.coefficients_continuousOn
  exact exists_unique_volterraPair B.radialLength_pos.le hi.1 hi.2 hc.1 hc.2 _ _

noncomputable def radialMode (hb : B.criticalExponent < 1) :
    C(Icc 0 B.radialLength, ℝ) × C(Icc 0 B.radialLength, ℝ) :=
  Classical.choose (B.exists_unique_radialMode hb)

theorem radialMode_spec (hb : B.criticalExponent < 1) :
    IsVolterraPair B.radialLength_pos.le B.coefficientX B.coefficientV
      0 (B.event * B.criticalExponent) (B.radialMode hb) :=
  (Classical.choose_spec (B.exists_unique_radialMode hb)).1

theorem radialMode_unique (hb : B.criticalExponent < 1)
    {p : C(Icc 0 B.radialLength, ℝ) × C(Icc 0 B.radialLength, ℝ)}
    (hp : IsVolterraPair B.radialLength_pos.le B.coefficientX B.coefficientV
      0 (B.event * B.criticalExponent) p) : p = B.radialMode hb :=
  (Classical.choose_spec (B.exists_unique_radialMode hb)).2 p hp

theorem radialMode_initial (hb : B.criticalExponent < 1) :
    (B.radialMode hb).1 ⟨0, left_mem_Icc.2 B.radialLength_pos.le⟩ = 0 ∧
    (B.radialMode hb).2 ⟨0, left_mem_Icc.2 B.radialLength_pos.le⟩ = B.event * B.criticalExponent := by
  simpa using B.radialMode_spec hb ⟨0, left_mem_Icc.2 B.radialLength_pos.le⟩

theorem radialMode_hasDerivAt (hb : B.criticalExponent < 1) {x : ℝ}
    (hx : x ∈ Ioo 0 B.radialLength) :
    HasDerivAt (extendCurve B.radialLength_pos.le (B.radialMode hb).1)
      (B.coefficientX x * extendCurve B.radialLength_pos.le (B.radialMode hb).2 x) x ∧
    HasDerivAt (extendCurve B.radialLength_pos.le (B.radialMode hb).2)
      (B.coefficientV x * extendCurve B.radialLength_pos.le (B.radialMode hb).1 x) x := by
  have hi := B.coefficients_integrable hb
  have hc := B.coefficients_continuousOn
  exact volterraPair_hasDerivAt B.radialLength_pos.le hi.1 hi.2 hc.1 hc.2 (B.radialMode_spec hb) hx

theorem radialMode_positive (hb : B.criticalExponent < 1)
    (x : Icc 0 B.radialLength) (hx : 0 < (x : ℝ)) :
    0 < (B.radialMode hb).1 x ∧ 0 < (B.radialMode hb).2 x := by
  have hi := B.coefficients_integrable hb
  have hc := B.coefficients_continuousOn
  have hdata := mul_pos B.event_pos B.criticalExponent_pos
  have hp := B.radialMode_spec hb
  have hnonneg := volterraPair_nonneg B.radialLength_pos.le hi.1 hi.2 hc.1 hc.2
    le_rfl hdata.le (fun _ ht => (B.coefficients_nonneg ht).1)
    (fun _ ht => (B.coefficients_nonneg ht).2) hp
  exact volterraPair_strict_positive B.radialLength_pos.le hi.1 hdata
    (fun _ ht => (B.coefficients_nonneg ht).1) (fun _ ht => (B.coefficients_nonneg ht).2)
    (fun _ ht => (B.coefficients_pos ht).1) hp hnonneg x hx

noncomputable def transmission (hb : B.criticalExponent < 1) : ℝ :=
  (B.radialMode hb).1 ⟨B.radialLength, right_mem_Icc.2 B.radialLength_pos.le⟩

theorem transmission_pos (hb : B.criticalExponent < 1) : 0 < B.transmission hb :=
  (B.radialMode_positive hb _ B.radialLength_pos).1

end CauchyHorizon.Background
