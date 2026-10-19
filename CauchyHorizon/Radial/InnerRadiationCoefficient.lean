import CauchyHorizon.Radial.ModeInner
import CauchyHorizon.Radial.Restoring

/-! The actual transverse source coefficient gains one power in squared energy. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon.Background

theorem exists_inner_radiation_coefficient_bound (B : Background) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y ∈ Ioc B.inner ((B.inner + B.event) / 2),
      ((Y - B.inner) ^ 2 * B.criticalWeight Y / (-B.F Y)) ^ 2 ≤ C * (Y - B.inner) := by
  obtain ⟨d, d₀, hd₀, _hdc, _hdroot, hd⟩ := B.exists_inner_restoring_factor
  obtain ⟨Q, hQ, hweight⟩ := B.exists_inner_weight_bound
  refine ⟨(Q / d₀) ^ 2, sq_nonneg _, ?_⟩
  intro Y hY
  have hband : Y ∈ Ioo B.inner B.event := ⟨hY.1, by linarith only [hY.2, B.inner_lt_event]⟩
  have hδ : 0 < Y - B.inner := sub_pos.2 hY.1
  have hdy := hd Y ⟨by linarith only [hY.1, B.inner_pos], hY.2⟩
  have hdp : 0 < d Y := hd₀.trans_le hdy.1
  have hq : 0 ≤ B.criticalWeight Y := (B.criticalWeight_pos hband).le
  have hp : 0 ≤ (Y - B.inner) ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hδ.le _
  have hsplit : (Y - B.inner) * (Y - B.inner) ^ (-1 / 2 : ℝ) =
      (Y - B.inner) ^ (1 / 2 : ℝ) := by
    calc
      _ = (Y - B.inner) ^ (1 + (-1 / 2 : ℝ)) := by rw [Real.rpow_add hδ, Real.rpow_one]
      _ = _ := by norm_num
  have hbound : (Y - B.inner) ^ 2 * B.criticalWeight Y / (-B.F Y) ≤
      Q / d₀ * (Y - B.inner) ^ (1 / 2 : ℝ) := calc
    _ = (Y - B.inner) * B.criticalWeight Y / d Y := by
      rw [hdy.2]
      field_simp [hδ.ne', hdp.ne']
    _ ≤ (Y - B.inner) * (Q * (Y - B.inner) ^ (-1 / 2 : ℝ)) / d₀ :=
      div_le_div₀ (mul_nonneg hδ.le (mul_nonneg hQ hp))
        (mul_le_mul_of_nonneg_left (hweight Y ⟨hY.1.le, hband.2.le⟩).1 hδ.le) hd₀ hdy.1
    _ = Q / d₀ * (Y - B.inner) ^ (1 / 2 : ℝ) := by rw [← hsplit]; ring
  calc
    _ ≤ (Q / d₀ * (Y - B.inner) ^ (1 / 2 : ℝ)) ^ 2 :=
      (sq_le_sq₀ (div_nonneg (mul_nonneg (sq_nonneg _) hq) (neg_pos.2 (B.F_neg hband)).le)
        (mul_nonneg (div_nonneg hQ hd₀.le) (Real.rpow_nonneg hδ.le _))).2 hbound
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast ((Y - B.inner) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hδ.le]
      norm_num

noncomputable def innerTransmissionError (B : Background) (hm : B.criticalExponent < 1)
    (L Ch Eprofile Etotal Y : ℝ) : ℝ :=
  let C := Real.exp (2 + 1 / 16) * (L * (Y - B.inner)) ^ 2
  let K := B.criticalWeight Y / (Real.exp (-1) * (-B.F Y) / B.outerRate)
  let cθ := extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - Y) * Ch
  let cζ := extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - Y) * Ch
  6 * (C / ((B.inner / 2) * B.innerRate)) ^ 2 * K ^ 2 * (cζ ^ 2 * Eprofile) +
    2 * (C * (2 * Real.exp 2) / (4 * B.innerRate ^ 2 * (B.inner / 2) ^ 2)) ^ 2 * Etotal +
    (cθ - B.transmission hm * Ch) ^ 2 * Eprofile

theorem inner_transmission_error_tendsto (B : Background) (hm : B.criticalExponent < 1)
    (L Ch Eprofile Etotal : ℝ) :
    Tendsto (B.innerTransmissionError hm L Ch Eprofile Etotal) (𝓝[>] B.inner) (𝓝 0) := by
  obtain ⟨Q, _hQ, hQbound⟩ := B.exists_inner_radiation_coefficient_bound
  have hsq : Tendsto (fun Y => ((Y - B.inner) ^ 2 * B.criticalWeight Y / (-B.F Y)) ^ 2)
      (𝓝[>] B.inner) (𝓝 0) := by
    have hlim : Tendsto (fun Y => Q * (Y - B.inner)) (𝓝[>] B.inner) (𝓝 0) := by
      have hc : Continuous (fun Y => Q * (Y - B.inner)) := by fun_prop
      simpa only [sub_self, mul_zero] using (hc.continuousAt (x := B.inner)).tendsto.mono_left
        (show 𝓝[>] B.inner ≤ 𝓝 B.inner from nhdsWithin_le_nhds)
    apply squeeze_zero' (Eventually.of_forall (fun Y => sq_nonneg _)) _ hlim
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (show B.inner < (B.inner + B.event) / 2 by linarith only [B.inner_lt_event]))]
      with Y hY hcap
    exact hQbound Y ⟨hY, hcap.le⟩
  let C := fun Y => Real.exp (2 + 1 / 16) * (L * (Y - B.inner)) ^ 2
  let cθ := fun Y => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - Y) * Ch
  let cζ := fun Y => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - Y) * Ch
  have hC : Continuous C := by fun_prop
  have hθ : Continuous cθ :=
    ((continuous_extendCurve _ _).comp (continuous_const.sub continuous_id)).mul continuous_const
  have hζ : Continuous cζ :=
    ((continuous_extendCurve _ _).comp (continuous_const.sub continuous_id)).mul continuous_const
  have hθend : cθ B.inner = B.transmission hm * Ch := by
    change (B.radialMode hm).1 (projIcc 0 B.radialLength B.radialLength_pos.le B.radialLength) * Ch = _
    simp only [projIcc_of_mem B.radialLength_pos.le
      (right_mem_Icc.2 B.radialLength_pos.le), transmission]
  let A := 6 * (Real.exp (2 + 1 / 16) * L ^ 2 / ((B.inner / 2) * B.innerRate)) ^ 2 *
    (B.outerRate / Real.exp (-1)) ^ 2
  have hfilter : 𝓝[>] B.inner ≤ 𝓝 B.inner := nhdsWithin_le_nhds
  have hs := (((tendsto_const_nhds (x := A)).mul hsq).mul
    ((hζ.continuousAt (x := B.inner)).tendsto.mono_left nhdsWithin_le_nhds |>.pow 2)).mul_const Eprofile
  have hf := ((hC.continuousAt (x := B.inner)).tendsto.mono_left hfilter |>.mul_const
    (2 * Real.exp 2) |>.div_const (4 * B.innerRate ^ 2 * (B.inner / 2) ^ 2) |>.pow 2).const_mul 2
      |>.mul_const Etotal
  have ht := (((hθ.continuousAt (x := B.inner)).tendsto.mono_left hfilter).sub_const
    (B.transmission hm * Ch) |>.pow 2).mul_const Eprofile
  have hh := (hs.add hf).add ht
  change Tendsto (fun Y => A * _ * cζ Y ^ 2 * Eprofile + _ + _) _ _ at hh
  simp only [C, sub_self, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
    zero_div, hθend, add_zero] at hh
  convert hh using 1
  ext Y
  dsimp only [innerTransmissionError, A, cθ, cζ, C]
  simp only [mul_pow, div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
  ring

end CauchyHorizon.Background
