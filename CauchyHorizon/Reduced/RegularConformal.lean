import CauchyHorizon.Reduced.RegularScalar

/-! Subtracting the anchor log lapse gives the conformal derivative with finite regular-time energy. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def waveAnchoredLog {K : Type*} [TopologicalSpace K] [CompactSpace K] (u₀ : K) :
    C(K, WaveVector) →L[ℝ] C(K, ℝ) :=
  ContinuousLinearMap.compLeftContinuous ℝ K (ContinuousLinearMap.proj (2 : Fin 3)) -
    (ContinuousLinearMap.const ℝ K).comp
      ((ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ u₀))

noncomputable def regularConformalVelocityRow {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ) (w : ℝ) : C(Icc ε U, ℝ) :=
  waveAnchoredLog ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)

def IsRegularConformalEnergy {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (k : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ) (T₀ C : ℝ) : Prop :=
  let a := anchoringLapse (hε.trans hεU) X
  let F := regularConformalVelocityRow hε hεU X χ
  (∀ w ∈ Ioo (regularTime a 0) 0,
    HasDerivAt (fun z => waveAnchoredLog ⟨U, hεU, le_rfl⟩ (renormalizedWaveRow hε 0 X (χ z))) (F w) w) ∧
  (∀ T, T₀ ≤ T → MemLp F 2 (volume.restrict (Ioo (regularTime a T) 0)) ∧
    (∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) ≤
      C * ∫ t in Ioi T, (‖compactRadiationRow hε k X t‖ ^ 2 + Real.exp (-(2 * k) * t))) ∧
  Tendsto (fun T => ∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) atTop (𝓝 0)

set_option maxHeartbeats 1000000 in
theorem regular_conformal_energy {U ε k A B T₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (hk : 0 < k) (hA : 0 < A) (hB : 0 ≤ B) (hT₀ : 0 ≤ T₀)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hderiv : ∀ (T : Ici (0 : ℝ)) (v : ℝ) (hv : v ∈ Icc 0 (T : ℝ)),
      HasDerivWithinAt (intervalExtension T.property (flipRectangle (X T).1))
        (flipRectangle (X T).2.1 ⟨v, hv⟩) (Icc 0 (T : ℝ)) v)
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hamp : ∀ t, T₀ ≤ t → A * Real.exp (-(2 * k) * t) ≤ anchoringLapse (hε.trans hεU) X t)
    (hbound : ∀ (t : ℝ) (ht : 0 ≤ t), T₀ ≤ t →
      ∀ u : Icc ε U,
        |(X ⟨t, ht⟩).2.1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, le_rfl⟩ 2 -
          (X ⟨t, ht⟩).2.1 ⟨U, hε.trans hεU, le_rfl⟩ ⟨t, ht, le_rfl⟩ 2| ≤
            B * (Real.exp (-k * t) * ‖compactRadiationRow hε k X t‖ + Real.exp (-(2 * k) * t)))
    (henergy : MemLp (radiationRow k X) 2 (volume.restrict (Ici 0))) :
    IsRegularConformalEnergy hε hεU k X χ T₀ (2 * B ^ 2 / A) := by
  let a := anchoringLapse (hε.trans hεU) X
  let F := regularConformalVelocityRow hε hεU X χ
  let C := 2 * B ^ 2 / A
  let P := waveAnchoredLog (⟨U, hεU, le_rfl⟩ : Icc ε U)
  obtain ⟨hfinite, hdiff, hcont⟩ := regular_wave_derivative hε hεU X hX hderiv hχ
  have hp := hχ.2.1
  have hFc : ContinuousOn F (Ioo (regularTime a 0) 0) := P.continuous.comp_continuousOn hcont
  have hw (t : ℝ) (ht : T₀ ≤ t) (htpos : 0 < t) :
      a t * ‖F (regularTime a t)‖ ^ 2 ≤ C * (‖compactRadiationRow hε k X t‖ ^ 2 + Real.exp (-(2 * k) * t)) := by
    let T : Ici (0 : ℝ) := ⟨t, htpos.le⟩
    let q := Real.exp (-k * t)
    let z := ‖compactRadiationRow hε k X t‖
    have hq : 0 < q := Real.exp_pos _
    have hz : 0 ≤ z := norm_nonneg _
    have ha : 0 < a t := hp t
    have he : Real.exp (-(2 * k) * t) = q ^ 2 := by
      rw [show -(2 * k) * t = -k * t + -k * t by ring, Real.exp_add]
      simp only [q, pow_two]
    have hnorm : ‖F (regularTime a t)‖ ≤ B * q * (z + q) / a t := by
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro u
      change ‖regularWaveVelocityRow hε hεU X χ (regularTime a t) u 2 -
        regularWaveVelocityRow hε hεU X χ (regularTime a t) ⟨U, hεU, le_rfl⟩ 2‖ ≤ _
      rw [hfinite T t htpos le_rfl u 2, hfinite T t htpos le_rfl ⟨U, hεU, le_rfl⟩ 2,
        ← sub_div, norm_div, Real.norm_of_nonneg (hp t).le]
      apply div_le_div_of_nonneg_right ?_ (hp t).le
      have hh := hbound t htpos.le ht u
      rw [he] at hh
      change |(X T).2.1 _ _ 2 - (X T).2.1 _ _ 2| ≤ _
      convert hh using 1
      dsimp only [q, z]
      ring
    have hqa : q ^ 2 / a t ≤ 1 / A := (div_le_div_iff₀ (hp t) hA).2 (by
      have hh := hamp t ht
      rw [he] at hh
      nlinarith only [hh])
    calc
      _ ≤ a t * (B * q * (z + q) / a t) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (hp t).le
      _ = (B ^ 2 * (z + q) ^ 2) * (q ^ 2 / a t) := by field_simp [ha.ne']
      _ ≤ (B ^ 2 * (z + q) ^ 2) * (1 / A) := mul_le_mul_of_nonneg_left hqa (by positivity)
      _ ≤ C * (z ^ 2 + q ^ 2) := by
        have hs : (z + q) ^ 2 ≤ 2 * (z ^ 2 + q ^ 2) := by nlinarith only [sq_nonneg (z - q)]
        have hh := mul_le_mul_of_nonneg_left hs (div_nonneg (sq_nonneg B) hA.le)
        calc
          _ = (B ^ 2 / A) * (z + q) ^ 2 := by ring
          _ ≤ (B ^ 2 / A) * (2 * (z ^ 2 + q ^ 2)) := hh
          _ = _ := by dsimp only [C]; ring
      _ = _ := by rw [he]
  have hi := (compactRadiationRestriction hε).comp_memLp' henergy
  have hiRad : IntegrableOn (fun t => ‖compactRadiationRow hε k X t‖ ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq_norm hi.1).1 hi
  have hiExp : IntegrableOn (fun t => Real.exp (-(2 * k) * t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_mul_Ioi (by linarith only [hk]) 0)
  have he := hχ.energy_of_majorant hT₀ hFc ((hiRad.add hiExp).const_mul C) hw
  refine ⟨(fun w hw => P.hasFDerivAt.comp_hasDerivAt w (hdiff w hw)), ?_, he.2⟩
  intro T hT
  simpa only [F, C, Pi.add_apply, integral_const_mul] using he.1 T hT

end CauchyHorizon
