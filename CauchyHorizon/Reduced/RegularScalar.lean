import CauchyHorizon.Reduced.RegularWave
import CauchyHorizon.Reduced.RadiationHalfline
import CauchyHorizon.Analysis.RegularTimeEnergy

/-! The actual scalar time derivative has finite mixed energy in the regular chart. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def compactRadiationRestriction {U ε : ℝ} (hε : 0 ≤ ε) :
    C(Icc 0 U, ℝ) →L[ℝ] C(Icc ε U, ℝ) :=
  ContinuousMap.compCLM ℝ ℝ
    ⟨fun u => ⟨u, hε.trans u.property.1, u.property.2⟩, by fun_prop⟩

noncomputable def compactRadiationRow {U ε : ℝ} (hε : 0 ≤ ε) (k : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (t : ℝ) : C(Icc ε U, ℝ) :=
  compactRadiationRestriction hε (radiationRow k X t)

noncomputable def waveScalar {K : Type*} [TopologicalSpace K] [CompactSpace K] :
    C(K, WaveVector) →L[ℝ] C(K, ℝ) :=
  ContinuousLinearMap.compLeftContinuous ℝ K (ContinuousLinearMap.proj (1 : Fin 3))

noncomputable def regularScalarVelocityRow {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ) (w : ℝ) : C(Icc ε U, ℝ) :=
  waveScalar (regularWaveVelocityRow hε hεU X χ w)

def IsRegularScalarEnergy {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (k : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ) (T₀ C : ℝ) : Prop :=
  let a := anchoringLapse (hε.trans hεU) X
  let F := regularScalarVelocityRow hε hεU X χ
  (∀ w ∈ Ioo (regularTime a 0) 0,
    HasDerivAt (fun z => waveScalar (renormalizedWaveRow hε 0 X (χ z))) (F w) w) ∧
  (∀ T, T₀ ≤ T → MemLp F 2 (volume.restrict (Ioo (regularTime a T) 0)) ∧
    (∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) ≤ C * ∫ t in Ioi T, ‖compactRadiationRow hε k X t‖ ^ 2) ∧
  Tendsto (fun T => ∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) atTop (𝓝 0)

set_option maxHeartbeats 1000000 in
theorem regular_scalar_energy {U ε k ρ A T₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (hρ : 0 < ρ) (hA : 0 < A) (hT₀ : 0 ≤ T₀)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hderiv : ∀ (T : Ici (0 : ℝ)) (v : ℝ) (hv : v ∈ Icc 0 (T : ℝ)),
      HasDerivWithinAt (intervalExtension T.property (flipRectangle (X T).1))
        (flipRectangle (X T).2.1 ⟨v, hv⟩) (Icc 0 (T : ℝ)) v)
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hr : ∀ (T : Ici (0 : ℝ)) u v, ρ ≤ (X T).1 u v 0)
    (hamp : ∀ t, T₀ ≤ t → A * Real.exp (-(2 * k) * t) ≤ anchoringLapse (hε.trans hεU) X t)
    (henergy : MemLp (radiationRow k X) 2 (volume.restrict (Ici 0))) :
    IsRegularScalarEnergy hε hεU k X χ T₀ (1 / (ρ ^ 2 * A)) := by
  let a := anchoringLapse (hε.trans hεU) X
  let F := regularScalarVelocityRow hε hεU X χ
  let C := 1 / (ρ ^ 2 * A)
  let J : Icc ε U → Icc 0 U := fun u => ⟨u, hε.trans u.property.1, u.property.2⟩
  obtain ⟨hfinite, hdiff, hcont⟩ := regular_wave_derivative hε hεU X hX hderiv hχ
  have hp := hχ.2.1
  have hFc : ContinuousOn F (Ioo (regularTime a 0) 0) := waveScalar.continuous.comp_continuousOn hcont
  have hbound (t : ℝ) (ht : T₀ ≤ t) (htpos : 0 < t) :
      a t * ‖F (regularTime a t)‖ ^ 2 ≤ C * ‖compactRadiationRow hε k X t‖ ^ 2 := by
    let T : Ici (0 : ℝ) := ⟨t, htpos.le⟩
    let v : Icc 0 (T : ℝ) := ⟨t, htpos.le, le_rfl⟩
    have hden : 0 < ρ * Real.exp (k * t) * a t := mul_pos (mul_pos hρ (Real.exp_pos _)) (hp t)
    have hnorm : ‖F (regularTime a t)‖ ≤ ‖compactRadiationRow hε k X t‖ / (ρ * Real.exp (k * t) * a t) := by
      apply (ContinuousMap.norm_le _ (div_nonneg (norm_nonneg _) hden.le)).2
      intro u
      have hrpos := hρ.trans_le (hr T (J u) v)
      have he : compactRadiationRow hε k X t u = Real.exp (k * t) * ((X T).1 (J u) v 0 * (X T).2.1 (J u) v 1) := by
        change radiationRow k X t (J u) = _
        rw [radiationRow_eq (t := t) X hX T le_rfl]
        simp only [spatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
          zero_mul, sub_zero]
        rw [projIcc_of_mem T.property (show t ∈ Icc 0 (T : ℝ) from ⟨htpos.le, le_rfl⟩)]
      have hf : F (regularTime a t) u = compactRadiationRow hε k X t u /
          (Real.exp (k * t) * (X T).1 (J u) v 0 * a t) := by
        change regularWaveVelocityRow hε hεU X χ (regularTime a t) u 1 = _
        rw [hfinite T t htpos le_rfl u 1, he]
        change (X T).2.1 (J u) v 1 / a t =
          (Real.exp (k * t) * ((X T).1 (J u) v 0 * (X T).2.1 (J u) v 1)) /
            (Real.exp (k * t) * (X T).1 (J u) v 0 * a t)
        have ha0 : a t ≠ 0 := (hp t).ne'
        field_simp [hrpos.ne', ha0]
      rw [hf, norm_div, Real.norm_of_nonneg (mul_pos (mul_pos (Real.exp_pos _) hrpos) (hp t)).le]
      apply div_le_div₀ (norm_nonneg _) ((compactRadiationRow hε k X t).norm_coe_le_norm u) hden
      calc
        _ = Real.exp (k * t) * ρ * a t := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hr T (J u) v) (Real.exp_pos _).le) (hp t).le
    have ha : A ≤ Real.exp (2 * k * t) * a t := by
      have hh := mul_le_mul_of_nonneg_left (hamp t ht) (Real.exp_pos (2 * k * t)).le
      have he : Real.exp (2 * k * t) * (A * Real.exp (-(2 * k) * t)) = A := by
        rw [neg_mul, Real.exp_neg]
        field_simp
      exact he ▸ hh
    calc
      _ ≤ a t * (‖compactRadiationRow hε k X t‖ / (ρ * Real.exp (k * t) * a t)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (hp t).le
      _ = ‖compactRadiationRow hε k X t‖ ^ 2 / (ρ ^ 2 * (Real.exp (2 * k * t) * a t)) := by
        rw [show 2 * k * t = k * t + k * t by ring, Real.exp_add]
        field_simp [hρ.ne', (hp t).ne']
      _ ≤ ‖compactRadiationRow hε k X t‖ ^ 2 / (ρ ^ 2 * A) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (sq_pos_of_pos hρ) hA)
          (mul_le_mul_of_nonneg_left ha (sq_nonneg ρ))
      _ = _ := by dsimp only [C]; ring
  have hi := (compactRadiationRestriction hε).comp_memLp' henergy
  have hiRad : IntegrableOn (fun t => ‖compactRadiationRow hε k X t‖ ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq_norm hi.1).1 hi
  have he := hχ.energy_of_majorant hT₀ hFc (hiRad.const_mul C) hbound
  refine ⟨(fun w hw => waveScalar.hasFDerivAt.comp_hasDerivAt w (hdiff w hw)), ?_, he.2⟩
  intro T hT
  simpa only [integral_const_mul] using he.1 T hT

end CauchyHorizon
