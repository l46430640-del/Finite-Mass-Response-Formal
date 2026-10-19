import CauchyHorizon.Reduced.OuterRadiation
import CauchyHorizon.Reduced.RadiationEnergy

/-! An exponential spatial weight makes radiation feedback small without a small band width. -/

open MeasureTheory Set

namespace CauchyHorizon

set_option maxHeartbeats 600000 in
theorem IsWaveIntegral.outer_radiation_spatial_kernel_on {U V e Λ a k ρ R N L σ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hσ : 0 < σ)
    (B : Icc 0 V → ℝ) (hB0 : ∀ v, 0 ≤ B v) (hB : Antitone B)
    (hlo : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v → ρ ≤ x.1 u v 0)
    (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v → |x.2.1 u v 0| ≤ L)
    (M : C(Icc 0 V, ℝ))
    (hM : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      Real.exp (k * v - σ * u * Real.exp (a * v)) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v) :
    (∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      Real.exp (k * v - σ * u * Real.exp (a * v)) *
          |scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 u v| ≤
        (N / ρ) * Real.exp (a * v) * causalExpIntegral hV (a - k) M v) ∧
      ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
        Real.exp (k * v - σ * u * Real.exp (a * v)) * |x.1 u v 0 * x.2.1 u v 1| ≤
          Real.exp (k * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
          (L * R / ρ) * Real.exp (k * v) * (∫ t in (0 : ℝ)..u, |uIn t 1|) +
          (L * N / (σ * ρ ^ 2)) * causalExpIntegral hV (a - k) M v := by
  let Γ : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
    (⟨fun q : Icc 0 U × Icc 0 V => Real.exp (σ * q.1 * Real.exp (a * q.2)),
      by fun_prop⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry
  have hΓ (u : Icc 0 U) : Monotone (Γ u) := by
    intro v w hvw
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hvw ha)) (mul_nonneg hσ.le u.property.1)
  have hM0 (v : Icc 0 V) : 0 ≤ M v :=
    (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)).trans (hM ⟨0, le_rfl, hU⟩ v (hB0 v))
  have hmajor (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ B v) :
      Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ Γ u v * M v := by
    have hh := mul_le_mul_of_nonneg_left (hM u v hu) (Real.exp_pos (σ * u * Real.exp (a * v))).le
    have he : Real.exp (σ * u * Real.exp (a * v)) *
        Real.exp (k * v - σ * u * Real.exp (a * v)) = Real.exp (k * v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [← mul_assoc, he] at hh
  obtain ⟨hcor, hlong⟩ := hx.outer_radiation_majorant_on hr hzin hinu hρ hN hL
    B hB hlo hin hν hlam Γ hΓ M hM0 hmajor
  have hweight (u : Icc 0 U) (v : Icc 0 V) :
      Real.exp (-(σ * u * Real.exp (a * v))) * Real.exp (k * v) =
        Real.exp (k * v - σ * u * Real.exp (a * v)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcancel (u : Icc 0 U) (v : Icc 0 V) :
      Real.exp (-(σ * u * Real.exp (a * v))) * Γ u v = 1 := by
    change Real.exp (-_) * Real.exp _ = 1
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  constructor
  · intro u v hu
    have hh := mul_le_mul_of_nonneg_left (hcor u v hu) (Real.exp_pos (-(σ * u * Real.exp (a * v)))).le
    rw [← mul_assoc, hweight] at hh
    apply hh.trans_eq
    have he := hcancel u v
    nlinarith only [congrArg (fun q => (N / ρ) * Real.exp (a * v) *
      causalExpIntegral hV (a - k) M v * q) he]
  · intro u v hu
    let E := Real.exp (a * v)
    let W := Real.exp (-(σ * u * E))
    let J := causalExpIntegral hV (a - k) M v
    have hE : 0 < E := Real.exp_pos _
    have hJ : 0 ≤ J := intervalIntegral.integral_nonneg v.property.1
      (fun t _ => mul_nonneg (Real.exp_pos _).le (hM0 _))
    have hW : 0 ≤ W := (Real.exp_pos _).le
    have hW1 : W ≤ 1 := Real.exp_le_one_iff.2
      (neg_nonpos.2 (mul_nonneg (mul_nonneg hσ.le u.property.1) hE.le))
    have hI : W * E * (∫ t in (0 : ℝ)..u, Γ (projIcc 0 U hU t) v) ≤ 1 / σ := by
      have hq : 0 < σ * E := mul_pos hσ (Real.exp_pos _)
      have heq : (∫ t in (0 : ℝ)..u, Γ (projIcc 0 U hU t) v) =
          (σ * E)⁻¹ * (Real.exp ((σ * E) * u) - 1) := by
        calc
          _ = ∫ t in (0 : ℝ)..u, Real.exp ((σ * E) * t) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_le u.property.1] at ht
            simp only [projIcc_of_mem hU ⟨ht.1, ht.2.trans u.property.2⟩]
            change Real.exp (σ * t * E) = Real.exp ((σ * E) * t)
            congr 1
            ring
          _ = _ := by
            rw [intervalIntegral.integral_comp_mul_left _ hq.ne', integral_exp]
            simp only [mul_zero, Real.exp_zero, smul_eq_mul]
      rw [heq]
      have he : W * Real.exp ((σ * E) * u) = 1 := by
        dsimp only [W]
        rw [← Real.exp_add]
        convert Real.exp_zero using 1
        congr 1
        ring
      have he' : W * E * ((σ * E)⁻¹ * (Real.exp ((σ * E) * u) - 1)) = (1 - W) / σ := by
        field_simp [hσ.ne', hE.ne']
        ring_nf at he ⊢
        nlinarith only [he]
      rw [he']
      exact div_le_div_of_nonneg_right (sub_le_self 1 hW) hσ.le
    have hR : 0 ≤ R := (abs_nonneg _).trans (hin ⟨0, le_rfl, hU⟩)
    have hsrc : 0 ≤ Real.exp (k * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
        (L * R / ρ) * Real.exp (k * v) * (∫ t in (0 : ℝ)..u, |uIn t 1|) := by
      have hi := intervalIntegral.integral_nonneg (μ := volume) u.property.1 (fun t _ => abs_nonneg (uIn t 1))
      positivity
    have hh := mul_le_mul_of_nonneg_left (hlong u v hu) hW
    have hsrc' := mul_le_mul_of_nonneg_right hW1 hsrc
    have hfb := mul_le_mul_of_nonneg_left hI
      (mul_nonneg (div_nonneg (mul_nonneg hL hN) (sq_nonneg ρ)) hJ)
    change W * (Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1|) ≤ _ at hh
    rw [← mul_assoc, hweight] at hh
    dsimp only [J, E] at hfb
    ring_nf at hh hsrc' hfb ⊢
    nlinarith only [hh, hsrc', hfb]

theorem IsWaveIntegral.outer_radiation_spatial_kernel {U V e Λ a k ρ R N L σ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hσ : 0 < σ)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (M : C(Icc 0 V, ℝ))
    (hM : ∀ (u : Icc 0 U) (v : Icc 0 V),
      Real.exp (k * v - σ * u * Real.exp (a * v)) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v) :
    (∀ (u : Icc 0 U) (v : Icc 0 V),
      Real.exp (k * v - σ * u * Real.exp (a * v)) *
          |scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 u v| ≤
        (N / ρ) * Real.exp (a * v) * causalExpIntegral hV (a - k) M v) ∧
      ∀ (u : Icc 0 U) (v : Icc 0 V),
        Real.exp (k * v - σ * u * Real.exp (a * v)) * |x.1 u v 0 * x.2.1 u v 1| ≤
          Real.exp (k * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
          (L * R / ρ) * Real.exp (k * v) * (∫ t in (0 : ℝ)..u, |uIn t 1|) +
          (L * N / (σ * ρ ^ 2)) * causalExpIntegral hV (a - k) M v := by
  have hh := hx.outer_radiation_spatial_kernel_on hr hzin hinu ha hρ hN hL hσ
    (fun _ => U) (fun _ => hU) antitone_const
    (fun u v _ => hlo u v) hin (fun u v _ => hν u v) (fun u v _ => hlam u v)
    M (fun u v _ => hM u v)
  exact ⟨fun u v => hh.1 u v u.property.2, fun u v => hh.2 u v u.property.2⟩

noncomputable def spatialRadiationRows {U V : ℝ} (a k σ : ℝ) (x : WaveState U V) :
    C(Icc 0 V, C(Icc 0 U, ℝ)) :=
  (⟨fun q : Icc 0 V × Icc 0 U => Real.exp (k * q.1 - σ * q.2 * Real.exp (a * q.1)) *
    (x.1 q.2 q.1 0 * x.2.1 q.2 q.1 1), by fun_prop⟩ : C(Icc 0 V × Icc 0 U, ℝ)).curry

noncomputable def spatialRadiationEnvelope {U V : ℝ} (a k σ : ℝ) (x : WaveState U V) :
    C(Icc 0 V, ℝ) :=
  ⟨fun v => ‖spatialRadiationRows a k σ x v‖, (spatialRadiationRows a k σ x).continuous.norm⟩

theorem IsWaveIntegral.spatial_radiation_energy {U V e Λ a k ρ R N L σ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (ha : 0 ≤ a) (hka : k < a) (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hσ : 0 < σ)
    (hsmall : L * N / (σ * ρ ^ 2) ≤ (a - k) / 2)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L) :
    (∫ t in (0 : ℝ)..V, (spatialRadiationEnvelope a k σ x (projIcc 0 V hV t)) ^ 2) ≤
      4 * ∫ t in (0 : ℝ)..V,
        (Real.exp (k * t) * |x.1 ⟨0, le_rfl, hU⟩ (projIcc 0 V hV t) 0 *
          vOut (projIcc 0 V hV t) 1| +
            (L * R / ρ) * Real.exp (k * t) * (∫ s in (0 : ℝ)..U, |uIn s 1|)) ^ 2 := by
  let M := spatialRadiationEnvelope a k σ x
  let F := fun t => Real.exp (k * t) * |x.1 ⟨0, le_rfl, hU⟩ (projIcc 0 V hV t) 0 *
    vOut (projIcc 0 V hV t) 1| + (L * R / ρ) * Real.exp (k * t) * (∫ s in (0 : ℝ)..U, |uIn s 1|)
  have hFc : Continuous F := by dsimp only [F]; fun_prop
  have hM (u : Icc 0 U) (v : Icc 0 V) :
      Real.exp (k * v - σ * u * Real.exp (a * v)) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v := by
    have hh := (spatialRadiationRows a k σ x v).norm_coe_le_norm u
    simpa only [M, spatialRadiationEnvelope, spatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using hh
  have hkernel := (hx.outer_radiation_spatial_kernel hr hzin hinu ha hρ hN hL hσ hlo hin hν hlam M hM).2
  have hfi : IntervalIntegrable (fun t => |uIn t 1|) volume 0 U := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    exact ((ContinuousLinearMap.proj (1 : Fin 3) : WaveVector →L[ℝ] ℝ).integrable_comp
      ((Lp.memLp uIn).integrable (by norm_num))).abs
  have hR : 0 ≤ R := (abs_nonneg _).trans (hin ⟨0, le_rfl, hU⟩)
  apply causalExpIntegral_absorb_sq hV (sub_pos.2 hka) (by positivity) hsmall M
    (fun v => norm_nonneg (spatialRadiationRows a k σ x v)) ((hFc.pow 2).intervalIntegrable _ _)
  intro v
  let : Nonempty (Icc 0 U) := ⟨⟨0, le_rfl, hU⟩⟩
  apply (ContinuousMap.norm_le_of_nonempty (spatialRadiationRows a k σ x v)).2
  intro u
  have hint := intervalIntegral.integral_mono_interval le_rfl u.property.1 u.property.2
    (Filter.Eventually.of_forall (fun t => abs_nonneg (uIn t 1))) hfi
  have hcoef : 0 ≤ (L * R / ρ) * Real.exp (k * v) := by positivity
  have hsrc := mul_le_mul_of_nonneg_left hint hcoef
  have hh := hkernel u v
  simp only [F, projIcc_of_mem hV v.property, spatialRadiationRows, ContinuousMap.curry_apply,
    ContinuousMap.coe_mk, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] at hh ⊢
  linarith only [hh, hsrc]

noncomputable def movingSpatialRadiationRows {U V : ℝ}
    (B : C(Icc 0 V, ℝ)) (hB : ∀ v, 0 ≤ B v) (a k σ : ℝ) (x : WaveState U V) :
    C(Icc 0 V, C(Icc 0 U, ℝ)) :=
  (⟨fun q : Icc 0 V × Icc 0 U =>
    let u : Icc 0 U := ⟨min (q.2 : ℝ) (B q.1),
      le_min q.2.property.1 (hB q.1), (min_le_left _ _).trans q.2.property.2⟩
    Real.exp (k * q.1 - σ * u * Real.exp (a * q.1)) * (x.1 u q.1 0 * x.2.1 u q.1 1),
    by fun_prop⟩ : C(Icc 0 V × Icc 0 U, ℝ)).curry

noncomputable def movingSpatialRadiationEnvelope {U V : ℝ}
    (B : C(Icc 0 V, ℝ)) (hB : ∀ v, 0 ≤ B v) (a k σ : ℝ) (x : WaveState U V) :
    C(Icc 0 V, ℝ) :=
  ⟨fun v => ‖movingSpatialRadiationRows B hB a k σ x v‖,
    (movingSpatialRadiationRows B hB a k σ x).continuous.norm⟩

theorem movingSpatialRadiationEnvelope_le_iff {U V a k σ C : ℝ} (hU : 0 ≤ U)
    (B : C(Icc 0 V, ℝ)) (hB : ∀ v, 0 ≤ B v) (x : WaveState U V) (v : Icc 0 V) :
    movingSpatialRadiationEnvelope B hB a k σ x v ≤ C ↔
      ∀ u : Icc 0 U, (u : ℝ) ≤ B v →
        Real.exp (k * v - σ * u * Real.exp (a * v)) * |x.1 u v 0 * x.2.1 u v 1| ≤ C := by
  let : Nonempty (Icc 0 U) := ⟨⟨0, le_rfl, hU⟩⟩
  change ‖movingSpatialRadiationRows B hB a k σ x v‖ ≤ C ↔ _
  rw [ContinuousMap.norm_le_of_nonempty]
  constructor
  · intro hb u hu
    have hh := hb u
    simpa only [movingSpatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
      min_eq_left hu, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using hh
  · intro hb u
    dsimp only [movingSpatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact hb ⟨min (u : ℝ) (B v), le_min u.property.1 (hB v),
      (min_le_left _ _).trans u.property.2⟩ (min_le_right _ _)

end CauchyHorizon
