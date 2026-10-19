import CauchyHorizon.Reduced.RadialRegularity
import CauchyHorizon.Analysis.ContinuousCalculus

/-! The transverse derivative of the radial flux, in the continuous section norm. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}

noncomputable def radialFluxVariation (z w : WaveVector) : ℝ :=
  (w 0) ^ 2 + z 0 * w 0 * w 2 - (z 0) ^ 2 * (w 1) ^ 2

noncomputable def radialFluxDifferential (e Λ : ℝ) (z d : C(Icc 0 V, WaveVector))
    (hr : ∀ v, z v 0 ≠ 0) : C(Icc 0 V, ℝ) :=
  ⟨fun v => Real.exp (z v 2) *
    (d v 0 * (-e ^ 2 / (2 * z v 0 ^ 3) + Λ * z v 0 / 2) +
      d v 2 * z v 0 * radialPotential (z v 0) e Λ), by
    unfold radialPotential
    fun_prop (disch := simp [hr])⟩

theorem radialFluxField_hasDerivWithinAt (z : WaveRectangle U V)
    (hr : ∀ u v, z u v 0 ≠ 0) {u : ℝ} (hu : u ∈ Icc 0 U)
    {d : C(Icc 0 V, WaveVector)}
    (hd : HasDerivWithinAt (intervalExtension hU z) d (Icc 0 U) u) :
    HasDerivWithinAt (intervalExtension hU (radialFluxField e Λ z hr))
      (radialFluxDifferential e Λ (z ⟨u, hu⟩) d (hr ⟨u, hu⟩)) (Icc 0 U) u := by
  let T (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, ℝ) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj i)
  let R := fun t => T 0 (intervalExtension hU z t)
  let L := fun t => T 2 (intervalExtension hU z t)
  have hT (i : Fin 3) (f : C(Icc 0 V, WaveVector)) (v : Icc 0 V) : T i f v = f v i := rfl
  have hR := (T 0).hasFDerivAt.comp_hasDerivWithinAt u hd
  have hL := (T 2).hasFDerivAt.comp_hasDerivWithinAt u hd
  change HasDerivWithinAt R (T 0 d) (Icc 0 U) u at hR
  change HasDerivWithinAt L (T 2 d) (Icc 0 U) u at hL
  have hn (t : ℝ) (v : Icc 0 V) : R t v ≠ 0 := hr _ v
  have hI := continuousMap_inverse_hasDerivWithinAt hR (hn u)
  have hE := (hasFDerivAt_exp (𝕂 := ℝ) (x := L u)).comp_hasDerivWithinAt u hL
  have hB := (((hI.mul hI).const_smul (e ^ 2 / 4)).const_add
    (ContinuousMap.const _ (-1 / 4 : ℝ))).add ((hR.mul hR).const_smul (Λ / 4))
  have hh := hE.mul hB
  have he := hh.congr_of_mem (f₁ := intervalExtension hU (radialFluxField e Λ z hr))
    (fun t (_ : t ∈ Icc 0 U) => ?_) hu
  · apply he.congr_deriv
    apply ContinuousMap.ext
    intro v
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_apply,
      one_apply_eq_self, smul_eq_mul, ContinuousMap.mul_apply,
      ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.smul_apply,
      ContinuousMap.neg_apply, continuousMap_exp_apply,
      continuousMap_inverse_apply _ (hn u)]
    simp only [R, L, hT,
      intervalExtension_apply, projIcc_of_mem hU hu]
    change _ = Real.exp (z ⟨u, hu⟩ v 2) *
      (d v 0 * (-e ^ 2 / (2 * z ⟨u, hu⟩ v 0 ^ 3) + Λ * z ⟨u, hu⟩ v 0 / 2) +
        d v 2 * z ⟨u, hu⟩ v 0 * radialPotential (z ⟨u, hu⟩ v 0) e Λ)
    unfold radialPotential
    field_simp [hr ⟨u, hu⟩ v]
    ring
  · apply ContinuousMap.ext
    intro v
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply,
      intervalExtension_apply, radialFluxField_apply, Function.comp_apply,
      ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.const_apply,
      ContinuousMap.smul_apply, continuousMap_exp_apply,
      continuousMap_inverse_apply _ (hn t), smul_eq_mul]
    change _ = Real.exp (z (projIcc 0 U hU t) v 2) *
      ((-1 / 4 : ℝ) + (e ^ 2 / 4) * ((z (projIcc 0 U hU t) v 0)⁻¹ *
        (z (projIcc 0 U hU t) v 0)⁻¹) + (Λ / 4) *
          (z (projIcc 0 U hU t) v 0 * z (projIcc 0 U hU t) v 0))
    unfold radialPotential
    field_simp [hr (projIcc 0 U hU t) v]

variable {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.radialNu_transverse_derivative
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      HasDerivWithinAt (fun t => intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v)
        ((1 + continuousPrimitive hV (radialFluxDifferential e Λ
            (x.1 (projIcc 0 U hU u)) (x.2.2 u) (hr (projIcc 0 U hU u))) v -
          (x.2.2 u v 0) ^ 2) / x.1 (projIcc 0 U hU u) v 0) (Icc 0 U) u := by
  have hzi : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (intervalExtension hU zIn) (uIn u) (Icc 0 U) u := by
    rw [hzin, map_add]
    filter_upwards [horizontalPrimitive_ae_hasDerivWithinAt hU uIn] with u hu
    exact hu.const_add c
  filter_upwards [hx.horizontal_derivative hzin, hzi, hinu, hx.radialNu_ae hr hinu,
    ae_restrict_mem measurableSet_Icc] with u hz hi hn ha hu
  let a : Icc 0 U := ⟨u, hu⟩
  have hF := radialFluxField_hasDerivWithinAt x.1 hr hu hz (e := e) (Λ := Λ)
  have hP := (continuousPrimitiveL (E := ℝ) hV).hasFDerivAt.comp_hasDerivWithinAt u hF
  intro v
  let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  have hR := T.hasFDerivAt.comp_hasDerivWithinAt u hz
  have hI := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u hi
  have hPv := (ContinuousMap.evalCLM ℝ v : C(Icc 0 V, ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u hP
  have hzero : intervalExtension hU x.1 u v 0 ≠ 0 := by
    simpa only [intervalExtension_apply, projIcc_of_mem hU hu] using hr a v
  have hh := (hI.neg.add hPv).div hR hzero
  change HasDerivWithinAt (fun t => intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v)
    (((-uIn u 0 + continuousPrimitive hV (radialFluxDifferential e Λ (x.1 a) (x.2.2 u) (hr a)) v) *
        intervalExtension hU x.1 u v 0 -
      (-intervalExtension hU zIn u 0 + continuousPrimitive hV
        (intervalExtension hU (radialFluxField e Λ x.1 hr) u) v) * x.2.2 u v 0) /
      (intervalExtension hU x.1 u v 0) ^ 2) (Icc 0 U) u at hh
  apply hh.congr_deriv
  simp only [intervalExtension_apply, projIcc_of_mem hU hu, hn, neg_neg] at ha ⊢
  have he := (eq_div_iff (hr a v)).1 (ha v)
  change x.2.2 u v 0 * x.1 a v 0 =
    -zIn a 0 + continuousPrimitive hV (radialFluxField e Λ x.1 hr a) v at he
  dsimp only [a] at he ⊢
  rw [← he]
  field_simp [hr ⟨u, hu⟩ v]

end CauchyHorizon
