import CauchyHorizon.Reduced.RadialSecond

/-! Conservation of the transverse Raychaudhuri error for the actual rough solution. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.radialFluxVariation_transverse_integral
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      radialFluxVariation (x.1 (projIcc 0 U hU u) v) (x.2.2 u v) =
        radialFluxVariation (zIn (projIcc 0 U hU u)) (uIn u) +
          continuousPrimitive hV (radialFluxDifferential e Λ
            (x.1 (projIcc 0 U hU u)) (x.2.2 u) (hr (projIcc 0 U hU u))) v := by
  have hb := waveIteration_incoming_derivative hU hV e Λ zIn vOut uIn x hx.choose
  rw [hx.choose_spec] at hb
  filter_upwards [hx.transverse_longitudinal_derivative, hb] with u hu hb
  let a := projIcc 0 U hU u
  let T (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, ℝ) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj i)
  let R := T 0 (x.1 a)
  let N := T 0 (x.2.2 u)
  let A := T 1 (x.2.2 u)
  let L := T 2 (x.2.2 u)
  let D := radialFluxDifferential e Λ (x.1 a) (x.2.2 u) (hr a)
  let B := radialFluxVariation (zIn a) (uIn u)
  let C : C(Icc 0 V, ℝ) := ContinuousMap.const _ B + continuousPrimitive hV D -
    N * N - R * N * L + (R * R) * (A * A)
  have hC (t : ℝ) (ht : t ∈ Icc 0 V) :
      HasDerivWithinAt (intervalExtension hV C) 0 (Icc 0 V) t := by
    let v : Icc 0 V := ⟨t, ht⟩
    have hR := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (hx.longitudinal_derivative a ht)
    have hD (i : Fin 3) := (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hu v)
    have hP := (continuousPrimitive_hasDerivWithinAt hV D ht).const_add B
    have hh := ((hP.sub ((hD 0).mul (hD 0))).sub ((hR.mul (hD 0)).mul (hD 2))).add
      ((hR.mul hR).mul ((hD 1).mul (hD 1)))
    change HasDerivWithinAt (intervalExtension hV C) _ (Icc 0 V) t at hh
    apply hh.congr_deriv
    simp only [Pi.mul_apply, Function.comp_apply, ContinuousLinearMap.proj_apply,
      intervalExtension_apply, projIcc_of_mem hV ht]
    change Real.exp (x.1 a v 2) *
        (x.2.2 u v 0 * (-e ^ 2 / (2 * x.1 a v 0 ^ 3) + Λ * x.1 a v 0 / 2) +
          x.2.2 u v 2 * x.1 a v 0 * radialPotential (x.1 a v 0) e Λ) -
      (waveSource e Λ (x.1 a v) (x.2.2 u v) (x.2.1 a v) 0 * x.2.2 u v 0 +
        x.2.2 u v 0 * waveSource e Λ (x.1 a v) (x.2.2 u v) (x.2.1 a v) 0) -
      ((x.2.1 a v 0 * x.2.2 u v 0 +
        x.1 a v 0 * waveSource e Λ (x.1 a v) (x.2.2 u v) (x.2.1 a v) 0) * x.2.2 u v 2 +
        x.1 a v 0 * x.2.2 u v 0 * waveSource e Λ (x.1 a v) (x.2.2 u v) (x.2.1 a v) 2) +
      ((x.2.1 a v 0 * x.1 a v 0 + x.1 a v 0 * x.2.1 a v 0) * (x.2.2 u v 1 * x.2.2 u v 1) +
        (x.1 a v 0 * x.1 a v 0) *
          (waveSource e Λ (x.1 a v) (x.2.2 u v) (x.2.1 a v) 1 * x.2.2 u v 1 +
            x.2.2 u v 1 * waveSource e Λ (x.1 a v) (x.2.2 u v) (x.2.1 a v) 1)) = 0
    simp only [waveSource, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      radialPotential, conformalPotential]
    field_simp [hr a v]
    ring
  have h0 : C ⟨0, le_rfl, hV⟩ = 0 := by
    have hz := waveIteration_incoming_value hU hV e Λ zIn vOut uIn x hx.choose a
    rw [hx.choose_spec] at hz
    change B + (∫ t in (0 : ℝ)..0, intervalExtension hV D t) -
      (x.2.2 u ⟨0, le_rfl, hV⟩ 0 * x.2.2 u ⟨0, le_rfl, hV⟩ 0) -
      x.1 a ⟨0, le_rfl, hV⟩ 0 * x.2.2 u ⟨0, le_rfl, hV⟩ 0 * x.2.2 u ⟨0, le_rfl, hV⟩ 2 +
      (x.1 a ⟨0, le_rfl, hV⟩ 0 * x.1 a ⟨0, le_rfl, hV⟩ 0) *
        (x.2.2 u ⟨0, le_rfl, hV⟩ 1 * x.2.2 u ⟨0, le_rfl, hV⟩ 1) = 0
    rw [intervalIntegral.integral_same, hz, hb]
    dsimp only [B, radialFluxVariation]
    ring
  intro v
  have hc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le v.property.1
    (intervalExtension hV C).continuous.continuousOn
    (fun t ht => (hC t ⟨ht.1.le, ht.2.le.trans v.property.2⟩).hasDerivAt
      (Icc_mem_nhds ht.1 (ht.2.trans_le v.property.2)))
    (intervalIntegrable_const (a := (0 : ℝ)) (b := (v : ℝ)) (c := (0 : ℝ)))
  simp only [intervalIntegral.integral_zero, intervalExtension_apply,
    projIcc_of_mem hV v.property, projIcc_of_mem hV (show (0 : ℝ) ∈ Icc 0 V from ⟨le_rfl, hV⟩), h0, sub_zero] at hc
  change 0 = B + continuousPrimitive hV D v - (x.2.2 u v 0 * x.2.2 u v 0) -
    x.1 a v 0 * x.2.2 u v 0 * x.2.2 u v 2 +
    (x.1 a v 0 * x.1 a v 0) * (x.2.2 u v 1 * x.2.2 u v 1) at hc
  change radialFluxVariation (x.1 a v) (x.2.2 u v) = B + continuousPrimitive hV D v
  unfold radialFluxVariation
  nlinarith only [hc]

theorem IsWaveIntegral.radial_constraint_identity
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      1 + continuousPrimitive hV (radialFluxDifferential e Λ
          (x.1 (projIcc 0 U hU u)) (x.2.2 u) (hr (projIcc 0 U hU u))) v -
        (x.2.2 u v 0) ^ 2 =
      x.1 (projIcc 0 U hU u) v 0 * x.2.2 u v 0 * x.2.2 u v 2 -
        (x.1 (projIcc 0 U hU u) v 0) ^ 2 * (x.2.2 u v 1) ^ 2 := by
  filter_upwards [hx.radialFluxVariation_transverse_integral hr, hinu, hinell] with u hu hn hl
  have hB : radialFluxVariation (zIn (projIcc 0 U hU u)) (uIn u) = 1 := by
    simp only [radialFluxVariation, hn, hl]
    ring
  intro v
  have he := hu v
  rw [hB] at he
  unfold radialFluxVariation at he
  linarith only [he]

theorem IsWaveIntegral.transverse_constraint
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      HasDerivWithinAt (fun t => intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v)
        (x.2.2 u v 2 * radialNuField hV e Λ zIn x.1 hr (projIcc 0 U hU u) v -
          x.1 (projIcc 0 U hU u) v 0 * (x.2.2 u v 1) ^ 2) (Icc 0 U) u := by
  filter_upwards [hx.radialNu_transverse_derivative hr hzin hinu,
    hx.radial_constraint_identity hr hinu hinell, hx.radialNu_ae hr hinu] with u hd hc hn
  intro v
  apply (hd v).congr_deriv
  rw [hc v, ← hn v]
  field_simp [hr (projIcc 0 U hU u) v]

end CauchyHorizon
