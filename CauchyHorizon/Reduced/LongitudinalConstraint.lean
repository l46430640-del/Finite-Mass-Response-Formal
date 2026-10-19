import CauchyHorizon.Reduced.LongitudinalFlux
import CauchyHorizon.Reduced.ConstraintIntegral

/-! The outgoing constraint follows from an absolutely continuous quadratic flux. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.radialFluxVariation_integral
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (u : Icc 0 U) (v : Icc 0 V) :
    radialFluxVariation (x.1 u v) (x.2.1 u v) =
      radialFluxVariation (x.1 ⟨0, le_rfl, hU⟩ v) (vOut v) +
      continuousPrimitive hU (radialFluxDifferential e Λ (flipRectangle x.1 v)
        (flipRectangle x.2.1 v) (fun u => hr u v)) u := by
  let T (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v)
  let Z (i : Fin 3) : ℝ → ℝ := fun t => intervalExtension hU x.1 t v i
  let W (i : Fin 3) : ℝ → ℝ := fun t => intervalExtension hU x.2.1 t v i
  let H : ℝ → ℝ := W 0 * W 0 + Z 0 * W 0 * W 2 - (Z 0 * Z 0) * (W 1 * W 1)
  let D := radialFluxDifferential e Λ (flipRectangle x.1 v) (flipRectangle x.2.1 v) (fun u => hr u v)
  have hZ (i : Fin 3) : AbsolutelyContinuousOnInterval (Z i) 0 U :=
    absolutelyContinuous_comp_contDiffAt (f := intervalExtension hU x.1) (g := T i)
      (hx.horizontal_absolutelyContinuous hzin)
      (fun _ _ => (T i).contDiff.contDiffAt)
  have hW (i : Fin 3) : AbsolutelyContinuousOnInterval (W i) 0 U :=
    absolutelyContinuous_comp_contDiffAt (f := intervalExtension hU x.2.1) (g := T i)
      hx.velocity_horizontal_absolutelyContinuous
      (fun _ _ => (T i).contDiff.contDiffAt)
  have hH : AbsolutelyContinuousOnInterval H 0 U :=
    (((hW 0).mul (hW 0)).add (((hZ 0).mul (hW 0)).mul (hW 2))).sub
      (((hZ 0).mul (hZ 0)).mul ((hW 1).mul (hW 1)))
  have he : deriv H =ᵐ[volume.restrict (Icc 0 U)] intervalExtension hU D := by
    filter_upwards [hx.horizontal_derivative hzin, hx.wave_equation,
      ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc 0 U)).ae_ne 0,
      (volume.restrict (Icc 0 U)).ae_ne U] with t hz hw ht ht0 htU
    have hdZ := (T 0).hasFDerivAt.comp_hasDerivWithinAt t hz
    have hdW (i : Fin 3) := (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hw v)
    have hh := (((hdW 0).mul (hdW 0)).add ((hdZ.mul (hdW 0)).mul (hdW 2))).sub
      ((hdZ.mul hdZ).mul ((hdW 1).mul (hdW 1)))
    change HasDerivWithinAt H _ (Icc 0 U) t at hh
    have hd : HasDerivWithinAt H (intervalExtension hU D t) (Icc 0 U) t := by
      apply hh.congr_deriv
      simp only [Pi.mul_apply, Function.comp_apply,
        ContinuousLinearMap.proj_apply, intervalExtension_apply, projIcc_of_mem hU ht]
      change (waveSource e Λ (x.1 ⟨t, ht⟩ v) (x.2.2 t v) (x.2.1 ⟨t, ht⟩ v) 0 * x.2.1 ⟨t, ht⟩ v 0 +
          x.2.1 ⟨t, ht⟩ v 0 * waveSource e Λ (x.1 ⟨t, ht⟩ v) (x.2.2 t v) (x.2.1 ⟨t, ht⟩ v) 0) +
        ((x.2.2 t v 0 * x.2.1 ⟨t, ht⟩ v 0 + x.1 ⟨t, ht⟩ v 0 *
          waveSource e Λ (x.1 ⟨t, ht⟩ v) (x.2.2 t v) (x.2.1 ⟨t, ht⟩ v) 0) * x.2.1 ⟨t, ht⟩ v 2 +
          x.1 ⟨t, ht⟩ v 0 * x.2.1 ⟨t, ht⟩ v 0 *
            waveSource e Λ (x.1 ⟨t, ht⟩ v) (x.2.2 t v) (x.2.1 ⟨t, ht⟩ v) 2) -
        ((x.2.2 t v 0 * x.1 ⟨t, ht⟩ v 0 + x.1 ⟨t, ht⟩ v 0 * x.2.2 t v 0) *
          (x.2.1 ⟨t, ht⟩ v 1 * x.2.1 ⟨t, ht⟩ v 1) +
          (x.1 ⟨t, ht⟩ v 0 * x.1 ⟨t, ht⟩ v 0) *
          (waveSource e Λ (x.1 ⟨t, ht⟩ v) (x.2.2 t v) (x.2.1 ⟨t, ht⟩ v) 1 * x.2.1 ⟨t, ht⟩ v 1 +
            x.2.1 ⟨t, ht⟩ v 1 * waveSource e Λ (x.1 ⟨t, ht⟩ v) (x.2.2 t v) (x.2.1 ⟨t, ht⟩ v) 1)) =
        Real.exp (x.1 ⟨t, ht⟩ v 2) * (x.2.1 ⟨t, ht⟩ v 0 *
          (-e ^ 2 / (2 * x.1 ⟨t, ht⟩ v 0 ^ 3) + Λ * x.1 ⟨t, ht⟩ v 0 / 2) +
          x.2.1 ⟨t, ht⟩ v 2 * x.1 ⟨t, ht⟩ v 0 * radialPotential (x.1 ⟨t, ht⟩ v 0) e Λ)
      simp only [waveSource, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        radialPotential, conformalPotential]
      field_simp [hr ⟨t, ht⟩ v]
      ring
    exact (hd.hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne ht.1 ht0.symm)
      (lt_of_le_of_ne ht.2 htU))).deriv
  have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le u.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl u.property.2
  have hp := (hH.mono hsub).integral_deriv_eq_sub
  have hs : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
  rw [intervalIntegral.integral_of_le u.property.1,
    integral_congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) he)] at hp
  have hzero := waveIteration_outgoing_derivative hU hV e Λ zIn vOut uIn x hx.choose
  rw [hx.choose_spec] at hzero
  simp only [H, Z, W, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, intervalExtension_apply,
    projIcc_of_mem hU u.property, projIcc_of_mem hU (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU⟩), hzero] at hp
  change _ = _ + (∫ t in (0 : ℝ)..u, intervalExtension hU D t)
  rw [intervalIntegral.integral_of_le u.property.1]
  have hp' : (∫ t in Ioc (0 : ℝ) u, intervalExtension hU D t) =
    radialFluxVariation (x.1 u v) (x.2.1 u v) -
      radialFluxVariation (x.1 ⟨0, le_rfl, hU⟩ v) (vOut v) := by
    simpa only [radialFluxVariation, sq, intervalExtension_apply] using hp
  linarith only [hp']

theorem IsWaveIntegral.longitudinal_constraint
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    {v : ℝ} (hv : v ∈ Icc 0 V)
    (hout : HasDerivWithinAt (fun t => intervalExtension hV vOut t 0)
      (vOut ⟨v, hv⟩ 2 * vOut ⟨v, hv⟩ 0 -
        x.1 ⟨0, le_rfl, hU⟩ ⟨v, hv⟩ 0 * (vOut ⟨v, hv⟩ 1) ^ 2) (Icc 0 V) v)
    (u : Icc 0 U) :
    HasDerivWithinAt (fun t => intervalExtension hV (x.2.1 u) t 0)
      (x.2.1 u ⟨v, hv⟩ 2 * x.2.1 u ⟨v, hv⟩ 0 -
        x.1 u ⟨v, hv⟩ 0 * (x.2.1 u ⟨v, hv⟩ 1) ^ 2) (Icc 0 V) v := by
  let a : Icc 0 V := ⟨v, hv⟩
  let o : Icc 0 U := ⟨0, le_rfl, hU⟩
  let F := radialFluxField e Λ (flipRectangle x.1) (fun v u => hr u v)
  let D := radialFluxDifferential e Λ (flipRectangle x.1 a) (flipRectangle x.2.1 a) (fun u => hr u a)
  have hF := radialFluxField_hasDerivWithinAt (flipRectangle x.1)
    (fun v u => hr u v) hv (hx.longitudinal_section_derivative hv) (e := e) (Λ := Λ)
  have hP := (continuousPrimitiveL (E := ℝ) hU).hasFDerivAt.comp_hasDerivWithinAt v hF
  have hPu := (ContinuousMap.evalCLM ℝ u : C(Icc 0 U, ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt v hP
  have hR (w : Icc 0 U) := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
    v (hx.longitudinal_derivative w hv)
  have hb := waveIteration_outgoing_derivative hU hV e Λ zIn vOut uIn x hx.choose
  rw [hx.choose_spec] at hb
  have hn : intervalExtension hV (x.1 u) v 0 ≠ 0 := by
    simpa only [intervalExtension_apply, projIcc_of_mem hV hv] using hr u a
  have hd := (((hR o).mul hout).add hPu).div (hR u) hn
  have hd' := hd.congr_of_mem (f₁ := fun t => intervalExtension hV (x.2.1 u) t 0)
    (fun t ht => ?_) hv
  · apply hd'.congr_deriv
    simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, ContinuousLinearMap.proj_apply,
      intervalExtension_apply, projIcc_of_mem hV hv]
    change ((x.2.1 o a 0 * vOut a 0 + x.1 o a 0 *
        (vOut a 2 * vOut a 0 - x.1 o a 0 * (vOut a 1) ^ 2) + continuousPrimitive hU D u) *
        x.1 u a 0 - (x.1 o a 0 * vOut a 0 + continuousPrimitive hU (F a) u) *
        x.2.1 u a 0) / (x.1 u a 0) ^ 2 = _
    have hflux := hx.horizontal_radial_flux hr hzin u a
    have hvar := hx.radialFluxVariation_integral hr hzin u a
    change x.1 u a 0 * x.2.1 u a 0 = x.1 o a 0 * vOut a 0 + continuousPrimitive hU (F a) u at hflux
    change radialFluxVariation (x.1 u a) (x.2.1 u a) =
      radialFluxVariation (x.1 o a) (vOut a) + continuousPrimitive hU D u at hvar
    rw [← hflux]
    have hbo : x.2.1 o = vOut := hb
    rw [hbo]
    have hn' := hr u a
    dsimp only [a] at hvar hn' ⊢
    field_simp [hn']
    unfold radialFluxVariation at hvar
    nlinarith only [hvar]
  · simp only [Pi.div_apply, Pi.mul_apply, Pi.add_apply, Function.comp_apply, intervalExtension_apply,
      projIcc_of_mem hV ht]
    have hf := hx.horizontal_radial_flux hr hzin u ⟨t, ht⟩
    change x.2.1 u ⟨t, ht⟩ 0 =
      (x.1 o ⟨t, ht⟩ 0 * vOut ⟨t, ht⟩ 0 + continuousPrimitive hU (F ⟨t, ht⟩) u) /
        x.1 u ⟨t, ht⟩ 0
    exact (eq_div_iff (hr u ⟨t, ht⟩)).2 (by simpa only [mul_comm] using hf)

theorem IsWaveIntegral.longitudinal_constraint_integral
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hout : ∀ t (ht : t ∈ Icc 0 V), HasDerivWithinAt (fun s => intervalExtension hV vOut s 0)
      (vOut ⟨t, ht⟩ 2 * vOut ⟨t, ht⟩ 0 -
        x.1 ⟨0, le_rfl, hU⟩ ⟨t, ht⟩ 0 * (vOut ⟨t, ht⟩ 1) ^ 2) (Icc 0 V) t)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.2.1 u v 0 * Real.exp (-x.1 u v 2) =
      x.2.1 u ⟨0, le_rfl, hV⟩ 0 * Real.exp (-x.1 u ⟨0, le_rfl, hV⟩ 2) -
        ∫ t in (0 : ℝ)..v, intervalExtension hV (x.1 u) t 0 *
          Real.exp (-intervalExtension hV (x.1 u) t 2) * (intervalExtension hV (x.2.1 u) t 1) ^ 2 := by
  let q : C(Icc 0 V, ℝ) := ⟨fun w => x.2.1 u w 0 * Real.exp (-x.1 u w 2), by fun_prop⟩
  let D : C(Icc 0 V, ℝ) := ⟨fun w => x.1 u w 0 * Real.exp (-x.1 u w 2) * (x.2.1 u w 1) ^ 2, by fun_prop⟩
  have hd (t : ℝ) (ht : t ∈ Icc 0 V) :
      HasDerivWithinAt (intervalExtension hV q) (-intervalExtension hV D t) (Icc 0 V) t := by
    have hl := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      t (hx.longitudinal_derivative u ht)
    have hh := (hx.longitudinal_constraint hr hzin ht (hout t ht) u).mul hl.neg.exp
    change HasDerivWithinAt (intervalExtension hV q) _ (Icc 0 V) t at hh
    apply hh.congr_deriv
    simp only [Pi.neg_apply, Function.comp_apply, ContinuousLinearMap.proj_apply,
      intervalExtension_apply, projIcc_of_mem hV ht]
    change (x.2.1 u ⟨t, ht⟩ 2 * x.2.1 u ⟨t, ht⟩ 0 - x.1 u ⟨t, ht⟩ 0 * (x.2.1 u ⟨t, ht⟩ 1) ^ 2) *
      Real.exp (-x.1 u ⟨t, ht⟩ 2) + x.2.1 u ⟨t, ht⟩ 0 *
        (Real.exp (-x.1 u ⟨t, ht⟩ 2) * -x.2.1 u ⟨t, ht⟩ 2) =
      -(x.1 u ⟨t, ht⟩ 0 * Real.exp (-x.1 u ⟨t, ht⟩ 2) * (x.2.1 u ⟨t, ht⟩ 1) ^ 2)
    ring
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le v.property.1
    (intervalExtension hV q).continuous.continuousOn
    (fun t ht => (hd t ⟨ht.1.le, ht.2.le.trans v.property.2⟩).hasDerivAt
      (Icc_mem_nhds ht.1 (ht.2.trans_le v.property.2)))
    ((intervalExtension hV D).continuous.neg.intervalIntegrable (0 : ℝ) v)
  rw [intervalIntegral.integral_neg] at hp
  simp only [intervalExtension_apply, projIcc_of_mem hV v.property,
    projIcc_of_mem hV (show (0 : ℝ) ∈ Icc 0 V from ⟨le_rfl, hV⟩)] at hp
  change -(∫ t in (0 : ℝ)..v, intervalExtension hV (x.1 u) t 0 *
      Real.exp (-intervalExtension hV (x.1 u) t 2) * (intervalExtension hV (x.2.1 u) t 1) ^ 2) =
    x.2.1 u v 0 * Real.exp (-x.1 u v 2) -
      x.2.1 u ⟨0, le_rfl, hV⟩ 0 * Real.exp (-x.1 u ⟨0, le_rfl, hV⟩ 2) at hp
  linarith only [hp]

end CauchyHorizon
