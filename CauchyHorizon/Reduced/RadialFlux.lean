import CauchyHorizon.Reduced.IntegralRegularity

/-! The radial flux identity for the actual mixed-regularity integral solution. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.transverse_longitudinal_derivative
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      HasDerivWithinAt (intervalExtension hV (x.2.2 u))
        (waveSource e Λ (x.1 (projIcc 0 U hU u) v) (x.2.2 u v)
          (x.2.1 (projIcc 0 U hU u) v)) (Icc 0 V) v := by
  let F := rectangleSource hU e Λ x hx.choose
  have hu : incomingTransverse uIn + verticalPrimitive hV F = x.2.2 :=
    congrArg (fun y : WaveState U V => y.2.2) hx.choose_spec
  have hin := (ContinuousLinearMap.const ℝ (Icc 0 V) : WaveVector →L[ℝ] C(Icc 0 V, WaveVector)).coeFn_compLpL
    (p := 2) (μ := volume.restrict (Icc 0 U)) uIn
  filter_upwards [Lp.coeFn_add (incomingTransverse (V := V) uIn) (verticalPrimitive hV F),
    hin, verticalPrimitive_ae hV F, rectangleSource_ae hU e Λ x hx.choose] with u hs hi hv he
  rw [hu] at hs
  change x.2.2 u = incomingTransverse uIn u + verticalPrimitive hV F u at hs
  change incomingTransverse (V := V) uIn u = ContinuousMap.const _ (uIn u) at hi
  rw [hi, hv] at hs
  intro v
  have hd := (continuousPrimitive_hasDerivWithinAt hV (F u) v.property).const_add (uIn u)
  change HasDerivWithinAt
    (intervalExtension hV (ContinuousMap.const _ (uIn u) + continuousPrimitive hV (F u)))
    (F u v) (Icc 0 V) v at hd
  rw [← hs] at hd
  exact (he v) ▸ hd

noncomputable def radialFluxField (e Λ : ℝ) (z : WaveRectangle U V)
    (hr : ∀ u v, z u v 0 ≠ 0) : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  ((ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U × Icc 0 V)
      (ContinuousLinearMap.proj (0 : Fin 3))) z.uncurry *
    (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U × Icc 0 V)
      (ContinuousLinearMap.proj (0 : Fin 3)))
      (wavePotentialField e Λ z.uncurry (fun q => hr q.1 q.2))).curry

theorem radialFluxField_apply (e Λ : ℝ) (z : WaveRectangle U V)
    (hr : ∀ u v, z u v 0 ≠ 0) (u : Icc 0 U) (v : Icc 0 V) :
    radialFluxField e Λ z hr u v = z u v 0 * (Real.exp (z u v 2) * radialPotential (z u v 0) e Λ) := rfl

theorem IsWaveIntegral.radial_flux (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (hr : ∀ u v, x.1 u v 0 ≠ 0) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      x.1 (projIcc 0 U hU u) v 0 * x.2.2 u v 0 =
        zIn (projIcc 0 U hU u) 0 * uIn u 0 +
          continuousPrimitive hV (radialFluxField e Λ x.1 hr (projIcc 0 U hU u)) v := by
  have hb := waveIteration_incoming_derivative hU hV e Λ zIn vOut uIn x hx.choose
  rw [hx.choose_spec] at hb
  filter_upwards [hx.transverse_longitudinal_derivative, hb] with u hu hb
  let a := projIcc 0 U hU u
  let q : C(Icc 0 V, ℝ) := ⟨fun v => x.1 a v 0 * x.2.2 u v 0, by fun_prop⟩
  let F := radialFluxField e Λ x.1 hr a
  have hd (v : ℝ) (hv : v ∈ Icc 0 V) :
      HasDerivWithinAt (intervalExtension hV q) (F ⟨v, hv⟩) (Icc 0 V) v := by
    have hz := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt v
      (hx.longitudinal_derivative a hv)
    have hn := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt v
      (hu ⟨v, hv⟩)
    have hp := hz.mul hn
    change HasDerivWithinAt (intervalExtension hV q)
      (x.2.1 a ⟨v, hv⟩ 0 * intervalExtension hV (x.2.2 u) v 0 +
        intervalExtension hV (x.1 a) v 0 * waveSource e Λ (x.1 a ⟨v, hv⟩)
          (x.2.2 u ⟨v, hv⟩) (x.2.1 a ⟨v, hv⟩) 0) (Icc 0 V) v at hp
    have he : x.2.1 a ⟨v, hv⟩ 0 * intervalExtension hV (x.2.2 u) v 0 +
        intervalExtension hV (x.1 a) v 0 * waveSource e Λ (x.1 a ⟨v, hv⟩)
          (x.2.2 u ⟨v, hv⟩) (x.2.1 a ⟨v, hv⟩) 0 = F ⟨v, hv⟩ := by
      simp only [intervalExtension_apply, projIcc_of_mem hV hv]
      change _ * _ + x.1 a ⟨v, hv⟩ 0 * (Real.exp (x.1 a ⟨v, hv⟩ 2) *
        radialPotential (x.1 a ⟨v, hv⟩ 0) e Λ - _ / x.1 a ⟨v, hv⟩ 0) =
        x.1 a ⟨v, hv⟩ 0 * (Real.exp (x.1 a ⟨v, hv⟩ 2) * radialPotential (x.1 a ⟨v, hv⟩ 0) e Λ)
      field_simp [hr a ⟨v, hv⟩]
      ring
    rwa [he] at hp
  intro v
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le v.property.1
    (intervalExtension hV q).continuous.continuousOn
    (fun t ht => by
      have htV : t ∈ Icc 0 V := ⟨ht.1.le, ht.2.le.trans v.property.2⟩
      have hdt := (hd t htV).hasDerivAt (Icc_mem_nhds ht.1 (ht.2.trans_le v.property.2))
      simpa only [intervalExtension_apply, projIcc_of_mem hV htV] using hdt)
    ((intervalExtension hV F).continuous.intervalIntegrable (0 : ℝ) v)
  change continuousPrimitive hV F v = intervalExtension hV q v - intervalExtension hV q 0 at hp
  simp only [intervalExtension_apply, projIcc_of_mem hV v.property,
    projIcc_of_mem hV (show (0 : ℝ) ∈ Icc 0 V from ⟨le_rfl, hV⟩)] at hp
  have hz := waveIteration_incoming_value hU hV e Λ zIn vOut uIn x hx.choose a
  rw [hx.choose_spec] at hz
  change continuousPrimitive hV F v = x.1 a v 0 * x.2.2 u v 0 -
    x.1 a ⟨0, le_rfl, hV⟩ 0 * x.2.2 u ⟨0, le_rfl, hV⟩ 0 at hp
  rw [hz, hb] at hp
  change x.1 a v 0 * x.2.2 u v 0 = zIn a 0 * uIn u 0 + continuousPrimitive hV F v
  linarith only [hp]

noncomputable def radialNuField (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (z : WaveRectangle U V)
    (hr : ∀ u v, z u v 0 ≠ 0) : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  let p : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
    (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (continuousPrimitiveL hV))
      (radialFluxField e Λ z hr)
  (⟨fun q : Icc 0 U × Icc 0 V => (-zIn q.1 0 + p.uncurry q) / z.uncurry q 0, by
    have hn : Continuous (fun q : Icc 0 U × Icc 0 V => -zIn q.1 0 + p.uncurry q) := by fun_prop
    have hd : Continuous (fun q : Icc 0 U × Icc 0 V => z.uncurry q 0) := by fun_prop
    exact hn.div hd (fun q => hr q.1 q.2)⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry

theorem radialNuField_apply (hV : 0 ≤ V) (e Λ : ℝ) (zIn : C(Icc 0 U, WaveVector))
    (z : WaveRectangle U V) (hr : ∀ u v, z u v 0 ≠ 0) (u : Icc 0 U) (v : Icc 0 V) :
    radialNuField hV e Λ zIn z hr u v =
      (-zIn u 0 + continuousPrimitive hV (radialFluxField e Λ z hr u) v) / z u v 0 := rfl

theorem IsWaveIntegral.radialNu_ae (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      x.2.2 u v 0 = radialNuField hV e Λ zIn x.1 hr (projIcc 0 U hU u) v := by
  filter_upwards [hx.radial_flux hr, hinu] with u hu hi
  intro v
  rw [radialNuField_apply]
  apply (eq_div_iff (hr _ _)).2
  have hv := hu v
  rw [hi, mul_neg_one] at hv
  simpa only [mul_comm] using hv

theorem IsWaveIntegral.radialNu_incoming (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (hr : ∀ u v, x.1 u v 0 ≠ 0) (u : Icc 0 U) :
    radialNuField hV e Λ zIn x.1 hr u ⟨0, le_rfl, hV⟩ = -1 := by
  have hz := waveIteration_incoming_value hU hV e Λ zIn vOut uIn x hx.choose u
  rw [hx.choose_spec] at hz
  have hr0 := hr u ⟨0, le_rfl, hV⟩
  rw [hz] at hr0
  rw [radialNuField_apply]
  change (-zIn u 0 + (∫ t in (0 : ℝ)..0, _)) / x.1 u ⟨0, le_rfl, hV⟩ 0 = -1
  simp only [intervalIntegral.integral_same, add_zero, hz, neg_div, div_self hr0]

end CauchyHorizon
