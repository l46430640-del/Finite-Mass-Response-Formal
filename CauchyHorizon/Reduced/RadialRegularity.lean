import CauchyHorizon.Reduced.RadialFlux
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The continuous radial representative is the actual transverse derivative everywhere. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.radial_horizontal_identity
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.1 u v 0 = c 0 + continuousPrimitive hV vOut v 0 +
      continuousPrimitive hU (radialNuField hV e Λ zIn x.1 hr) u v := by
  let T : C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, ℝ) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj (0 : Fin 3))
  have he : T.compLpL 2 (volume.restrict (Icc 0 U)) x.2.2 =
      intervalToLp hU 2 (radialNuField hV e Λ zIn x.1 hr) := by
    apply Lp.ext
    filter_upwards [T.coeFn_compLpL x.2.2,
      intervalToLp_ae hU 2 (radialNuField hV e Λ zIn x.1 hr), hx.radialNu_ae hr hinu] with t ht hn ha
    rw [ht, hn]
    apply ContinuousMap.ext
    intro w
    exact ha w
  have hh := congrArg (fun z : WaveRectangle U V => ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) T z)
    (hx.horizontal_identity hzin)
  rw [map_add, ← horizontalPrimitive_compLp hU T x.2.2, he, horizontalPrimitive_intervalToLp] at hh
  exact congrArg (fun z : C(Icc 0 U, C(Icc 0 V, ℝ)) => z u v) hh

theorem IsWaveIntegral.radial_hasDerivWithinAt
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (v : Icc 0 V) {u : ℝ} (hu : u ∈ Icc 0 U) :
    HasDerivWithinAt (fun t => intervalExtension hU x.1 t v 0)
      (radialNuField hV e Λ zIn x.1 hr ⟨u, hu⟩ v) (Icc 0 U) u := by
  have hd := (ContinuousMap.evalCLM ℝ v : C(Icc 0 V, ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u
    (continuousPrimitive_hasDerivWithinAt hU (radialNuField hV e Λ zIn x.1 hr) hu)
  have hc := hd.const_add (c 0 + continuousPrimitive hV vOut v 0)
  apply hc.congr_of_mem _ hu
  intro t ht
  change intervalExtension hU x.1 t v 0 = c 0 + continuousPrimitive hV vOut v 0 +
    intervalExtension hU (continuousPrimitive hU (radialNuField hV e Λ zIn x.1 hr)) t v
  simpa only [intervalExtension_apply, projIcc_of_mem hU ht] using
    hx.radial_horizontal_identity hr hzin hinu ⟨t, ht⟩ v

noncomputable def radialSourceField (e Λ : ℝ) (z v : WaveRectangle U V)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (hr : ∀ u w, z u w 0 ≠ 0) :
    C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  let G := wavePotentialField e Λ z.uncurry (fun q => hr q.1 q.2)
  (⟨fun q : Icc 0 U × Icc 0 V => G q 0 - ν.uncurry q * v.uncurry q 0 / z.uncurry q 0, by
    have hG : Continuous (fun q : Icc 0 U × Icc 0 V => G q 0) := by fun_prop
    have hn : Continuous (fun q : Icc 0 U × Icc 0 V => ν.uncurry q * v.uncurry q 0) := by fun_prop
    have hd : Continuous (fun q : Icc 0 U × Icc 0 V => z.uncurry q 0) := by fun_prop
    exact hG.sub (hn.div hd (fun q => hr q.1 q.2))⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry

theorem radialSourceField_apply (e Λ : ℝ) (z w : WaveRectangle U V)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (hr : ∀ u v, z u v 0 ≠ 0) (u : Icc 0 U) (v : Icc 0 V) :
    radialSourceField e Λ z w ν hr u v =
      Real.exp (z u v 2) * radialPotential (z u v 0) e Λ - ν u v * w u v 0 / z u v 0 := rfl

theorem IsWaveIntegral.radialNu_hasDerivWithinAt
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (u : Icc 0 U) (v : Icc 0 V) :
    HasDerivWithinAt (intervalExtension hV (radialNuField hV e Λ zIn x.1 hr u))
      (radialSourceField e Λ x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr u v) (Icc 0 V) v := by
  let F := radialFluxField e Λ x.1 hr u
  have hn := (continuousPrimitive_hasDerivWithinAt hV F v.property).const_add (-zIn u 0)
  have hz := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt (v : ℝ)
    (hx.longitudinal_derivative u v.property)
  have hzero : intervalExtension hV (x.1 u) v 0 ≠ 0 := by
    simpa only [intervalExtension_apply, projIcc_of_mem hV v.property] using hr u v
  have hd := hn.div hz hzero
  change HasDerivWithinAt (intervalExtension hV (radialNuField hV e Λ zIn x.1 hr u))
    ((F v * intervalExtension hV (x.1 u) v 0 -
      (-zIn u 0 + intervalExtension hV (continuousPrimitive hV F) v) * x.2.1 u v 0) /
      (intervalExtension hV (x.1 u) v 0) ^ 2) (Icc 0 V) v at hd
  apply hd.congr_deriv
  simp only [intervalExtension_apply, projIcc_of_mem hV v.property, radialSourceField_apply,
    radialNuField_apply]
  change (radialFluxField e Λ x.1 hr u v * x.1 u v 0 -
    (-zIn u 0 + continuousPrimitive hV F v) * x.2.1 u v 0) / (x.1 u v 0) ^ 2 = _
  rw [radialFluxField_apply]
  field_simp [hr u v]
  ring

theorem IsWaveIntegral.lambda_horizontal_identity
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.2.1 u v 0 = vOut v 0 + continuousPrimitive hU
      (radialSourceField e Λ x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr) u v := by
  let N := radialNuField hV e Λ zIn x.1 hr
  let F := rectangleSource hU e Λ x hr
  let G := radialSourceField e Λ x.1 x.2.1 N hr
  let T : C(Icc 0 V, WaveVector) →L[ℝ] C(Icc 0 V, ℝ) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj (0 : Fin 3))
  have he : T.compLpL 2 (volume.restrict (Icc 0 U)) F = intervalToLp hU 2 G := by
    apply Lp.ext
    filter_upwards [T.coeFn_compLpL F, intervalToLp_ae hU 2 G,
      rectangleSource_ae hU e Λ x hr, hx.radialNu_ae hr hinu] with t ht hg hs hn
    rw [ht, hg]
    apply ContinuousMap.ext
    intro w
    change rectangleSource hU e Λ x hr t w 0 = G (projIcc 0 U hU t) w
    rw [hs w]
    change Real.exp (x.1 (projIcc 0 U hU t) w 2) * radialPotential (x.1 (projIcc 0 U hU t) w 0) e Λ -
      x.2.2 t w 0 * x.2.1 (projIcc 0 U hU t) w 0 / x.1 (projIcc 0 U hU t) w 0 = _
    rw [hn w]
    rfl
  have hv : ContinuousMap.const _ vOut + horizontalPrimitive hU F = x.2.1 :=
    congrArg (fun y : WaveState U V => y.2.1) hx.choose_spec
  have hh := congrArg (fun z : WaveRectangle U V => ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) T z) hv.symm
  rw [map_add, ← horizontalPrimitive_compLp hU T F, he, horizontalPrimitive_intervalToLp] at hh
  exact congrArg (fun z : C(Icc 0 U, C(Icc 0 V, ℝ)) => z u v) hh

theorem IsWaveIntegral.lambda_hasDerivWithinAt
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (v : Icc 0 V) {u : ℝ} (hu : u ∈ Icc 0 U) :
    HasDerivWithinAt (fun t => intervalExtension hU x.2.1 t v 0)
      (radialSourceField e Λ x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr ⟨u, hu⟩ v)
      (Icc 0 U) u := by
  let G := radialSourceField e Λ x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr
  have hd := (ContinuousMap.evalCLM ℝ v : C(Icc 0 V, ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u
    (continuousPrimitive_hasDerivWithinAt hU G hu)
  have hc := hd.const_add (vOut v 0)
  apply hc.congr_of_mem _ hu
  intro t ht
  change intervalExtension hU x.2.1 t v 0 = vOut v 0 + intervalExtension hU (continuousPrimitive hU G) t v
  simpa only [intervalExtension_apply, projIcc_of_mem hU ht] using
    hx.lambda_horizontal_identity hr hinu ⟨t, ht⟩ v

end CauchyHorizon
