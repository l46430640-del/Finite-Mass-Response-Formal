import CauchyHorizon.Reduced.RadialRegularity

/-! Scalar transport and local Lp preservation for the actual rough integral solution. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

noncomputable def waveCoordinateField (i : Fin 3) (z : WaveRectangle U V) : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
    (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj i)) z

noncomputable def scalarTransportSource (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (w : WaveRectangle U V) :
    C(Icc 0 U, C(Icc 0 V, ℝ)) := -ν * waveCoordinateField 1 w

noncomputable def scalarTransportCorrection (hV : 0 ≤ V) (ν : C(Icc 0 U, C(Icc 0 V, ℝ)))
    (w : WaveRectangle U V) : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (continuousPrimitiveL hV) (scalarTransportSource ν w)

noncomputable def scalarIncomingCoefficient (zIn : C(Icc 0 U, WaveVector)) (z : WaveRectangle U V)
    (hr : ∀ u v, z u v 0 ≠ 0) : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  (⟨fun q : Icc 0 U × Icc 0 V => zIn q.1 0 / z.uncurry q 0, by
    have hn : Continuous (fun q : Icc 0 U × Icc 0 V => zIn q.1 0) := by fun_prop
    have hd : Continuous (fun q : Icc 0 U × Icc 0 V => z.uncurry q 0) := by fun_prop
    exact hn.div hd (fun q => hr q.1 q.2)⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry

noncomputable def scalarRegularPart (hV : 0 ≤ V) (z w : WaveRectangle U V)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (hr : ∀ u v, z u v 0 ≠ 0) : C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  let C := scalarTransportCorrection hV ν w
  (⟨fun q : Icc 0 U × Icc 0 V => C.uncurry q / z.uncurry q 0, by
    have hd : Continuous (fun q : Icc 0 U × Icc 0 V => z.uncurry q 0) := by fun_prop
    exact C.uncurry.continuous.div hd (fun q => hr q.1 q.2)⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry

theorem IsWaveIntegral.zeta_transport
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      x.1 (projIcc 0 U hU u) v 0 * x.2.2 u v 1 =
        zIn (projIcc 0 U hU u) 0 * uIn u 1 +
          scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 (projIcc 0 U hU u) v := by
  have hb := waveIteration_incoming_derivative hU hV e Λ zIn vOut uIn x hx.choose
  rw [hx.choose_spec] at hb
  filter_upwards [hx.transverse_longitudinal_derivative, hx.radialNu_ae hr hinu, hb] with u hu hn hb
  let a := projIcc 0 U hU u
  let N := radialNuField hV e Λ zIn x.1 hr
  let q : C(Icc 0 V, ℝ) := ⟨fun v => x.1 a v 0 * x.2.2 u v 1, by fun_prop⟩
  let F := scalarTransportSource N x.2.1 a
  have hd (v : ℝ) (hv : v ∈ Icc 0 V) :
      HasDerivWithinAt (intervalExtension hV q) (F ⟨v, hv⟩) (Icc 0 V) v := by
    have hz := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt v
      (hx.longitudinal_derivative a hv)
    have hs := (ContinuousLinearMap.proj (1 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt v
      (hu ⟨v, hv⟩)
    have hp := hz.mul hs
    change HasDerivWithinAt (intervalExtension hV q)
      (x.2.1 a ⟨v, hv⟩ 0 * intervalExtension hV (x.2.2 u) v 1 +
        intervalExtension hV (x.1 a) v 0 * waveSource e Λ (x.1 a ⟨v, hv⟩)
          (x.2.2 u ⟨v, hv⟩) (x.2.1 a ⟨v, hv⟩) 1) (Icc 0 V) v at hp
    apply hp.congr_deriv
    simp only [intervalExtension_apply, projIcc_of_mem hV hv]
    change _ * _ + x.1 a ⟨v, hv⟩ 0 *
      (-(x.2.2 u ⟨v, hv⟩ 0 * x.2.1 a ⟨v, hv⟩ 1 + x.2.1 a ⟨v, hv⟩ 0 * x.2.2 u ⟨v, hv⟩ 1) /
        x.1 a ⟨v, hv⟩ 0) = -N a ⟨v, hv⟩ * x.2.1 a ⟨v, hv⟩ 1
    rw [hn ⟨v, hv⟩]
    field_simp [hr a ⟨v, hv⟩]
    ring
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
  change continuousPrimitive hV F v = x.1 a v 0 * x.2.2 u v 1 -
    x.1 a ⟨0, le_rfl, hV⟩ 0 * x.2.2 u ⟨0, le_rfl, hV⟩ 1 at hp
  rw [hz, hb] at hp
  change x.1 a v 0 * x.2.2 u v 1 = zIn a 0 * uIn u 1 + continuousPrimitive hV F v
  linarith only [hp]

theorem IsWaveIntegral.scalar_decomposition
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U),
      (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u) =
        uIn u 1 • scalarIncomingCoefficient zIn x.1 hr (projIcc 0 U hU u) +
          scalarRegularPart hV x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr (projIcc 0 U hU u) := by
  filter_upwards [hx.zeta_transport hr hinu] with u hu
  apply ContinuousMap.ext
  intro v
  change x.2.2 u v 1 = uIn u 1 * (zIn (projIcc 0 U hU u) 0 / x.1 (projIcc 0 U hU u) v 0) +
    scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 (projIcc 0 U hU u) v /
      x.1 (projIcc 0 U hU u) v 0
  have he := hu v
  field_simp [hr (projIcc 0 U hU u) v]
  nlinarith only [he]

theorem IsWaveIntegral.scalar_transverse_memLp
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {p : ℝ≥0∞} (hf : MemLp (fun u => uIn u 1) p (volume.restrict (Icc 0 U))) :
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u)) p (volume.restrict (Icc 0 U)) := by
  let A := scalarIncomingCoefficient zIn x.1 hr
  let B := scalarRegularPart hV x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr
  have hA : MemLp (intervalExtension hU A) ∞ (volume.restrict (Icc 0 U)) :=
    (intervalExtension hU A).memLp_top
  have hB : MemLp (intervalExtension hU B) p (volume.restrict (Icc 0 U)) :=
    (intervalExtension hU B).memLp_top.mono_exponent le_top
  apply ((hA.smul hf).add hB).ae_eq
  filter_upwards [hx.scalar_decomposition hr hinu] with u hu
  exact hu.symm

theorem IsWaveIntegral.theta_transport
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      HasDerivWithinAt (fun t => intervalExtension hU x.1 t v 0 * intervalExtension hU x.2.1 t v 1)
        (-x.2.1 (projIcc 0 U hU u) v 0 * x.2.2 u v 1) (Icc 0 U) u := by
  filter_upwards [hx.horizontal_derivative hzin, hx.wave_equation] with u hu hv
  intro v
  let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  have hz := T.hasFDerivAt.comp_hasDerivWithinAt u hu
  have hs := (ContinuousLinearMap.proj (1 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt u (hv v)
  have hp := hz.mul hs
  change HasDerivWithinAt (fun t => intervalExtension hU x.1 t v 0 * intervalExtension hU x.2.1 t v 1)
    (x.2.2 u v 0 * intervalExtension hU x.2.1 u v 1 + intervalExtension hU x.1 u v 0 *
      waveSource e Λ (x.1 (projIcc 0 U hU u) v) (x.2.2 u v) (x.2.1 (projIcc 0 U hU u) v) 1) (Icc 0 U) u at hp
  apply hp.congr_deriv
  simp only [intervalExtension_apply]
  change _ * _ + x.1 (projIcc 0 U hU u) v 0 *
    (-(x.2.2 u v 0 * x.2.1 (projIcc 0 U hU u) v 1 + x.2.1 (projIcc 0 U hU u) v 0 * x.2.2 u v 1) /
      x.1 (projIcc 0 U hU u) v 0) = _
  field_simp [hx.choose (projIcc 0 U hU u) v]
  ring

end CauchyHorizon
