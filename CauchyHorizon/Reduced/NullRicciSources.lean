import CauchyHorizon.Reduced.CoordinateRicci
import CauchyHorizon.Reduced.GeneralRadialConstraint
import CauchyHorizon.Reduced.LongitudinalConstraint
import CauchyHorizon.Reduced.WeakFirstDerivative
import CauchyHorizon.Analysis.NullWeakDerivative

/-! The propagated radial constraints identify both null Ricci distributions with scalar energy. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

noncomputable def nullScalarDerivative {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (i : Fin 2) (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  ![x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 1,
    x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 1] i

def HasNullRicciSources {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi → ∀ i : Fin 2,
    Integrable (fun w => 2 * (nullScalarDerivative hU hV x i w) ^ 2)
      (rectangleProductMeasure U V A B) ∧
    ricciDistribution U V A B (coordinateChristoffel hU hV x θ) (i.castAdd 2) (i.castAdd 2) =
      rectangleProductDistribution U V A B (fun w => 2 * (nullScalarDerivative hU hV x i w) ^ 2)

set_option maxHeartbeats 2000000 in
theorem IsWaveIntegral.null_ricci_sources {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (n : C(Icc 0 U, ℝ))
    (hn : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = n (projIcc 0 U hU u))
    (hnAC : AbsolutelyContinuousOnInterval (intervalExtension hU n) 0 U)
    (hnd : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (intervalExtension hU n)
        (uIn u 2 * n (projIcc 0 U hU u) - zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2) (Icc 0 U) u)
    (hout : ∀ v (hv : v ∈ Icc 0 V),
      HasDerivWithinAt (fun t => intervalExtension hV vOut t 0)
        (vOut ⟨v, hv⟩ 2 * vOut ⟨v, hv⟩ 0 -
          x.1 ⟨0, le_rfl, hU⟩ ⟨v, hv⟩ 0 * (vOut ⟨v, hv⟩ 1) ^ 2) (Icc 0 V) v) :
    HasNullRicciSources hU hV x := by
  let N := radialVelocityField hV e Λ n zIn x.1 hx.choose
  obtain ⟨hNae, hNr, hNd⟩ := hx.general_radial_constraint hx.choose hzin n hn hnd
  let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let p := fun w : ℝ × ℝ => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let q := fun w : ℝ × ℝ => x.2.2 w.1 (projIcc 0 V hV w.2)
  let a₁ := fun w : ℝ × ℝ => N (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) / z w 0
  let a₂ := fun w : ℝ × ℝ => p w 0 / z w 0
  let g₁ := fun w => q w 2 * a₁ w - (q w 1) ^ 2 - (a₁ w) ^ 2
  let g₂ := fun w => p w 2 * a₂ w - (p w 1) ^ 2 - (a₂ w) ^ 2
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hz (i : Fin 3) : Continuous (fun w => z w i) := by fun_prop
  have hp (i : Fin 3) : Continuous (fun w => p w i) := by fun_prop
  have hr (w : ℝ × ℝ) : z w 0 ≠ 0 := hx.choose _ _
  have ha₁ : Continuous a₁ := (by fun_prop : Continuous
    (fun w : ℝ × ℝ => N (projIcc 0 U hU w.1) (projIcc 0 V hV w.2))).div (hz 0) hr
  have ha₂ : Continuous a₂ := (hp 0).div (hz 0) hr
  have hLp {f : ℝ × ℝ → ℝ} (hf : Continuous f) : MemLp f 2 μ := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
    apply MemLp.of_bound hf.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with w hw
    exact hC w hw
  have hq (i : Fin 3) : MemLp (fun w => q w i) 2 μ := (hx.weak_first_derivatives hzin i).2.2.1
  have hg₁ : Integrable g₁ μ :=
    (((hq 2).integrable_mul (hLp ha₁)).sub ((memLp_two_iff_integrable_sq (hq 1).1).1 (hq 1))).sub
      ((memLp_two_iff_integrable_sq (hLp ha₁).1).1 (hLp ha₁))
  have hg₂ : Integrable g₂ μ :=
    (((hLp (hp 2)).integrable_mul (hLp ha₂)).sub
      ((memLp_two_iff_integrable_sq (hLp (hp 1)).1).1 (hLp (hp 1)))).sub
        ((memLp_two_iff_integrable_sq (hLp ha₂).1).1 (hLp ha₂))
  have hAC₁ (v : ℝ) : AbsolutelyContinuousOnInterval (fun u => a₁ (u, v)) 0 U := by
    let v' := projIcc 0 V hV v
    have hW := (hx.general_radial_constraint_integral hx.choose hzin n hn hnAC hnd v').1
    let G : C(Icc 0 V, WaveVector) → ℝ := fun z => Real.exp (z v' 2) / z v' 0
    have hG : ∀ y ∈ (intervalExtension hU x.1) '' uIcc (0 : ℝ) U, ContDiffAt ℝ 1 G y := by
      rintro _ ⟨u, _hu, rfl⟩
      let E (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
        (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v')
      exact (Real.contDiff_exp.contDiffAt.comp _ (E 2).contDiff.contDiffAt).div
        (E 0).contDiff.contDiffAt (hx.choose _ _)
    have hGAC := absolutelyContinuous_comp_contDiffAt (hx.horizontal_absolutelyContinuous hzin) hG
    have hh := hW.mul hGAC
    have he : (fun u => (intervalExtension hU N u v' * Real.exp (-intervalExtension hU x.1 u v' 2)) *
        G (intervalExtension hU x.1 u)) = fun u => a₁ (u, v) := by
      funext u
      change (N (projIcc 0 U hU u) v' * Real.exp (-z (u, v) 2)) *
        (Real.exp (z (u, v) 2) / z (u, v) 0) = N (projIcc 0 U hU u) v' / z (u, v) 0
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero, hr]
    exact he ▸ hh
  have hd₁ (v : ℝ) : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (fun t => a₁ (t, v)) (g₁ (u, v)) (Icc 0 U) u := by
    filter_upwards [hNd, ae_restrict_mem measurableSet_Icc] with u hd hu
    let v' := projIcc 0 V hV v
    have hh := (hd v').div (hNr ⟨u, hu⟩ v') (hr (u, v))
    apply hh.congr_deriv
    dsimp only [g₁, a₁, z, q, v', intervalExtension_apply]
    rw [projIcc_of_mem hU hu]
    field_simp [hx.choose ⟨u, hu⟩ (projIcc 0 V hV v)]
    ring
  have hd₂ (u : ℝ) (v : ℝ) (hv : v ∈ Icc 0 V) :
      HasDerivWithinAt (fun t => a₂ (u, t)) (g₂ (u, v)) (Icc 0 V) v := by
    let u' := projIcc 0 U hU u
    have hp' := hx.longitudinal_constraint hx.choose hzin hv (hout v hv) u'
    have hr' := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt v
      (hx.longitudinal_derivative u' hv)
    have hh := hp'.div hr' (hr (u, v))
    apply hh.congr_deriv
    simp only [intervalExtension_apply, projIcc_of_mem hV hv, Function.comp_apply,
      ContinuousLinearMap.proj_apply]
    dsimp only [g₂, a₂, z, p, u']
    rw [projIcc_of_mem hV hv]
    field_simp [hx.choose (projIcc 0 U hU u) ⟨v, hv⟩]
  have hAC₂ (u : ℝ) : AbsolutelyContinuousOnInterval (fun v => a₂ (u, v)) 0 V := by
    let d : C(Icc 0 V, ℝ) := ⟨fun v => g₂ (u, v), by
      dsimp only [g₂]
      fun_prop⟩
    have hl : LipschitzOnWith ‖d‖₊ (fun v => a₂ (u, v)) (Icc 0 V) :=
      (convex_Icc (0 : ℝ) V).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (hd₂ u)
        (fun v hv => show ‖d ⟨v, hv⟩‖₊ ≤ ‖d‖₊ from d.norm_coe_le_norm ⟨v, hv⟩)
    have hl' : LipschitzOnWith ‖d‖₊ (fun v => a₂ (u, v)) (uIcc 0 V) := by
      simpa only [uIcc_of_le hV] using hl
    exact hl'.absolutelyContinuousOnInterval
  intro A B θ hA hB hθ hθA
  let ν := volume.restrict (Icc 0 A ×ˢ Icc 0 B)
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let : IsFiniteMeasure (rectangleProductMeasure U V A B) :=
    show IsFiniteMeasure (μ.prod ν) from inferInstance
  have hD := null_derivatives_of_sections (A := A) (B := B) hU hV
    ((hLp ha₁).integrable (by norm_num)) ((hLp ha₂).integrable (by norm_num)) hg₁ hg₂
    (Eventually.of_forall hAC₁) (Eventually.of_forall hd₁) (Eventually.of_forall hAC₂)
    (Eventually.of_forall fun u => (ae_restrict_mem measurableSet_Icc).mono fun v hv => hd₂ u v hv)
  let a : Fin 2 → ℝ × ℝ → ℝ := ![a₁, a₂]
  let g : Fin 2 → ℝ × ℝ → ℝ := ![g₁, g₂]
  let s : Fin 2 → ℝ × ℝ → ℝ := ![fun w => q w 1, fun w => p w 1]
  have hgi (i : Fin 2) : Integrable (g i) μ := by fin_cases i <;> assumption
  have hai (i : Fin 2) : Integrable (a i) μ := by
    fin_cases i
    · exact (hLp ha₁).integrable (by norm_num)
    · exact (hLp ha₂).integrable (by norm_num)
  have hsi (i : Fin 2) : Integrable (fun w => 2 * (s i w) ^ 2) μ := by
    fin_cases i
    · exact ((memLp_two_iff_integrable_sq (hq 1).1).1 (hq 1)).const_mul 2
    · exact ((memLp_two_iff_integrable_sq (hLp (hp 1)).1).1 (hLp (hp 1))).const_mul 2
  have hAE : ∀ᵐ w ∂μ, q w 0 = N (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) := by
    dsimp only [μ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hNae] with w hw
    exact hw (projIcc 0 V hV w.2)
  have hAE4 : ∀ᵐ w ∂μ.prod ν, q w.1 0 = N (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) :=
    Measure.quasiMeasurePreserving_fst.ae hAE
  have hpair {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B f ψ = ∫ w, f w * ψ w ∂(μ.prod ν) := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) (μ.prod ν) f ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have htest {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) : Integrable (fun w => f w * ψ w) (μ.prod ν) := by
    obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
    exact hf.mul_bdd ψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  intro i
  have hc := (hx.coordinate_ricci hzin A B θ hA hB hθ hθA).2 i
  have hsource : Integrable (fun w => 2 * (nullScalarDerivative hU hV x i w) ^ 2) (μ.prod ν) := by
    fin_cases i
    · exact (hsi 0).comp_fst ν
    · exact (hsi 1).comp_fst ν
  refine ⟨hsource, ?_⟩
  have har : (fun w => nullRadialRatio hU hV x i w) =ᵐ[μ.prod ν] fun w => a i w.1 := by
    filter_upwards [hAE4] with w hw
    fin_cases i
    · change q w.1 0 / z w.1 0 = N (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) / z w.1 0
      rw [hw]
    · rfl
  have he : rectangleProductDistribution U V A B (nullRadialRatio hU hV x i) =
      rectangleProductDistribution U V A B (fun w => a i w.1) := by
    ext ψ
    rw [hpair (hc.1.integrable (by norm_num)), hpair ((hai i).comp_fst ν)]
    exact integral_congr_ae (har.mul (EventuallyEq.rfl))
  have hd : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate (i.castAdd 2))
      (rectangleProductDistribution U V A B (fun w => a i w.1)) =
        rectangleProductDistribution U V A B (fun w => g i w.1) := by
    fin_cases i
    · exact hD.1
    · exact hD.2
  rw [hc.2.2, he, hd]
  ext ψ
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hpair ((hgi i).comp_fst ν), hpair hc.2.1, hpair hsource,
    ← integral_const_mul, ← integral_add ((htest ((hgi i).comp_fst ν) ψ).const_mul (-2)) (htest hc.2.1 ψ)]
  apply integral_congr_ae
  filter_upwards [har] with w hw
  rw [hw]
  fin_cases i
  · change -2 * ((q w.1 2 * a₁ w.1 - (q w.1 1) ^ 2 - (a₁ w.1) ^ 2) * ψ w) +
      (2 * q w.1 2 * a₁ w.1 - 2 * (a₁ w.1) ^ 2) * ψ w = 2 * (q w.1 1) ^ 2 * ψ w
    ring
  · change -2 * ((p w.1 2 * a₂ w.1 - (p w.1 1) ^ 2 - (a₂ w.1) ^ 2) * ψ w) +
      (2 * p w.1 2 * a₂ w.1 - 2 * (a₂ w.1) ^ 2) * ψ w = 2 * (p w.1 1) ^ 2 * ψ w
    ring

end CauchyHorizon
