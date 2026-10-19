import CauchyHorizon.Reduced.CoordinateRicci
import CauchyHorizon.Reduced.WeakFirstDerivative
import CauchyHorizon.Geometry.MixedRicci
import CauchyHorizon.Analysis.NullWeakDerivative

/-! Both mixed coordinate Ricci components follow from the actual wave equations. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

noncomputable def mixedRicciSource {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  let p := x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  let q := x.2.2 w.1.1 (projIcc 0 V hV w.1.2)
  2 * q 1 * p 1 + Real.exp (z 2) * (e ^ 2 / (2 * z 0 ^ 4) - Λ / 2)

def HasMixedRicciSources {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi →
    Integrable (mixedRicciSource hU hV e Λ x) (rectangleProductMeasure U V A B) ∧
    ∀ i : Fin 2,
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) (i.castAdd 2) (i.rev.castAdd 2) =
        rectangleProductDistribution U V A B (mixedRicciSource hU hV e Λ x)

set_option maxHeartbeats 2000000 in
theorem IsWaveIntegral.mixed_ricci_sources {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasMixedRicciSources hU hV e Λ x := by
  let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let p := fun w : ℝ × ℝ => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let q := fun w : ℝ × ℝ => x.2.2 w.1 (projIcc 0 V hV w.2)
  let t₀ := fun w => q w 2 + 2 * (q w 0 / z w 0)
  let t₁ := fun w => p w 2 + 2 * (p w 0 / z w 0)
  let Q := fun w => -2 * q w 0 * p w 0 / (z w 0) ^ 2
  let S := fun w => 2 * q w 1 * p w 1 + Real.exp (z w 2) * (e ^ 2 / (2 * (z w 0) ^ 4) - Λ / 2)
  let g := fun w => Q w - S w
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hz (i : Fin 3) : Continuous (fun w => z w i) := by fun_prop
  have hp (i : Fin 3) : Continuous (fun w => p w i) := by fun_prop
  have hr (w : ℝ × ℝ) : z w 0 ≠ 0 := hx.choose _ _
  have hi : Continuous (fun w => (z w 0)⁻¹) := (hz 0).inv₀ hr
  have hLp {f : ℝ × ℝ → ℝ} (hf : Continuous f) : MemLp f 2 μ := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
    apply MemLp.of_bound hf.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with w hw
    exact hC w hw
  have hq (i : Fin 3) : MemLp (fun w => q w i) 2 μ := (hx.weak_first_derivatives hzin i).2.2.1
  have ht₁ : Integrable t₁ μ := (hLp ((hp 2).add (((hp 0).div (hz 0) hr).const_mul 2))).integrable (by norm_num)
  have ht₀ : Integrable t₀ μ := by
    have hh := ((hq 2).integrable (by norm_num)).add
      (((hq 0).integrable_mul (hLp hi)).const_mul 2)
    apply hh.congr
    exact Eventually.of_forall fun w => by
      simp only [t₀, div_eq_mul_inv, Pi.add_apply, Pi.mul_apply]
  have hQ : Integrable Q μ := by
    have hh := ((hq 0).integrable_mul (hLp ((hp 0).div ((hz 0).pow 2) (fun w => pow_ne_zero _ (hr w))))).const_mul (-2)
    apply hh.congr
    exact Eventually.of_forall fun w => by
      dsimp only [Q, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
      ring
  have hS : Integrable S μ := by
    have hv : Continuous (fun w => Real.exp (z w 2) * (e ^ 2 / (2 * (z w 0) ^ 4) - Λ / 2)) :=
      (Real.continuous_exp.comp (hz 2)).mul ((continuous_const.div (continuous_const.mul ((hz 0).pow 4))
        (fun w => mul_ne_zero (by norm_num) (pow_ne_zero _ (hr w)))).sub continuous_const)
    have hh := (((hq 1).integrable_mul (hLp (hp 1))).const_mul 2).add
      (hv.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    apply hh.congr
    exact Eventually.of_forall fun w => by
      dsimp only [S, Pi.add_apply, Pi.mul_apply]
      ring
  have hg : Integrable g μ := hQ.sub hS
  have hAC₁ (v : ℝ) : AbsolutelyContinuousOnInterval (fun u => t₁ (u, v)) 0 U := by
    let v' := projIcc 0 V hV v
    let E (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v')
    have hP (i : Fin 3) := absolutelyContinuous_comp_contDiffAt
      (g := E i) hx.velocity_horizontal_absolutelyContinuous (fun _ _ => (E i).contDiff.contDiffAt)
    let G : C(Icc 0 V, WaveVector) → ℝ := fun y => (y v' 0)⁻¹
    have hG : ∀ y ∈ (intervalExtension hU x.1) '' uIcc (0 : ℝ) U, ContDiffAt ℝ 1 G y := by
      rintro _ ⟨u, _hu, rfl⟩
      exact (E 0).contDiff.contDiffAt.inv (hx.choose _ _)
    have hGAC := absolutelyContinuous_comp_contDiffAt (hx.horizontal_absolutelyContinuous hzin) hG
    exact (hP 2).add (((hP 0).mul hGAC).const_mul 2)
  have hd₁ (v : ℝ) : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (fun t => t₁ (t, v)) (g (u, v)) (Icc 0 U) u := by
    filter_upwards [hx.horizontal_derivative hzin, hx.wave_equation,
      ae_restrict_mem measurableSet_Icc] with u hz' hp' hu
    let v' := projIcc 0 V hV v
    let E (i : Fin 3) : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have hP (i : Fin 3) := (E i).hasFDerivAt.comp_hasDerivWithinAt u (hp' v')
    let R : C(Icc 0 V, WaveVector) →L[ℝ] ℝ := (E 0).comp (ContinuousMap.evalCLM ℝ v')
    have hR := R.hasFDerivAt.comp_hasDerivWithinAt u hz'
    have hh := (hP 2).add (((hP 0).div hR (hr (u, v))).const_mul 2)
    apply hh.congr_deriv
    simp only [E, R, Function.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply,
      ContinuousMap.evalCLM_apply, intervalExtension_apply, g, Q, S, z, p, q,
      v', projIcc_of_mem hU hu, waveSource, Matrix.cons_val_zero, Matrix.cons_val,
      radialPotential, conformalPotential]
    field_simp [hx.choose ⟨u, hu⟩ (projIcc 0 V hV v)]
    ring
  have hsecond : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      AbsolutelyContinuousOnInterval (fun v => t₀ (u, v)) 0 V ∧
        ∀ v ∈ Icc 0 V, HasDerivWithinAt (fun t => t₀ (u, t)) (g (u, v)) (Icc 0 V) v := by
    filter_upwards [hx.transverse_identity hx.choose, rectangleSource_ae hU e Λ x hx.choose] with u ht hs
    let u' := projIcc 0 U hU u
    have hd (v : ℝ) (hv : v ∈ Icc 0 V) :
        HasDerivWithinAt (fun t => t₀ (u, t)) (g (u, v)) (Icc 0 V) v := by
      have hq' : HasDerivWithinAt (intervalExtension hV (x.2.2 u))
          (rectangleSource hU e Λ x hx.choose u ⟨v, hv⟩) (Icc 0 V) v := by
        rw [ht, map_add]
        exact (continuousPrimitive_hasDerivWithinAt hV _ hv).const_add (uIn u)
      rw [hs ⟨v, hv⟩] at hq'
      let E (i : Fin 3) : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj i
      have hQ' (i : Fin 3) := (E i).hasFDerivAt.comp_hasDerivWithinAt v hq'
      have hR := (E 0).hasFDerivAt.comp_hasDerivWithinAt v (hx.longitudinal_derivative u' hv)
      have hh := (hQ' 2).add (((hQ' 0).div hR (hr (u, v))).const_mul 2)
      apply hh.congr_deriv
      simp only [E, Function.comp_apply, ContinuousLinearMap.proj_apply, intervalExtension_apply,
        g, Q, S, z, p, q, u', projIcc_of_mem hV hv, waveSource,
        Matrix.cons_val_zero, Matrix.cons_val, radialPotential, conformalPotential]
      field_simp [hx.choose (projIcc 0 U hU u) ⟨v, hv⟩]
      ring
    refine ⟨?_, hd⟩
    let d : C(Icc 0 V, ℝ) := ⟨fun v => g (u, v), by
      have hqv (i : Fin 3) : Continuous (fun v : Icc 0 V => q (u, v) i) := by
        dsimp only [q]
        fun_prop
      have hzv (i : Fin 3) : Continuous (fun v : Icc 0 V => z (u, v) i) :=
        (hz i).comp (continuous_const.prodMk continuous_subtype_val)
      have hpv (i : Fin 3) : Continuous (fun v : Icc 0 V => p (u, v) i) :=
        (hp i).comp (continuous_const.prodMk continuous_subtype_val)
      exact (((continuous_const.mul (hqv 0)).mul (hpv 0)).div ((hzv 0).pow 2)
        (fun v => pow_ne_zero _ (hr (u, v)))).sub
        (((continuous_const.mul (hqv 1)).mul (hpv 1)).add
          ((Real.continuous_exp.comp (hzv 2)).mul
            ((continuous_const.div (continuous_const.mul ((hzv 0).pow 4))
              (fun v => mul_ne_zero (by norm_num) (pow_ne_zero _ (hr (u, v))))).sub continuous_const)))⟩
    have hl : LipschitzOnWith ‖d‖₊ (fun v => t₀ (u, v)) (Icc 0 V) :=
      (convex_Icc (0 : ℝ) V).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hd
        (fun v hv => show ‖d ⟨v, hv⟩‖₊ ≤ ‖d‖₊ from d.norm_coe_le_norm ⟨v, hv⟩)
    have hl' : LipschitzOnWith ‖d‖₊ (fun v => t₀ (u, v)) (uIcc 0 V) := by
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
  have hD := null_derivatives_of_sections (A := A) (B := B) hU hV ht₁ ht₀ hg hg
    (Eventually.of_forall hAC₁) (Eventually.of_forall hd₁) (hsecond.mono fun _ h => h.1)
    (hsecond.mono fun _ h => (ae_restrict_mem measurableSet_Icc).mono fun v hv => h.2 v hv)
  let Γ := coordinateChristoffel hU hV x θ
  let t : Fin 2 → ℝ × ℝ → ℝ := ![t₀, t₁]
  let K := (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)
  have hAe : ∀ᵐ w ∂μ.prod ν, w ∈ K := by
    have he : μ.prod ν = volume.restrict K := by
      simp only [μ, ν, K, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [he]
    exact ae_restrict_mem ((measurableSet_Icc.prod measurableSet_Icc).prod
      (measurableSet_Icc.prod measurableSet_Icc))
  have hn (i : Fin 2) (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) :
      (∀ k, Γ w k (i.castAdd 2) (i.rev.castAdd 2) = 0) ∧
      ricciTrace (Γ w) (i.castAdd 2) = t i w.1 ∧
      ricciQuadratic (Γ w) (i.castAdd 2) (i.rev.castAdd 2) = Q w.1 := by
    have hs : Real.sin (θ + w.2.1) ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hw.2.1.1]) (by linarith [hw.2.1.2]))
    have hm := mixed_connection_contractions (H := Real.exp (z w.1 2))
      (c := Real.cos (θ + w.2.1)) (qr := q w.1 0) (pr := p w.1 0)
      (qell := q w.1 2) (pell := p w.1 2) (hr w.1) hs i
    refine ⟨hm.1, ?_, hm.2⟩
    have ht := (null_connection_contractions (H := Real.exp (z w.1 2))
      (c := Real.cos (θ + w.2.1)) (qr := q w.1 0) (pr := p w.1 0)
      (qell := q w.1 2) (pell := p w.1 2) (Real.exp_ne_zero _) (hr w.1) hs i).2.1
    fin_cases i <;> exact ht
  have hpΓ := (hx.coordinate_ricci hzin A B θ hA hB hθ hθA).1
  have hc := hx.coordinate_connection hzin A B θ hA hB hθ hθA
  have htrace (i : Fin 2) : Integrable (fun w => ricciTrace (Γ w) (i.castAdd 2)) (μ.prod ν) :=
    integrable_finsetSum Finset.univ fun k _ => (hc.1 k (i.castAdd 2) k).integrable (by norm_num)
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
  refine ⟨hS.comp_fst ν, ?_⟩
  intro i
  have hti : Integrable (t i) μ := by fin_cases i <;> assumption
  have he : rectangleProductDistribution U V A B (fun w => ricciTrace (Γ w) (i.castAdd 2)) =
      rectangleProductDistribution U V A B (fun w => t i w.1) := by
    ext ψ
    rw [hpair (htrace i), hpair (hti.comp_fst ν)]
    apply integral_congr_ae
    filter_upwards [hAe] with w hw
    rw [(hn i w hw).2.1]
  have hd : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate (i.rev.castAdd 2))
      (rectangleProductDistribution U V A B (fun w => t i w.1)) =
        rectangleProductDistribution U V A B (fun w => g w.1) := by
    fin_cases i
    · exact hD.2
    · exact hD.1
  have hzero (k : Fin 4) : rectangleProductDistribution U V A B
      (fun w => Γ w k (i.castAdd 2) (i.rev.castAdd 2)) = 0 := by
    ext ψ
    rw [hpair ((hc.1 k (i.castAdd 2) (i.rev.castAdd 2)).integrable (by norm_num))]
    change (∫ w, Γ w k (i.castAdd 2) (i.rev.castAdd 2) * ψ w ∂μ.prod ν) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [hAe] with w hw
    rw [(hn i w hw).1 k, zero_mul]
    rfl
  change ricciDistribution U V A B Γ (i.castAdd 2) (i.rev.castAdd 2) = _
  rw [ricciDistribution]
  simp_rw [hzero, map_zero, Finset.sum_const_zero, zero_sub, he, hd]
  ext ψ
  simp only [add_apply, neg_apply]
  change _ = rectangleProductDistribution U V A B (fun w => S w.1) ψ
  rw [hpair (hg.comp_fst ν), hpair (hpΓ.1 (i.castAdd 2) (i.rev.castAdd 2)), hpair (hS.comp_fst ν),
    ← integral_neg]
  rw [← integral_add (f := fun w => -(g w.1 * ψ w))
    (g := fun w => ricciQuadratic (Γ w) (i.castAdd 2) (i.rev.castAdd 2) * ψ w)
    (htest (hg.comp_fst ν) ψ).neg (htest (hpΓ.1 (i.castAdd 2) (i.rev.castAdd 2)) ψ)]
  apply integral_congr_ae
  filter_upwards [hAe] with w hw
  rw [(hn i w hw).2.2]
  change -((Q w.1 - S w.1) * ψ w) + Q w.1 * ψ w = S w.1 * ψ w
  ring

end CauchyHorizon
