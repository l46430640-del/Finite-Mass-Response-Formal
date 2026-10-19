import CauchyHorizon.Reduced.WeakFirstDerivative
import CauchyHorizon.Analysis.NullWeakDerivative

/-! The two radial contributions to angular Ricci have actual L1 weak derivatives. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

noncomputable def angularNullFlux {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (i : Fin 2) (w : ℝ × ℝ) : ℝ :=
  let z := x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let p := x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let q := x.2.2 w.1 (projIcc 0 V hV w.2)
  ![2 * z 0 * p 0 / Real.exp (z 2), 2 * z 0 * q 0 / Real.exp (z 2)] i

noncomputable def angularNullSource {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (i : Fin 2) (w : ℝ × ℝ) : ℝ :=
  let z := x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let p := x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let q := x.2.2 w.1 (projIcc 0 V hV w.2)
  (-1 + e ^ 2 / (z 0) ^ 2 + Λ * (z 0) ^ 2) / 2 -
    ![2 * z 0 * p 0 * q 2 / Real.exp (z 2), 2 * z 0 * q 0 * p 2 / Real.exp (z 2)] i

set_option maxHeartbeats 2000000 in
theorem IsWaveIntegral.angular_radial_derivatives {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    (∀ i, IntegrableOn (angularNullFlux hU hV x i) (Icc 0 U ×ˢ Icc 0 V) ∧
      IntegrableOn (angularNullSource hU hV e Λ x i) (Icc 0 U ×ˢ Icc 0 V)) ∧
    ∀ (A B : ℝ) (b : ℝ × ℝ → ℝ), IntegrableOn b (Icc 0 A ×ˢ Icc 0 B) →
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((1, 0), (0, 0))
        (rectangleProductDistribution U V A B (fun w => angularNullFlux hU hV x 0 w.1 * b w.2)) =
          rectangleProductDistribution U V A B (fun w => angularNullSource hU hV e Λ x 0 w.1 * b w.2) ∧
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 1), (0, 0))
        (rectangleProductDistribution U V A B (fun w => angularNullFlux hU hV x 1 w.1 * b w.2)) =
          rectangleProductDistribution U V A B (fun w => angularNullSource hU hV e Λ x 1 w.1 * b w.2) := by
  let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let p := fun w : ℝ × ℝ => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
  let q := fun w : ℝ × ℝ => x.2.2 w.1 (projIcc 0 V hV w.2)
  let C := fun w => (-1 + e ^ 2 / (z w 0) ^ 2 + Λ * (z w 0) ^ 2) / 2
  let f₀ := fun w => 2 * z w 0 * p w 0 / Real.exp (z w 2)
  let f₁ := fun w => 2 * z w 0 * q w 0 / Real.exp (z w 2)
  let g₀ := fun w => C w - 2 * z w 0 * p w 0 * q w 2 / Real.exp (z w 2)
  let g₁ := fun w => C w - 2 * z w 0 * q w 0 * p w 2 / Real.exp (z w 2)
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hz (i : Fin 3) : Continuous (fun w => z w i) := by fun_prop
  have hp (i : Fin 3) : Continuous (fun w => p w i) := by fun_prop
  have hr (w : ℝ × ℝ) : z w 0 ≠ 0 := hx.choose _ _
  have hH : Continuous (fun w => Real.exp (z w 2)) := Real.continuous_exp.comp (hz 2)
  have hC : Continuous C := ((continuous_const.add
    (continuous_const.div ((hz 0).pow 2) (fun w => pow_ne_zero _ (hr w)))).add
      (continuous_const.mul ((hz 0).pow 2))).div_const 2
  have hLp {f : ℝ × ℝ → ℝ} (hf : Continuous f) : MemLp f 2 μ := by
    obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
    apply MemLp.of_bound hf.aestronglyMeasurable K
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with w hw
    exact hK w hw
  have hq (i : Fin 3) : MemLp (fun w => q w i) 2 μ := (hx.weak_first_derivatives hzin i).2.2.1
  have hf₀ : Continuous f₀ := ((continuous_const.mul (hz 0)).mul (hp 0)).div hH (fun _ => Real.exp_ne_zero _)
  have hF₀ : Integrable f₀ μ := (hLp hf₀).integrable (by norm_num)
  have hF₁ : Integrable f₁ μ := by
    have hh := (hq 0).integrable_mul (hLp (((continuous_const (y := (2 : ℝ))).mul (hz 0)).div hH (fun _ => Real.exp_ne_zero _)))
    apply hh.congr
    exact Eventually.of_forall fun w => by dsimp only [f₁, Pi.mul_apply, Pi.div_apply]; ring
  have hG₀ : Integrable g₀ μ := by
    have hh := ((hLp hC).integrable (by norm_num)).sub ((hq 2).integrable_mul (hLp hf₀))
    apply hh.congr
    exact Eventually.of_forall fun w => by dsimp only [g₀, f₀, Pi.mul_apply, Pi.sub_apply]; ring
  have hG₁ : Integrable g₁ μ := by
    have hh := ((hLp hC).integrable (by norm_num)).sub ((hq 0).integrable_mul
      (hLp ((((continuous_const (y := (2 : ℝ))).mul (hz 0)).mul (hp 2)).div hH (fun _ => Real.exp_ne_zero _))))
    apply hh.congr
    exact Eventually.of_forall fun w => by dsimp only [g₁, Pi.mul_apply, Pi.div_apply, Pi.sub_apply]; ring
  have hAC₀ (v : ℝ) : AbsolutelyContinuousOnInterval (fun u => f₀ (u, v)) 0 U := by
    let v' := projIcc 0 V hV v
    let E (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v')
    have hP := absolutelyContinuous_comp_contDiffAt (g := E 0)
      hx.velocity_horizontal_absolutelyContinuous (fun _ _ => (E 0).contDiff.contDiffAt)
    let G : C(Icc 0 V, WaveVector) → ℝ := fun y => 2 * y v' 0 / Real.exp (y v' 2)
    have hG : ∀ y ∈ (intervalExtension hU x.1) '' uIcc (0 : ℝ) U, ContDiffAt ℝ 1 G y := by
      intro y _hy
      exact (contDiffAt_const.mul (E 0).contDiff.contDiffAt).div
        (Real.contDiff_exp.contDiffAt.comp _ (E 2).contDiff.contDiffAt) (Real.exp_ne_zero _)
    have hh := (absolutelyContinuous_comp_contDiffAt (hx.horizontal_absolutelyContinuous hzin) hG).mul hP
    have he : (fun u => G (intervalExtension hU x.1 u) * E 0 (intervalExtension hU x.2.1 u)) =
        fun u => f₀ (u, v) := by
      funext u
      simp only [G, E, f₀, z, p, v', intervalExtension_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousMap.evalCLM_apply]
      ring
    exact he ▸ hh
  have hd₀ (v : ℝ) : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (fun t => f₀ (t, v)) (g₀ (u, v)) (Icc 0 U) u := by
    filter_upwards [hx.horizontal_derivative hzin, hx.wave_equation,
      ae_restrict_mem measurableSet_Icc] with u hz' hp' hu
    let v' := projIcc 0 V hV v
    let E (i : Fin 3) : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj i
    let R (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ := (E i).comp (ContinuousMap.evalCLM ℝ v')
    have hZ (i : Fin 3) := (R i).hasFDerivAt.comp_hasDerivWithinAt u hz'
    have hP := (E 0).hasFDerivAt.comp_hasDerivWithinAt u (hp' v')
    have hExp := (Real.hasDerivAt_exp _).comp_hasDerivWithinAt u (hZ 2)
    have hh := (((hZ 0).const_mul 2).mul hP).div hExp (Real.exp_ne_zero _)
    apply hh.congr_deriv
    simp only [E, R, Function.comp_apply, Pi.mul_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply,
      ContinuousMap.evalCLM_apply, intervalExtension_apply, g₀, C, z, p, q, v', projIcc_of_mem hU hu,
      waveSource, Matrix.cons_val_zero, radialPotential]
    field_simp [hx.choose ⟨u, hu⟩ (projIcc 0 V hV v), Real.exp_ne_zero]
    ring
  have hsecond : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      AbsolutelyContinuousOnInterval (fun v => f₁ (u, v)) 0 V ∧
        ∀ v ∈ Icc 0 V, HasDerivWithinAt (fun t => f₁ (u, t)) (g₁ (u, v)) (Icc 0 V) v := by
    filter_upwards [hx.transverse_identity hx.choose, rectangleSource_ae hU e Λ x hx.choose] with u ht hs
    let u' := projIcc 0 U hU u
    have hd (v : ℝ) (hv : v ∈ Icc 0 V) :
        HasDerivWithinAt (fun t => f₁ (u, t)) (g₁ (u, v)) (Icc 0 V) v := by
      have hq' : HasDerivWithinAt (intervalExtension hV (x.2.2 u))
          (rectangleSource hU e Λ x hx.choose u ⟨v, hv⟩) (Icc 0 V) v := by
        rw [ht, map_add]
        exact (continuousPrimitive_hasDerivWithinAt hV _ hv).const_add (uIn u)
      rw [hs ⟨v, hv⟩] at hq'
      let E (i : Fin 3) : WaveVector →L[ℝ] ℝ := ContinuousLinearMap.proj i
      have hQ' := (E 0).hasFDerivAt.comp_hasDerivWithinAt v hq'
      have hZ (i : Fin 3) := (E i).hasFDerivAt.comp_hasDerivWithinAt v (hx.longitudinal_derivative u' hv)
      have hExp := (Real.hasDerivAt_exp _).comp_hasDerivWithinAt v (hZ 2)
      have hh := (((hZ 0).const_mul 2).mul hQ').div hExp (Real.exp_ne_zero _)
      apply hh.congr_deriv
      simp only [E, Function.comp_apply, Pi.mul_apply, ContinuousLinearMap.proj_apply, intervalExtension_apply,
        g₁, C, z, p, q, u', projIcc_of_mem hV hv, waveSource, Matrix.cons_val_zero, radialPotential]
      field_simp [hx.choose (projIcc 0 U hU u) ⟨v, hv⟩, Real.exp_ne_zero]
      ring
    refine ⟨?_, hd⟩
    let d : C(Icc 0 V, ℝ) := ⟨fun v => g₁ (u, v), by
      have hqv : Continuous (fun v : Icc 0 V => q (u, v) 0) := by dsimp only [q]; fun_prop
      have hzv (i : Fin 3) : Continuous (fun v : Icc 0 V => z (u, v) i) :=
        (hz i).comp (continuous_const.prodMk continuous_subtype_val)
      have hpv : Continuous (fun v : Icc 0 V => p (u, v) 2) :=
        (hp 2).comp (continuous_const.prodMk continuous_subtype_val)
      exact (hC.comp (continuous_const.prodMk continuous_subtype_val)).sub
        ((((continuous_const.mul (hzv 0)).mul hqv).mul hpv).div
          (Real.continuous_exp.comp (hzv 2)) (fun _ => Real.exp_ne_zero _))⟩
    have hl : LipschitzOnWith ‖d‖₊ (fun v => f₁ (u, v)) (Icc 0 V) :=
      (convex_Icc (0 : ℝ) V).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hd
        (fun v hv => show ‖d ⟨v, hv⟩‖₊ ≤ ‖d‖₊ from d.norm_coe_le_norm ⟨v, hv⟩)
    have hl' : LipschitzOnWith ‖d‖₊ (fun v => f₁ (u, v)) (uIcc 0 V) := by
      simpa only [uIcc_of_le hV] using hl
    exact hl'.absolutelyContinuousOnInterval
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hF₀, hG₀⟩
    · exact ⟨hF₁, hG₁⟩
  · intro A B b hb
    exact null_weighted_derivatives_of_sections hU hV hF₀ hF₁ hG₀ hG₁
      (Eventually.of_forall hAC₀) (Eventually.of_forall hd₀) (hsecond.mono fun _ h => h.1)
      (hsecond.mono fun _ h => (ae_restrict_mem measurableSet_Icc).mono fun v hv => h.2 v hv) b hb

end CauchyHorizon
