import CauchyHorizon.Reduced.AngularFlux
import CauchyHorizon.Reduced.CoordinateRicci
import CauchyHorizon.Geometry.AngularRicci

/-! Angular coordinate Ricci includes the intrinsic unit-sphere curvature. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

noncomputable def angularRicciSource {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (e Λ : ℝ) (x : WaveState U V) (θ : ℝ) (i : Fin 2)
    (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  let r := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0
  (e ^ 2 / r ^ 2 + Λ * r ^ 2) * ![1, Real.sin (θ + w.2.1) ^ 2] i

def HasAngularRicciSources {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi → ∀ i : Fin 2,
    Integrable (angularRicciSource hU hV e Λ x θ i) (rectangleProductMeasure U V A B) ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) (i.natAdd 2) (i.natAdd 2) =
        rectangleProductDistribution U V A B (angularRicciSource hU hV e Λ x θ i)

set_option maxHeartbeats 3000000 in
theorem IsWaveIntegral.angular_ricci_sources {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c₀ : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c₀ + horizontalPrimitive hU uIn) :
    HasAngularRicciSources hU hV e Λ x := by
  intro A B θ hA hB hθ hθA
  let μ := volume.restrict (Icc 0 U ×ˢ Icc 0 V)
  let ν := volume.restrict (Icc 0 A ×ˢ Icc 0 B)
  let K := (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  let : IsFiniteMeasure (rectangleProductMeasure U V A B) :=
    show IsFiniteMeasure (μ.prod ν) from inferInstance
  let s := fun y : ℝ × ℝ => Real.sin (θ + (projIcc 0 A hA y.1 : ℝ))
  let c := fun y : ℝ × ℝ => Real.cos (θ + (projIcc 0 A hA y.1 : ℝ))
  have hs : Continuous s := by fun_prop
  have hc : Continuous c := by fun_prop
  have hs0 (y : ℝ × ℝ) : s y ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [(projIcc 0 A hA y.1).property.1])
    (by linarith [(projIcc 0 A hA y.1).property.2]))
  let a : Fin 2 → ℝ × ℝ → ℝ := fun i y => ![c y / s y, -s y * c y] i
  let da : Fin 2 → ℝ × ℝ → ℝ := fun i y => ![-1 / s y ^ 2, s y ^ 2 - c y ^ 2] i
  let b : Fin 2 → ℝ × ℝ → ℝ := fun i y => ![1, s y ^ 2] i
  have ha (i : Fin 2) : Continuous (a i) := by
    fin_cases i
    · exact hc.div hs hs0
    · exact hs.neg.mul hc
  have hda (i : Fin 2) : Continuous (da i) := by
    fin_cases i
    · exact continuous_const.div (hs.pow 2) (fun y => pow_ne_zero _ (hs0 y))
    · exact (hs.pow 2).sub (hc.pow 2)
  have hb (i : Fin 2) : Continuous (b i) := by fin_cases i; exact continuous_const; exact hs.pow 2
  have hLp {P Q : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
      MemLp f 2 (volume.restrict (Icc 0 P ×ˢ Icc 0 Q)) := by
    let : IsFiniteMeasure (volume.restrict (Icc 0 P ×ˢ Icc 0 Q)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      infer_instance
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
    apply MemLp.of_bound hf.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with w hw
    exact hC w hw
  have hangle (i : Fin 2) : HasL2FirstDerivatives A B (a i) (da i) (fun _ => 0) := by
    have hd (v u : ℝ) (hu : u ∈ Icc 0 A) :
        HasDerivWithinAt (fun t => a i (t, v)) (da i (u, v)) (Icc 0 A) u := by
      have harg := (hasDerivAt_id u).const_add θ
      have hn : Real.sin (θ + u) ≠ 0 := by simpa only [s, projIcc_of_mem hA hu] using hs0 (u, v)
      have he := Real.sin_sq_add_cos_sq (θ + u)
      fin_cases i
      · have hh := (harg.cos.div harg.sin hn).hasDerivWithinAt (s := Icc 0 A)
        have hh' := hh.congr_of_mem (f₁ := fun t => a 0 (t, v)) (fun t ht => by simp only [a, Matrix.cons_val_zero, c, s,
          projIcc_of_mem hA ht, Pi.div_apply, id_eq]) hu
        apply hh'.congr_deriv
        change ((-Real.sin (θ + u) * 1 * Real.sin (θ + u) - Real.cos (θ + u) *
          (Real.cos (θ + u) * 1)) / Real.sin (θ + u) ^ 2) = -1 / s (u, v) ^ 2
        simp only [s, projIcc_of_mem hA hu]
        field_simp
        nlinarith
      · have hh := (harg.sin.neg.mul harg.cos).hasDerivWithinAt (s := Icc 0 A)
        have hh' := hh.congr_of_mem (f₁ := fun t => a 1 (t, v)) (fun t ht => by simp only [a, Matrix.cons_val_one, Matrix.cons_val_zero,
          c, s, projIcc_of_mem hA ht, Pi.mul_apply, Pi.neg_apply, id_eq]) hu
        apply hh'.congr_deriv
        change -(Real.cos (θ + u) * 1) * Real.cos (θ + u) +
          -Real.sin (θ + u) * (-Real.sin (θ + u) * 1) = s (u, v) ^ 2 - c (u, v) ^ 2
        simp only [s, c, projIcc_of_mem hA hu]
        ring
    refine l2_first_derivatives_of_sections hA hB (hLp (ha i)) (hLp (hda i))
      (hLp continuous_const) ?_ ?_ ?_ ?_
    · intro v
      let d : C(Icc 0 A, ℝ) := ⟨fun u => da i (u, v), (hda i).comp
        (continuous_subtype_val.prodMk continuous_const)⟩
      have hl := (convex_Icc (0 : ℝ) A).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (hd v)
        (fun u hu => show ‖d ⟨u, hu⟩‖₊ ≤ ‖d‖₊ from d.norm_coe_le_norm ⟨u, hu⟩)
      have hl' : LipschitzOnWith ‖d‖₊ (fun u => a i (u, v)) (uIcc 0 A) := by
        simpa only [uIcc_of_le hA] using hl
      exact hl'.absolutelyContinuousOnInterval
    · intro v
      exact (ae_restrict_mem measurableSet_Icc).mono fun u hu => hd v u hu
    · intro u
      fin_cases i
      · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c (u, 0) / s (u, 0))).contDiffOn.absolutelyContinuousOnInterval
      · exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => -s (u, 0) * c (u, 0))).contDiffOn.absolutelyContinuousOnInterval
    · intro u
      fin_cases i
      · exact Eventually.of_forall fun v => hasDerivWithinAt_const v _ (c (u, 0) / s (u, 0))
      · exact Eventually.of_forall fun v => hasDerivWithinAt_const v _ (-s (u, 0) * c (u, 0))
  have hconst : HasL2FirstDerivatives U V (fun _ => (1 : ℝ)) (fun _ => 0) (fun _ => 0) := by
    refine l2_first_derivatives_of_sections hU hV (hLp continuous_const) (hLp continuous_const)
      (hLp continuous_const) ?_ ?_ ?_ ?_
    · exact fun _ => (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))).contDiffOn.absolutelyContinuousOnInterval
    · exact fun _ => Eventually.of_forall fun u => hasDerivWithinAt_const u _ _
    · exact fun _ => (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))).contDiffOn.absolutelyContinuousOnInterval
    · exact fun _ => Eventually.of_forall fun v => hasDerivWithinAt_const v _ _
  have hAD (i : Fin 2) : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 2)
      (rectangleProductDistribution U V A B (fun w => a i w.2)) =
        rectangleProductDistribution U V A B (fun w => da i w.2) := by
    have hh : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 2)
        (rectangleProductDistribution U V A B (fun w => 1 * a i w.2)) =
          rectangleProductDistribution U V A B (fun w => 1 * da i w.2) :=
      ((l2_product_derivatives hconst (hangle i)).2 2).2
    simpa only [one_mul] using hh
  let F := angularNullFlux hU hV x
  let G := angularNullSource hU hV e Λ x
  have hR := hx.angular_radial_derivatives hzin
  let Γ := coordinateChristoffel hU hV x θ
  let f : Fin 2 → Fin 4 → (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun i k w =>
    ![F 0 w.1 * b i w.2, F 1 w.1 * b i w.2, ![0, a 1 w.2] i, 0] k
  let d : Fin 2 → Fin 4 → (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun i k w =>
    ![G 0 w.1 * b i w.2, G 1 w.1 * b i w.2, ![0, da 1 w.2] i, 0] k
  let t : Fin 2 → (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun i w => ![a 0 w.2, 0] i
  let dt : Fin 2 → (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun i w => ![da 0 w.2, 0] i
  have hfi (i : Fin 2) (k : Fin 4) : Integrable (f i k) (μ.prod ν) := by
    fin_cases k
    · exact (hR.1 0).1.mul_prod ((hLp (hb i)).integrable (by norm_num))
    · exact (hR.1 1).1.mul_prod ((hLp (hb i)).integrable (by norm_num))
    · fin_cases i
      · exact integrable_const 0
      · exact ((hLp (ha 1)).integrable (by norm_num)).comp_snd μ
    · exact integrable_const 0
  have hdi (i : Fin 2) (k : Fin 4) : Integrable (d i k) (μ.prod ν) := by
    fin_cases k
    · exact (hR.1 0).2.mul_prod ((hLp (hb i)).integrable (by norm_num))
    · exact (hR.1 1).2.mul_prod ((hLp (hb i)).integrable (by norm_num))
    · fin_cases i
      · exact integrable_const 0
      · exact ((hLp (hda 1)).integrable (by norm_num)).comp_snd μ
    · exact integrable_const 0
  have hti (i : Fin 2) : Integrable (t i) (μ.prod ν) := by
    fin_cases i
    · exact ((hLp (ha 0)).integrable (by norm_num)).comp_snd μ
    · exact integrable_const 0
  have hdti (i : Fin 2) : Integrable (dt i) (μ.prod ν) := by
    fin_cases i
    · exact ((hLp (hda 0)).integrable (by norm_num)).comp_snd μ
    · exact integrable_const 0
  have hAe : ∀ᵐ w ∂μ.prod ν, w ∈ K := by
    have he : μ.prod ν = volume.restrict K := by
      simp only [μ, ν, K, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [he]
    exact ae_restrict_mem ((measurableSet_Icc.prod measurableSet_Icc).prod
      (measurableSet_Icc.prod measurableSet_Icc))
  have hgeom (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) :=
    angular_connection_contractions (H := Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2))
      (c := Real.cos (θ + w.2.1))
      (qr := x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 0)
      (pr := x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0)
      (qell := x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 2)
      (pell := x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2)
      (Real.exp_ne_zero _) (hx.choose (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)) (show Real.sin (θ + w.2.1) ≠ 0 from
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hw.2.1.1]) (by linarith [hw.2.1.2])))
  have hconn := hx.coordinate_connection hzin A B θ hA hB hθ hθA
  have hQ := (hx.coordinate_ricci hzin A B θ hA hB hθ hθA).1.1
  have hpair {v : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hv : Integrable v (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B v ψ = ∫ w, v w * ψ w ∂(μ.prod ν) := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) (μ.prod ν) v ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hv.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hcongr {v v' : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hv : Integrable v (μ.prod ν))
      (hv' : Integrable v' (μ.prod ν)) (he : v =ᵐ[μ.prod ν] v') :
      rectangleProductDistribution U V A B v = rectangleProductDistribution U V A B v' := by
    ext ψ
    rw [hpair hv, hpair hv']
    exact integral_congr_ae (he.mono fun _ h => congrArg (· * _) h)
  have hzero : rectangleProductDistribution U V A B (fun _ => 0) = 0 := by
    ext ψ
    rw [hpair (integrable_const 0)]
    simp only [zero_mul, integral_zero, zero_apply]
  have hΓ (i : Fin 2) (k : Fin 4) : rectangleProductDistribution U V A B
      (fun w => Γ w k (i.natAdd 2) (i.natAdd 2)) = rectangleProductDistribution U V A B (f i k) := by
    apply hcongr ((hconn.1 k (i.natAdd 2) (i.natAdd 2)).integrable (by norm_num)) (hfi i k)
    filter_upwards [hAe] with w hw
    have hh := hgeom w hw
    fin_cases i <;> fin_cases k <;>
      dsimp [f, F, angularNullFlux, b, a, s, c] <;>
      (try rw [projIcc_of_mem hA hw.2.1]) <;>
      (try simp only [mul_one]) <;> first | exact hh.1 _ | exact hh.2.1 _
  have htrace (i : Fin 2) : rectangleProductDistribution U V A B
      (fun w => ricciTrace (Γ w) (i.natAdd 2)) = rectangleProductDistribution U V A B (t i) := by
    apply hcongr (integrable_finsetSum Finset.univ fun k _ =>
      (hconn.1 k (i.natAdd 2) k).integrable (by norm_num)) (hti i)
    filter_upwards [hAe] with w hw
    have hh := hgeom w hw
    fin_cases i
    · dsimp [t, a, c, s]
      rw [projIcc_of_mem hA hw.2.1]
      exact hh.2.2.1
    · exact hh.2.2.2.1
  have hDf (i : Fin 2) (k : Fin 4) : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate k)
      (rectangleProductDistribution U V A B (f i k)) = rectangleProductDistribution U V A B (d i k) := by
    have hrad := hR.2 A B (b i) ((hLp (hb i)).integrable (by norm_num))
    fin_cases k
    · exact hrad.1
    · exact hrad.2
    · fin_cases i
      · change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 2)
          (rectangleProductDistribution U V A B (fun _ => 0)) = rectangleProductDistribution U V A B (fun _ => 0)
        rw [hzero, map_zero]
      · exact hAD 1
    · change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 3)
        (rectangleProductDistribution U V A B (fun _ => 0)) = rectangleProductDistribution U V A B (fun _ => 0)
      rw [hzero, map_zero]
  have hDt (i : Fin 2) : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate (i.natAdd 2))
      (rectangleProductDistribution U V A B (t i)) = rectangleProductDistribution U V A B (dt i) := by
    fin_cases i
    · exact hAD 0
    · change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 3)
        (rectangleProductDistribution U V A B (fun _ => 0)) = rectangleProductDistribution U V A B (fun _ => 0)
      rw [hzero, map_zero]
  have htest {v : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hv : Integrable v (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) : Integrable (fun w => v w * ψ w) (μ.prod ν) := by
    obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
    exact hv.mul_bdd ψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  intro i
  have hS : Integrable (angularRicciSource hU hV e Λ x θ i) (μ.prod ν) := by
    have hcontinuous : Continuous (angularRicciSource hU hV e Λ x θ i) := by
      have hr (w : (ℝ × ℝ) × (ℝ × ℝ)) :
          x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 ^ 2 ≠ 0 := pow_ne_zero _ (hx.choose _ _)
      change Continuous (fun w => angularRicciSource hU hV e Λ x θ i w)
      fin_cases i <;> dsimp [angularRicciSource] <;> fun_prop
    have he : μ.prod ν = volume.restrict K := by
      simp only [μ, ν, K, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [he]
    exact hcontinuous.continuousOn.integrableOn_compact
      ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc))
  refine ⟨hS, ?_⟩
  change ricciDistribution U V A B Γ (i.natAdd 2) (i.natAdd 2) = _
  rw [ricciDistribution]
  simp_rw [hΓ, htrace, hDf, hDt]
  ext ψ
  simp only [add_apply, sub_apply, sum_apply]
  simp_rw [hpair (hdi i _)]
  rw [hpair (hdti i), hpair (hQ (i.natAdd 2) (i.natAdd 2)), hpair hS,
    ← integral_finsetSum _ (fun k _ => htest (hdi i k) ψ),
    ← integral_sub (integrable_finsetSum _ (fun k _ => htest (hdi i k) ψ)) (htest (hdti i) ψ)]
  rw [← integral_add (f := fun w => (∑ k, d i k w * ψ w) - dt i w * ψ w)
      ((integrable_finsetSum Finset.univ (fun k _ => htest (hdi i k) ψ)).sub (htest (hdti i) ψ))
      (htest (hQ (i.natAdd 2) (i.natAdd 2)) ψ)]
  apply integral_congr_ae
  filter_upwards [hAe] with w hw
  have hh := hgeom w hw
  have hsine := Real.sin_sq_add_cos_sq (θ + w.2.1)
  have hsne : Real.sin (θ + w.2.1) ≠ 0 := by
    simpa only [s, projIcc_of_mem hA hw.2.1] using hs0 w.2
  let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  let p := x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
  let q := x.2.2 w.1.1 (projIcc 0 V hV w.1.2)
  let R := 2 * z 0 * (p 0 * q 2 + q 0 * p 2) / Real.exp (z 2)
  have hq₀ : ricciQuadratic (Γ w) 2 2 = R - (Real.cos (θ + w.2.1) / Real.sin (θ + w.2.1)) ^ 2 :=
    hh.2.2.2.2.1
  have hq₁ : ricciQuadratic (Γ w) 3 3 = R * Real.sin (θ + w.2.1) ^ 2 + Real.cos (θ + w.2.1) ^ 2 :=
    hh.2.2.2.2.2
  have hcurv : -(-1 / Real.sin (θ + w.2.1) ^ 2) -
      (Real.cos (θ + w.2.1) / Real.sin (θ + w.2.1)) ^ 2 = 1 := by
    field_simp
    nlinarith only [hsine]
  rw [Fin.sum_univ_four]
  fin_cases i <;>
    dsimp [d, G, angularNullSource, dt, da, b, a, s, c, angularRicciSource] <;>
    rw [projIcc_of_mem hA hw.2.1] <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [hq₀]
    dsimp only [R, z, p, q]
    linear_combination ψ w * hcurv
  · rw [hq₁]
    dsimp only [R, z, p, q]
    ring

end CauchyHorizon
