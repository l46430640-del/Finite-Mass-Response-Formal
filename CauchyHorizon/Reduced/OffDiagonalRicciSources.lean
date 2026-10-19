import CauchyHorizon.Reduced.CoordinateRicci
import CauchyHorizon.Analysis.NullWeakDerivative
import CauchyHorizon.Analysis.DistributionIndependence
import CauchyHorizon.Geometry.AngularRicci
import CauchyHorizon.Geometry.OffDiagonalRicci

/-! All null-angular and off-diagonal angular Ricci distributions vanish. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

def HasOffDiagonalRicciSources {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi →
    (∀ i j : Fin 2,
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) (i.castAdd 2) (j.natAdd 2) = 0 ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) (j.natAdd 2) (i.castAdd 2) = 0) ∧
    ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 2 3 = 0 ∧
    ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 3 2 = 0

set_option maxHeartbeats 3000000 in
theorem IsWaveIntegral.off_diagonal_ricci_sources {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c₀ : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c₀ + horizontalPrimitive hU uIn) :
    HasOffDiagonalRicciSources hU hV x := by
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
  let Γ := coordinateChristoffel hU hV x θ
  let a := fun i y => nullRadialRatio hU hV x i (y, 0)
  let b := fun i y => nullLogDerivative hU hV x i (y, 0)
  let cot := fun t : ℝ => Real.cos (θ + (projIcc 0 A hA t : ℝ)) /
    Real.sin (θ + (projIcc 0 A hA t : ℝ))
  have hcot : Continuous cot := by
    have hs (t : ℝ) : Real.sin (θ + (projIcc 0 A hA t : ℝ)) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [(projIcc 0 A hA t).property.1])
        (by linarith [(projIcc 0 A hA t).property.2]))
    exact (by fun_prop : Continuous (fun t => Real.cos (θ + (projIcc 0 A hA t : ℝ)))).div
      (by fun_prop) hs
  have hci : Integrable (fun y : ℝ × ℝ => cot y.1) ν :=
    (hcot.comp continuous_fst).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hAe : ∀ᵐ w ∂μ.prod ν, w ∈ K := by
    have he : μ.prod ν = volume.restrict K := by
      simp only [μ, ν, K, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [he]
    exact ae_restrict_mem ((measurableSet_Icc.prod measurableSet_Icc).prod
      (measurableSet_Icc.prod measurableSet_Icc))
  have hs (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) : Real.sin (θ + w.2.1) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hw.2.1.1]) (by linarith [hw.2.1.2]))
  have hn (i : Fin 2) (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) :
      (∀ k, Γ w k (i.castAdd 2) (i.castAdd 2) = if k = i.castAdd 2 then b i w.1 else 0) ∧
      ricciTrace (Γ w) (i.castAdd 2) = b i w.1 + 2 * a i w.1 ∧
      ricciQuadratic (Γ w) (i.castAdd 2) (i.castAdd 2) =
        2 * b i w.1 * a i w.1 - 2 * a i w.1 ^ 2 ∧
      Γ w 2 (i.castAdd 2) 2 = a i w.1 :=
    null_connection_contractions (Real.exp_ne_zero _)
      (hx.choose (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)) (hs w hw) i
  have hang (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) :=
    angular_connection_contractions (H := Real.exp (x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2))
      (c := Real.cos (θ + w.2.1))
      (qr := x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 0)
      (pr := x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0)
      (qell := x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 2)
      (pell := x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2)
      (Real.exp_ne_zero _) (hx.choose (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)) (hs w hw)
  have hna (i j : Fin 2) (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) :
      (∀ k, Γ w k (i.castAdd 2) (j.natAdd 2) = if k = j.natAdd 2 then a i w.1 else 0) ∧
      (∀ k, Γ w k (j.natAdd 2) (i.castAdd 2) = if k = j.natAdd 2 then a i w.1 else 0) ∧
      ricciQuadratic (Γ w) (i.castAdd 2) (j.natAdd 2) = 0 ∧
      ricciQuadratic (Γ w) (j.natAdd 2) (i.castAdd 2) = 0 :=
    null_angular_connection_contractions (hx.choose _ _) (hs w hw) i j
  have haa (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) :
      (∀ k, Γ w k 2 3 = if k = 3 then cot w.2.1 else 0) ∧
      (∀ k, Γ w k 3 2 = if k = 3 then cot w.2.1 else 0) ∧
      ricciQuadratic (Γ w) 2 3 = 0 ∧ ricciQuadratic (Γ w) 3 2 = 0 := by
    dsimp only [cot]
    rw [projIcc_of_mem hA hw.2.1]
    exact angular_off_diagonal_contractions (hx.choose _ _) (hs w hw)
  have hconn := hx.coordinate_connection hzin A B θ hA hB hθ hθA
  have hΓ (k i j : Fin 4) : Integrable (fun w => Γ w k i j) (μ.prod ν) :=
    (hconn.1 k i j).integrable (by norm_num)
  have hQ := (hx.coordinate_ricci hzin A B θ hA hB hθ hθA).1.1
  have hai (i : Fin 2) : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => a i w.1) (μ.prod ν) :=
    (hΓ 2 (i.castAdd 2) 2).congr (by
      filter_upwards [hAe] with w hw
      exact (hn i w hw).2.2.2)
  have hbi (i : Fin 2) : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => b i w.1) (μ.prod ν) :=
    (hΓ (i.castAdd 2) (i.castAdd 2) (i.castAdd 2)).congr (by
      filter_upwards [hAe] with w hw
      exact ((hn i w hw).1 _).trans (if_pos rfl))
  have hpair {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f (μ.prod ν))
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B f ψ = ∫ w, f w * ψ w ∂(μ.prod ν) := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) (μ.prod ν) f ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hcongr {f g : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f (μ.prod ν))
      (hg : Integrable g (μ.prod ν)) (he : f =ᵐ[μ.prod ν] g) :
      rectangleProductDistribution U V A B f = rectangleProductDistribution U V A B g := by
    ext ψ
    rw [hpair hf, hpair hg]
    exact integral_congr_ae (he.mono fun _ h => congrArg (· * _) h)
  have hzero : rectangleProductDistribution U V A B (fun _ => 0) = 0 := by
    ext ψ
    rw [hpair (integrable_const 0)]
    simp only [zero_mul, integral_zero, zero_apply]
  have hDA (f : ℝ × ℝ → ℝ) (hf : Integrable (fun w => f w.1) (μ.prod ν)) (j : Fin 2) :
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate (j.natAdd 2))
        (rectangleProductDistribution U V A B (fun w => f w.1)) = 0 := by
    have hd := rectangle_independent_derivatives hA hB
      (f := fun _ => (1 : ℝ)) (g := fun _ => (1 : ℝ)) (integrable_const 1) (integrable_const 1)
    have hf' : Integrable (fun w => f w.1 * (1 : ℝ)) (rectangleProductMeasure U V A B) := by
      change Integrable (fun w => f w.1 * (1 : ℝ)) (μ.prod ν)
      simpa only [mul_one] using hf
    fin_cases j
    · change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 0), (1, 0))
        (rectangleProductDistribution U V A B (fun w => f w.1)) = 0
      simpa only [mul_one, Prod.zero_eq_mk] using rectangle_product_right_derivative_zero (f := f) (b := fun _ => 1)
        (U := U) (V := V) (A := A) (B := B) (v := (1, 0)) (integrable_const 1) hf' hd.1
    · change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 0), (0, 1))
        (rectangleProductDistribution U V A B (fun w => f w.1)) = 0
      simpa only [mul_one, Prod.zero_eq_mk] using rectangle_product_right_derivative_zero (f := f) (b := fun _ => 1)
        (U := U) (V := V) (A := A) (B := B) (v := (0, 1)) (integrable_const 1) hf' hd.2
  have hDC : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate 3)
      (rectangleProductDistribution U V A B (fun w => cot w.2.1)) = 0 := by
    have hd := (rectangle_independent_derivatives hA hB
      (f := fun _ => (1 : ℝ)) (g := cot) (integrable_const 1) hci).2
    have hcprod : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => cot w.2.1) (μ.prod ν) :=
      hci.comp_snd μ
    have hcprod' := hcprod.const_mul (1 : ℝ)
    have hh := rectangle_product_right_derivative_zero (U := U) (V := V) (A := A) (B := B)
      (f := fun _ => (1 : ℝ)) (b := fun y => cot y.1) (v := (0, 1)) hci hcprod' hd
    change Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 0), (0, 1))
      (rectangleProductDistribution U V A B (fun w => cot w.2.1)) = 0
    simpa only [one_mul, Prod.zero_eq_mk] using hh
  have hDN (i : Fin 2) : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate (i.castAdd 2))
      (rectangleProductDistribution U V A B (fun w => cot w.2.1)) = 0 := by
    have hh := null_weighted_derivatives_of_sections (A := A) (B := B) hU hV
      (f₁ := fun _ => (1 : ℝ)) (f₂ := fun _ => (1 : ℝ)) (g₁ := fun _ => 0) (g₂ := fun _ => 0)
      (integrable_const 1) (integrable_const 1) (integrable_const 0) (integrable_const 0)
      (Eventually.of_forall fun _ => (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))).contDiffOn.absolutelyContinuousOnInterval)
      (Eventually.of_forall fun _ => Eventually.of_forall fun t => hasDerivWithinAt_const t _ _)
      (Eventually.of_forall fun _ => (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))).contDiffOn.absolutelyContinuousOnInterval)
      (Eventually.of_forall fun _ => Eventually.of_forall fun t => hasDerivWithinAt_const t _ _)
      (fun y => cot y.1) hci
    simp only [one_mul, zero_mul, hzero] at hh
    fin_cases i
    · exact hh.1
    · exact hh.2
  have htN (i : Fin 2) : rectangleProductDistribution U V A B
      (fun w => ricciTrace (Γ w) (i.castAdd 2)) =
        rectangleProductDistribution U V A B (fun w => b i w.1 + 2 * a i w.1) := by
    apply hcongr (integrable_finsetSum _ (fun k _ => hΓ k (i.castAdd 2) k))
      ((hbi i).add ((hai i).const_mul 2))
    filter_upwards [hAe] with w hw
    exact (hn i w hw).2.1
  have htA (j : Fin 2) : rectangleProductDistribution U V A B
      (fun w => ricciTrace (Γ w) (j.natAdd 2)) =
        if j = 0 then rectangleProductDistribution U V A B (fun w => cot w.2.1) else 0 := by
    fin_cases j
    · apply hcongr (integrable_finsetSum _ (fun k _ => hΓ k 2 k)) (hci.comp_snd μ)
      filter_upwards [hAe] with w hw
      dsimp only [cot]
      rw [projIcc_of_mem hA hw.2.1]
      exact (hang w hw).2.2.1
    · change rectangleProductDistribution U V A B (fun w => ricciTrace (Γ w) 3) = 0
      rw [← hzero]
      apply hcongr (integrable_finsetSum _ (fun k _ => hΓ k 3 k)) (integrable_const 0)
      filter_upwards [hAe] with w hw
      exact (hang w hw).2.2.2.1
  have hlead {i j k₀ : Fin 4} {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ}
      (hf : Integrable f (μ.prod ν))
      (he : ∀ᵐ w ∂μ.prod ν, ∀ k, Γ w k i j = if k = k₀ then f w else 0)
      (hd : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate k₀)
        (rectangleProductDistribution U V A B f) = 0) :
      ∀ k, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate k)
        (rectangleProductDistribution U V A B (fun w => Γ w k i j)) = 0 := by
    intro k
    by_cases hk : k = k₀
    · subst k
      have heq := hcongr (hΓ k₀ i j) hf (he.mono fun w hw => by simpa using hw k₀)
      rw [heq]
      exact hd
    · have heq := hcongr (hΓ k i j) (integrable_const 0) (he.mono fun w hw => by simpa [hk] using hw k)
      rw [heq, hzero, map_zero]
  have hfinish {i j : Fin 4}
      (hl : ∀ k, Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate k)
        (rectangleProductDistribution U V A B (fun w => Γ w k i j)) = 0)
      (ht : Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate j)
        (rectangleProductDistribution U V A B (fun w => ricciTrace (Γ w) i)) = 0)
      (hq : ∀ᵐ w ∂μ.prod ν, ricciQuadratic (Γ w) i j = 0) :
      ricciDistribution U V A B Γ i j = 0 := by
    have heq : rectangleProductDistribution U V A B (fun w => ricciQuadratic (Γ w) i j) =
        rectangleProductDistribution U V A B (fun _ => 0) :=
      hcongr (hQ i j) (integrable_const 0) hq
    simp only [ricciDistribution, hl, ht, heq, hzero, Finset.sum_const_zero, sub_self, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    constructor
    · apply hfinish (hlead (hai i) (hAe.mono fun w hw => (hna i j w hw).1) (hDA (a i) (hai i) j))
      · rw [htN]
        exact hDA (fun y => b i y + 2 * a i y) ((hbi i).add ((hai i).const_mul 2)) j
      · exact hAe.mono fun w hw => (hna i j w hw).2.2.1
    · apply hfinish (hlead (hai i) (hAe.mono fun w hw => (hna i j w hw).2.1) (hDA (a i) (hai i) j))
      · rw [htA]
        split_ifs
        · exact hDN i
        · exact map_zero _
      · exact hAe.mono fun w hw => (hna i j w hw).2.2.2
  · apply hfinish (hlead (hci.comp_snd μ) (hAe.mono fun w hw => (haa w hw).1) hDC)
    · rw [show (2 : Fin 4) = (0 : Fin 2).natAdd 2 from rfl, htA]
      exact hDC
    · exact hAe.mono fun w hw => (haa w hw).2.2.1
  · apply hfinish (hlead (hci.comp_snd μ) (hAe.mono fun w hw => (haa w hw).2.1) hDC)
    · rw [show (3 : Fin 4) = (1 : Fin 2).natAdd 2 from rfl, htA]
      exact map_zero _
    · exact hAe.mono fun w hw => (haa w hw).2.2.2

end CauchyHorizon
