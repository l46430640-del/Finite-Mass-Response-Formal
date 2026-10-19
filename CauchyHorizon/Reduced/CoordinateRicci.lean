import CauchyHorizon.Reduced.CoordinateConnection
import CauchyHorizon.Geometry.NullRicci

/-! The actual null Ricci distributions reduce to the radial constraint combinations. -/

open MeasureTheory Set Filter
open scoped Distributions

namespace CauchyHorizon

noncomputable def nullRadialRatio {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (i : Fin 2) (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  let r := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0
  ![x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 0 / r,
    x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0 / r] i

noncomputable def nullLogDerivative {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (i : Fin 2) (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  ![x.2.2 w.1.1 (projIcc 0 V hV w.1.2) 2,
    x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 2] i

def HasCoordinateRicci {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi →
    HasRicciPairing U V A B (coordinateChristoffel hU hV x θ) ∧
    ∀ i : Fin 2,
      let a := nullRadialRatio hU hV x i
      let b := nullLogDerivative hU hV x i
      MemLp a 2 (rectangleProductMeasure U V A B) ∧
      Integrable (fun w => 2 * b w * a w - 2 * a w ^ 2) (rectangleProductMeasure U V A B) ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) (i.castAdd 2) (i.castAdd 2) =
        (-2 : ℝ) • Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (productCoordinate (i.castAdd 2))
          (rectangleProductDistribution U V A B a) +
        rectangleProductDistribution U V A B (fun w => 2 * b w * a w - 2 * a w ^ 2)

set_option maxHeartbeats 1500000 in
theorem IsWaveIntegral.coordinate_ricci {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasCoordinateRicci hU hV x := by
  intro A B θ hA hB hθ hθA
  let μ := rectangleProductMeasure U V A B
  let K := (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)
  let Γ := coordinateChristoffel hU hV x θ
  let a := nullRadialRatio hU hV x
  let b := nullLogDerivative hU hV x
  have hμ : μ = volume.restrict K := by
    simp only [μ, K, rectangleProductMeasure, Measure.volume_eq_prod, Measure.prod_restrict]
  let : IsFiniteMeasure μ := by
    simp only [μ, rectangleProductMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  have hAe : ∀ᵐ w ∂μ, w ∈ K := by
    rw [hμ]
    exact ae_restrict_mem ((measurableSet_Icc.prod measurableSet_Icc).prod
      (measurableSet_Icc.prod measurableSet_Icc))
  have hc := hx.coordinate_connection hzin A B θ hA hB hθ hθA
  have hΓ (k i j : Fin 4) : Integrable (fun w => Γ w k i j) μ :=
    (hc.1 k i j).integrable (by norm_num)
  have hp := ricci_distribution_pairing hΓ hc.2.1
  have hn (i : Fin 2) (w : (ℝ × ℝ) × (ℝ × ℝ)) (hw : w ∈ K) :
      (∀ k, Γ w k (i.castAdd 2) (i.castAdd 2) = if k = i.castAdd 2 then b i w else 0) ∧
      ricciTrace (Γ w) (i.castAdd 2) = b i w + 2 * a i w ∧
      ricciQuadratic (Γ w) (i.castAdd 2) (i.castAdd 2) = 2 * b i w * a i w - 2 * a i w ^ 2 ∧
      Γ w 2 (i.castAdd 2) 2 = a i w := by
    exact null_connection_contractions (Real.exp_ne_zero _)
      (hx.choose (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2))
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hw.2.1.1])
        (by linarith [hw.2.1.2]))) i
  have htest {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f μ)
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) : Integrable (fun w => f w * ψ w) μ := by
    obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
    exact hf.mul_bdd ψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hpair {f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hf : Integrable f μ)
      (ψ : 𝓓(openRectangleProduct U V A B, ℝ)) :
      rectangleProductDistribution U V A B f ψ = ∫ w, f w * ψ w ∂μ := by
    change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) μ f ψ = _
    rw [TestFunction.integralAgainstBilinCLM_eq_integral (hf.locallyIntegrable.locallyIntegrableOn _)]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  refine ⟨hp, ?_⟩
  intro i
  let j : Fin 4 := i.castAdd 2
  have ha : MemLp (a i) 2 μ := (hc.1 2 j 2).ae_eq (by
    filter_upwards [hAe] with w hw
    exact (hn i w hw).2.2.2)
  have hb : MemLp (b i) 2 μ := (hc.1 j j j).ae_eq (by
    filter_upwards [hAe] with w hw
    exact ((hn i w hw).1 j).trans (if_pos rfl))
  have hai : Integrable (a i) μ := ha.integrable (by norm_num)
  have hbi : Integrable (b i) μ := hb.integrable (by norm_num)
  have hQ : Integrable (fun w => 2 * b i w * a i w - 2 * a i w ^ 2) μ :=
    (hp.1 j j).congr (by
      filter_upwards [hAe] with w hw
      exact (hn i w hw).2.2.1)
  refine ⟨ha, hQ, ?_⟩
  ext ψ
  let dψ : Fin 4 → 𝓓(openRectangleProduct U V A B, ℝ) :=
    fun k => TestFunction.lineDerivCLM ℝ (productCoordinate k) ψ
  have hlead (k : Fin 4) : (∫ w, Γ w k j j * dψ k w ∂μ) =
      if k = j then (∫ w, b i w * dψ j w ∂μ) else 0 := by
    calc
      _ = ∫ w, (if k = j then b i w else 0) * dψ k w ∂μ := by
        apply integral_congr_ae
        filter_upwards [hAe] with w hw
        rw [(hn i w hw).1 k]
      _ = _ := by split_ifs with h <;> simp [h]
  have hsum : (∑ k, -(∫ w, Γ w k j j * dψ k w ∂μ)) = -(∫ w, b i w * dψ j w ∂μ) := by
    simp_rw [hlead]
    simp
  have htrace : (∫ w, ricciTrace (Γ w) j * dψ j w ∂μ) =
      (∫ w, b i w * dψ j w ∂μ) + 2 * ∫ w, a i w * dψ j w ∂μ := by
    calc
      _ = ∫ w, b i w * dψ j w + 2 * (a i w * dψ j w) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hAe] with w hw
        rw [(hn i w hw).2.1]
        ring
      _ = _ := by rw [integral_add (htest hbi _) ((htest hai _).const_mul 2), integral_const_mul]
  have hquadratic : (∫ w, ricciQuadratic (Γ w) j j * ψ w ∂μ) =
      ∫ w, (2 * b i w * a i w - 2 * a i w ^ 2) * ψ w ∂μ := by
    apply integral_congr_ae
    filter_upwards [hAe] with w hw
    rw [(hn i w hw).2.2.1]
  rw [(hp.2 j j ψ).2.2.2]
  change (∑ k, -(∫ w, Γ w k j j * dψ k w ∂μ)) +
    (∫ w, ricciTrace (Γ w) j * dψ j w ∂μ) + (∫ w, ricciQuadratic (Γ w) j j * ψ w ∂μ) = _
  rw [hsum, htrace, hquadratic]
  simp only [add_apply, smul_apply,
    Distribution.lineDerivCLM_apply, smul_eq_mul]
  rw [hpair hai, hpair hQ]
  change _ = -2 * -(∫ w, a i w * dψ j w ∂μ) + _
  ring

end CauchyHorizon
