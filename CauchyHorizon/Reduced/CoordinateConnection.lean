import CauchyHorizon.Reduced.CoordinateMetric
import CauchyHorizon.Geometry.ConnectionChange

/-! The actual coordinate connection is torsion free, metric compatible and locally L2. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

noncomputable def coordinateChristoffel {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (θ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) (k i j : Fin 4) : ℝ :=
  christoffel (coordinateMetricInverse hU hV x θ w)
    (fun l => coordinateMetricPartial hU hV x θ l w) k i j

def HasL2CoordinateConnection {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (x : WaveState U V) : Prop :=
  ∀ (A B θ : ℝ), 0 ≤ A → 0 ≤ B → 0 < θ → θ + A < Real.pi →
    (∀ k i j, MemLp (fun w => coordinateChristoffel hU hV x θ w k i j) 2
      (rectangleProductMeasure U V A B)) ∧
    (∀ k i j l m n, Integrable (fun w => coordinateChristoffel hU hV x θ w k i j *
      coordinateChristoffel hU hV x θ w l m n) (rectangleProductMeasure U V A B)) ∧
    ∀ w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B),
      IsMetricConnection (coordinateMetric hU hV x θ w)
        (fun k => coordinateMetricPartial hU hV x θ k w) (coordinateChristoffel hU hV x θ w)

theorem IsWaveIntegral.coordinate_connection {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasL2CoordinateConnection hU hV x := by
  intro A B θ hA hB hθ hθA
  have hm := hx.coordinate_metric hzin A B θ hA hB hθ hθA
  let K := (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)
  have hμ : rectangleProductMeasure U V A B = volume.restrict K := by
    simp only [K, rectangleProductMeasure, Measure.volume_eq_prod, Measure.prod_restrict]
  have hInv (i j : Fin 4) : MemLp (fun w => coordinateMetricInverse hU hV x θ w i j) ⊤
      (rectangleProductMeasure U V A B) := by
    rw [hμ]
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hm.2.1 i j)
    apply memLp_top_of_bound ((hm.2.1 i j).aestronglyMeasurable hK.measurableSet) C
    filter_upwards [ae_restrict_mem hK.measurableSet] with w hw
    exact hC w hw
  have hΓ (k i j : Fin 4) : MemLp (fun w => coordinateChristoffel hU hV x θ w k i j) 2
      (rectangleProductMeasure U V A B) :=
    christoffel_memLp hInv (fun i j k => ((hm.2.2.1 j k).2 i).1) k i j
  refine ⟨hΓ, ?_, ?_⟩
  · intro k i j l m n
    exact (hΓ k i j).integrable_mul (hΓ l m n)
  · intro w hw
    have hg := hm.2.2.2 w hw
    apply christoffel_identities
    · intro i j
      exact congrFun (congrFun hg.2.2.2.1 j) i
    · exact hg.2.2.2.2.1
    · intro k i j
      fin_cases k <;> fin_cases i <;> fin_cases j <;> rfl

theorem IsWaveIntegral.coordinate_connection_unique {U V e Λ A B θ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi)
    {w : (ℝ × ℝ) × (ℝ × ℝ)}
    (hw : w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B))
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    IsMetricConnection (coordinateMetric hU hV x θ w)
      (fun k => coordinateMetricPartial hU hV x θ k w) Γ ↔
        Γ = coordinateChristoffel hU hV x θ w := by
  have hg := (hx.coordinate_metric hzin A B θ hA hB hθ hθA).2.2.2 w hw
  constructor
  · intro hΓ
    apply hΓ.eq_christoffel
    · intro i j
      exact congrFun (congrFun hg.2.2.2.1 j) i
    · exact hg.2.2.2.2.2.1
  · rintro rfl
    exact (hx.coordinate_connection hzin A B θ hA hB hθ hθA).2.2 w hw

theorem IsWaveIntegral.coordinate_connection_change {U V e Λ A B θ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi)
    {w : (ℝ × ℝ) × (ℝ × ℝ)}
    (hw : w ∈ (Icc 0 U ×ˢ Icc 0 V) ×ˢ (Icc 0 A ×ˢ Icc 0 B))
    {J K : Matrix (Fin 4) (Fin 4) ℝ} (hJK : J * K = 1) (hKJ : K * J = 1)
    {dJ : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ} (hdJ : ∀ i k j, dJ i k j = dJ j k i) :
    connectionChange (coordinateChristoffel hU hV x θ w) J K dJ =
      christoffel (K * coordinateMetricInverse hU hV x θ w * K.transpose)
        (metricChangeDerivative (coordinateMetric hU hV x θ w)
          (fun k => coordinateMetricPartial hU hV x θ k w) J dJ) := by
  have hg := (hx.coordinate_metric hzin A B θ hA hB hθ hθA).2.2.2 w hw
  exact ((hx.coordinate_connection hzin A B θ hA hB hθ hθA).2.2 w hw).change_eq_christoffel
    hg.2.2.2.1 hg.2.2.2.2.2.1 hJK hKJ hdJ

end CauchyHorizon
