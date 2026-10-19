import CauchyHorizon.Reduced.ConstraintIntegral
import CauchyHorizon.Reduced.RadialBoundary

/-! Finite-time radial convergence from the actual flux integral operator. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

theorem IsWaveIntegral.radial_tendsto {ι : Type*} {l : Filter ι}
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : ι → C(Icc 0 U, WaveVector)} {vOut : ι → C(Icc 0 V, WaveVector)}
    {uIn : ι → Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : ι → WaveState U V}
    {zRef : C(Icc 0 U, WaveVector)} {vRef : C(Icc 0 V, WaveVector)}
    {uRef : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {y : WaveState U V}
    (hx : ∀ i, IsWaveIntegral hU hV e Λ (zIn i) (vOut i) (uIn i) (x i))
    (hy : IsWaveIntegral hU hV e Λ zRef vRef uRef y)
    (hr : ∀ i u v, (x i).1 u v 0 ≠ 0) (hyR : ∀ u v, y.1 u v 0 ≠ 0)
    (hlim : Tendsto (fun i => (x i).1) l (𝓝 y.1)) :
    Tendsto (fun i => radialNuField hV e Λ (zIn i) (x i).1 (hr i)) l
        (𝓝 (radialNuField hV e Λ zRef y.1 hyR)) ∧
      Tendsto (fun i => radialProductField hV e Λ (zIn i) (x i).1 (hr i)) l
        (𝓝 (radialProductField hV e Λ zRef y.1 hyR)) := by
  let P := {z : WaveRectangle U V // ∀ u v, z u v 0 ≠ 0}
  let F : C(P, C(Icc 0 U, C(Icc 0 V, ℝ))) :=
    (⟨fun q : P × Icc 0 U => radialNuOperator hV e Λ (q.1.val q.2), by
      apply continuous_iff_continuousAt.2
      intro q
      exact (radialNuOperator_contDiffAt hV e Λ _ (q.1.property q.2)).continuousAt.comp
        (f := fun q : P × Icc 0 U => q.1.val q.2)
        (((continuous_subtype_val.comp continuous_fst).eval continuous_snd).continuousAt)⟩ :
      C(P × Icc 0 U, C(Icc 0 V, ℝ))).curry
  have he {z : C(Icc 0 U, WaveVector)} {v : C(Icc 0 V, WaveVector)}
      {u : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {w : WaveState U V}
      (hw : IsWaveIntegral hU hV e Λ z v u w) (hwR : ∀ u v, w.1 u v 0 ≠ 0) :
      F ⟨w.1, hwR⟩ = radialNuField hV e Λ z w.1 hwR := by
    apply ContinuousMap.ext
    intro a
    exact hw.radialNu_operator hwR a
  have hs : Tendsto (fun i => (⟨(x i).1, hr i⟩ : P)) l (𝓝 (⟨y.1, hyR⟩ : P)) :=
    tendsto_subtype_rng.2 hlim
  have hn := F.continuous.tendsto (⟨y.1, hyR⟩ : P) |>.comp hs
  have hseq : ∀ i, F ⟨(x i).1, hr i⟩ = radialNuField hV e Λ (zIn i) (x i).1 (hr i) :=
    fun i => he (hx i) (hr i)
  simp only [Function.comp_def, hseq, he hy hyR] at hn
  refine ⟨hn, ?_⟩
  let R : WaveRectangle U V →L[ℝ] C(Icc 0 U, C(Icc 0 V, ℝ)) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
      (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj (0 : Fin 3)))
  have hh := ((R.continuous.tendsto y.1).comp hlim).mul hn
  exact hh

end CauchyHorizon
