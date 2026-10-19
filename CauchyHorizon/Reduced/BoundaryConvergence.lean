import CauchyHorizon.Reduced.BoundaryTrace
import CauchyHorizon.Reduced.AmplitudeTrace
import CauchyHorizon.Reduced.RadialBoundary
import CauchyHorizon.Analysis.UniformTail
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! Continuous finite-time observables of the actual renormalized field. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

noncomputable def renormalizedWaveRectangle {U ε T : ℝ} (hε : 0 ≤ ε) (k : ℝ) :
    C(WaveState U T, C(Icc 0 T, C(Icc ε U, WaveVector))) :=
  (⟨fun q : (WaveState U T × Icc 0 T) × Icc ε U =>
    q.1.1.1 ⟨q.2, hε.trans q.2.property.1, q.2.property.2⟩ q.1.2 +
      (fun i => if i = 2 then 2 * k * (q.1.2 : ℝ) else 0), by
        apply Continuous.add
        · exact (continuous_fst.fst.fst.eval (by fun_prop)).eval continuous_fst.snd
        · apply continuous_pi
          intro i
          split_ifs <;> fun_prop⟩ :
      C((WaveState U T × Icc 0 T) × Icc ε U, WaveVector)).curry.curry

theorem renormalizedWaveRow_tendstoUniformlyOn {ι E : Type*} [PseudoMetricSpace E] {l : Filter ι}
    {U ε k : ℝ} (hε : 0 ≤ ε)
    (X : ι → (T : Ici (0 : ℝ)) → WaveState U T) (Y : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ i (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X i T) = X i S)
    (hY : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (Y T) = Y S)
    (G : C(C(Icc ε U, WaveVector), E)) (T : Ici (0 : ℝ))
    (hlim : Tendsto (fun i => X i T) l (𝓝 (Y T))) :
    TendstoUniformlyOn (fun i t => G (renormalizedWaveRow hε k (X i) t))
      (fun t => G (renormalizedWaveRow hε k Y t)) l (Icc 0 (T : ℝ)) := by
  have hcont := (ContinuousMap.continuous_postcomp G).comp (renormalizedWaveRectangle (T := (T : ℝ)) hε k).continuous
  have hh := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    (hcont.tendsto _ |>.comp hlim) univ isCompact_univ
  have he (W : (T : Ici (0 : ℝ)) → WaveState U T)
      (hW : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
        waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
          le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (W T) = W S)
      (t : Icc 0 (T : ℝ)) :
      renormalizedWaveRectangle hε k (W T) t = renormalizedWaveRow hε k W t := by
    apply ContinuousMap.ext
    intro u
    funext i
    exact (renormalizedWaveRow_apply hε W hW T t.property.1 t.property.2 u i).symm
  apply Metric.tendstoUniformlyOn_iff.2
  intro δ hδ
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hh δ hδ] with i hi
  intro t ht
  have hb := hi ⟨t, ht⟩ (mem_univ _)
  change dist (G (renormalizedWaveRectangle hε k (Y T) ⟨t, ht⟩))
    (G (renormalizedWaveRectangle hε k (X i T) ⟨t, ht⟩)) < δ at hb
  simpa only [he Y hY, he (X i) (hX i)] using hb

theorem scalarBoundaryRow_tendstoUniformlyOn {ι : Type*} {l : Filter ι}
    {U ε : ℝ} (hε : 0 ≤ ε)
    (X : ι → (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))
    (Y : (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))
    (hX : ∀ i (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      X i S u v = X i T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (hY : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      Y S u v = Y T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (T : Ici (0 : ℝ)) (hlim : Tendsto (fun i => X i T) l (𝓝 (Y T))) :
    TendstoUniformlyOn (fun i => scalarBoundaryRow hε (X i))
      (scalarBoundaryRow hε Y) l (Icc 0 (T : ℝ)) := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro δ hδ
  filter_upwards [(Metric.tendsto_nhds (α := C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))).1 hlim δ hδ] with i hi
  intro t ht
  rw [dist_comm] at hi
  apply lt_of_le_of_lt ?_ hi
  apply (ContinuousMap.dist_le dist_nonneg).2
  intro u
  rw [scalarBoundaryRow_apply hε Y hY T ht.1 ht.2,
    scalarBoundaryRow_apply hε (X i) (hX i) T ht.1 ht.2]
  let w : Icc 0 U := ⟨u, hε.trans u.property.1, u.property.2⟩
  exact (ContinuousMap.dist_apply_le_dist (f := Y T w) (g := X i T w) ⟨t, ht⟩).trans
    (ContinuousMap.dist_apply_le_dist (f := Y T) (g := X i T) w)

end CauchyHorizon
