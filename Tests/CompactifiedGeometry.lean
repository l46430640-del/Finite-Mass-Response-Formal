import CauchyHorizon.Reduced.CompactifiedGeometry

open Set Filter
open scoped Topology ENNReal

namespace CauchyHorizon.Tests

-- The time domain itself is compact, with the genuine infinite endpoint.
example : CompactSpace ℝ≥0∞ := inferInstance

example {E : Type*} [TopologicalSpace E] {f : ℝ → E} {z : E}
    (hf : ContinuousOn f (Ici 0)) (hz : Tendsto f atTop (𝓝 z)) :
    compactifiedTimeTrace hf hz (ENNReal.ofReal 0) = f 0 ∧
      compactifiedTimeTrace hf hz ⊤ = z :=
  ⟨compactifiedTimeTrace_ofReal hf hz le_rfl, compactifiedTimeTrace_top hf hz⟩

-- Every finite section is unchanged, not merely eventually equal to the original field.
example {E : Type*} [TopologicalSpace E] {f : ℝ → E} {z : E}
    (hf : ContinuousOn f (Ici 0)) (hz : Tendsto f atTop (𝓝 z))
    (T : Ici (0 : ℝ)) (t : Icc 0 (T : ℝ)) :
    compactifiedTimeTrace hf hz (ENNReal.ofReal t) = f t :=
  compactifiedTimeTrace_ofReal hf hz t.property.1

-- A constant field acquires no artificial endpoint value.
example (c : ℝ) :
    compactifiedTimeTrace (continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => c) (Ici 0))
      tendsto_const_nhds = ContinuousMap.const ℝ≥0∞ c := by
  ext t
  by_cases ht : t = ⊤
  · subst t
    exact compactifiedTimeTrace_top _ _
  · exact compactifiedTimeTrace_finite _ _ ht

-- The Banach-valued continuous map is jointly continuous on the compactified spacetime strip.
example {U ε : ℝ} (G : C(ℝ≥0∞, C(Icc ε U, ℝ))) :
    Continuous (fun q : ℝ≥0∞ × Icc ε U => G q.1 q.2) := G.uncurry.continuous

-- Norm convergence controls every time and incoming point simultaneously, including infinity.
example {U ε : ℝ} (G : ℕ → C(ℝ≥0∞, C(Icc ε U, ℝ)))
    (hG : Tendsto G atTop (𝓝 (G 0))) :
    ∀ d > (0 : ℝ), ∀ᶠ n in atTop, ∀ t u, |G n t u - G 0 t u| < d := by
  intro d hd
  filter_upwards [(Metric.tendsto_nhds (u := G)).1 hG d hd] with n hn
  intro t u
  rw [← Real.dist_eq]
  exact ((ContinuousMap.dist_apply_le_dist u).trans
    (ContinuousMap.dist_apply_le_dist t)).trans_lt hn

-- The same late-strip lower bounds survive at the infinite endpoint, uniformly in the sequence.
example {U ε k : ℝ} (hε : 0 ≤ ε)
    (X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T)
    (N : (n : ℕ) → (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))
    (hG : HasCompactifiedGeometry hε k X N) :
    ∃ R A : ℕ → C(ℝ≥0∞, C(Icc ε U, ℝ)),
      (∀ n, Tendsto (fun t => waveRadius (renormalizedWaveRow hε k (X n) t)) atTop (𝓝 (R n ⊤))) ∧
      (∀ n, Tendsto (fun t => waveAmplitude (renormalizedWaveRow hε k (X n) t)) atTop (𝓝 (A n ⊤))) ∧
      ∃ ρ Alo Ahi : ℝ, 0 < ρ ∧ 0 < Alo ∧ 0 < Ahi ∧
        ∀ n u, ρ ≤ R n ⊤ u ∧ Alo ≤ A n ⊤ u ∧ A n ⊤ u ≤ Ahi := by
  obtain ⟨R, A, _Nu, _hfinite, htrace, _hR, _hA, _hNu,
    _T, ρ, Alo, Ahi, _hT, hρ, hAlo, hAhi, hb⟩ := hG
  exact ⟨R, A, (fun n => (htrace n).1), (fun n => (htrace n).2.1),
    ρ, Alo, Ahi, hρ, hAlo, hAhi, fun n u => hb n ⊤ le_top u⟩

end CauchyHorizon.Tests
