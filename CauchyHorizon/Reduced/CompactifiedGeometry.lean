import CauchyHorizon.Analysis.CompactifiedTime
import CauchyHorizon.Reduced.BoundaryConvergence
import CauchyHorizon.Reduced.RegularRadius

/-! The actual radius, lapse amplitude and radial velocity on a common compactified time strip. -/

open Set Filter
open scoped Topology ENNReal

namespace CauchyHorizon

theorem renormalizedWaveRow_continuousOn {U ε k : ℝ} (hε : 0 ≤ ε)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S) :
    ContinuousOn (renormalizedWaveRow hε k X) (Ici 0) := by
  apply continuousOn_halfline_of_prefixes
  intro T
  have hT : 0 ≤ (T : ℝ) := T.property
  apply (intervalExtension hT (renormalizedWaveRectangle hε k (X T))).continuous.continuousOn.congr
  intro t ht
  rw [intervalExtension_apply, projIcc_of_mem hT ht]
  ext u i
  exact renormalizedWaveRow_apply hε X hX T ht.1 ht.2 u i

theorem scalarBoundaryRow_continuousOn {U ε : ℝ} (hε : 0 ≤ ε)
    (Y : (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))
    (hY : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      Y S u v = Y T u ⟨v, v.property.1, v.property.2.trans hST⟩) :
    ContinuousOn (scalarBoundaryRow hε Y) (Ici 0) := by
  apply continuousOn_halfline_of_prefixes
  intro T
  have hT : 0 ≤ (T : ℝ) := T.property
  let rows : C(Icc 0 (T : ℝ), C(Icc ε U, ℝ)) :=
    (⟨fun q : Icc 0 (T : ℝ) × Icc ε U =>
      Y T ⟨q.2, hε.trans q.2.property.1, q.2.property.2⟩ q.1, by fun_prop⟩ :
      C(Icc 0 (T : ℝ) × Icc ε U, ℝ)).curry
  apply (intervalExtension hT rows).continuous.continuousOn.congr
  intro t ht
  rw [intervalExtension_apply, projIcc_of_mem hT ht]
  ext u
  exact scalarBoundaryRow_apply hε Y hY T ht.1 ht.2 u

def HasCompactifiedGeometry {U ε : ℝ} (hε : 0 ≤ ε) (k : ℝ)
    (X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T)
    (N : (n : ℕ) → (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ))) : Prop :=
  ∃ R A Nu : ℕ → C(ℝ≥0∞, C(Icc ε U, ℝ)),
    (∀ (n : ℕ) (S : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htS : t ≤ S) (u : Icc ε U),
      R n (ENNReal.ofReal t) u = (X n S).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htS⟩ 0 ∧
      A n (ENNReal.ofReal t) u = Real.exp (2 * k * t) *
        Real.exp ((X n S).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htS⟩ 2) ∧
      Nu n (ENNReal.ofReal t) u = N n S ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htS⟩) ∧
    (∀ n, Tendsto (fun t => waveRadius (renormalizedWaveRow hε k (X n) t)) atTop (𝓝 (R n ⊤)) ∧
      Tendsto (fun t => waveAmplitude (renormalizedWaveRow hε k (X n) t)) atTop (𝓝 (A n ⊤)) ∧
      Tendsto (scalarBoundaryRow hε (N n)) atTop (𝓝 (Nu n ⊤))) ∧
    Tendsto R atTop (𝓝 (R 0)) ∧ Tendsto A atTop (𝓝 (A 0)) ∧ Tendsto Nu atTop (𝓝 (Nu 0)) ∧
    ∃ T₀ ρ Alo Ahi : ℝ, 0 ≤ T₀ ∧ 0 < ρ ∧ 0 < Alo ∧ 0 < Ahi ∧
      ∀ n (t : ℝ≥0∞), ENNReal.ofReal T₀ ≤ t → ∀ u,
        ρ ≤ R n t u ∧ Alo ≤ A n t u ∧ A n t u ≤ Ahi

theorem compactified_geometry {U ε k T₀ ρ Alo Ahi : ℝ} (hε : 0 ≤ ε)
    (hT₀ : 0 ≤ T₀) (hρ : 0 < ρ) (hAlo : 0 < Alo) (hAhi : 0 < Ahi)
    (X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T)
    (N : (n : ℕ) → (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))
    (hX : ∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X n T) = X n S)
    (hN : ∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      N n S u v = N n T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (Z : ℕ → C(Icc ε U, WaveVector)) (Nh : ℕ → C(Icc ε U, ℝ))
    (hZ : ∀ n, Tendsto (renormalizedWaveRow hε k (X n)) atTop (𝓝 (Z n)))
    (hNh : ∀ n, Tendsto (scalarBoundaryRow hε (N n)) atTop (𝓝 (Nh n)))
    (hZseq : Tendsto Z atTop (𝓝 (Z 0)))
    (hXseq : TendstoUniformlyOn (fun n => renormalizedWaveRow hε k (X n))
      (renormalizedWaveRow hε k (X 0)) atTop (Ici 0))
    (hNhseq : Tendsto Nh atTop (𝓝 (Nh 0)))
    (hNseq : TendstoUniformlyOn (fun n => scalarBoundaryRow hε (N n))
      (scalarBoundaryRow hε (N 0)) atTop (Ici 0))
    (hfloor : ∀ n (S : Ici (0 : ℝ)) u v, ρ ≤ (X n S).1 u v 0)
    (hR : ∀ n u, ρ ≤ Z n u 0)
    (hA : ∀ n t, T₀ ≤ t → ∀ u,
      Alo ≤ waveAmplitude (renormalizedWaveRow hε k (X n) t) u ∧
        waveAmplitude (renormalizedWaveRow hε k (X n) t) u ≤ Ahi)
    (hAh : ∀ n u, Alo ≤ waveAmplitude (Z n) u ∧ waveAmplitude (Z n) u ≤ Ahi) :
    HasCompactifiedGeometry hε k X N := by
  let hXc := fun n => renormalizedWaveRow_continuousOn (k := k) hε (X n) (hX n)
  let hNc := fun n => scalarBoundaryRow_continuousOn hε (N n) (hN n)
  let G := fun n => compactifiedTimeTrace (hXc n) (hZ n)
  let Nu := fun n => compactifiedTimeTrace (hNc n) (hNh n)
  let Rmap : C(C(Icc ε U, WaveVector), C(Icc ε U, ℝ)) := ⟨waveRadius, waveRadius.continuous⟩
  let R := fun n => Rmap.comp (G n)
  let A := fun n => waveAmplitude.comp (G n)
  have hG := compactifiedTimeTrace_tendsto hXc hZ (hXc 0) (hZ 0) hXseq hZseq
  have hNu := compactifiedTimeTrace_tendsto hNc hNh (hNc 0) (hNh 0) hNseq hNhseq
  refine ⟨R, A, Nu, ?_, ?_,
    (ContinuousMap.continuous_postcomp Rmap).tendsto (G 0) |>.comp hG,
    (ContinuousMap.continuous_postcomp waveAmplitude).tendsto (G 0) |>.comp hG,
    hNu, T₀, ρ, Alo, Ahi, hT₀, hρ, hAlo, hAhi, ?_⟩
  · intro n S t ht htS u
    have hGfinite : G n (ENNReal.ofReal t) = renormalizedWaveRow hε k (X n) t :=
      compactifiedTimeTrace_ofReal (hXc n) (hZ n) ht
    have hNfinite : Nu n (ENNReal.ofReal t) = scalarBoundaryRow hε (N n) t :=
      compactifiedTimeTrace_ofReal (hNc n) (hNh n) ht
    change waveRadius (G n (ENNReal.ofReal t)) u = _ ∧
      waveAmplitude (G n (ENNReal.ofReal t)) u = _ ∧ Nu n (ENNReal.ofReal t) u = _
    rw [hGfinite, hNfinite]
    refine ⟨?_, waveAmplitude_renormalizedWaveRow_apply hε (X n) (hX n) S ht htS u,
      scalarBoundaryRow_apply hε (N n) (hN n) S ht htS u⟩
    change renormalizedWaveRow hε k (X n) t u 0 = _
    rw [renormalizedWaveRow_apply hε (X n) (hX n) S ht htS]
    simp
  · intro n
    change Tendsto _ atTop (𝓝 (waveRadius (G n ⊤))) ∧
      Tendsto _ atTop (𝓝 (waveAmplitude (G n ⊤))) ∧ Tendsto _ atTop (𝓝 (Nu n ⊤))
    simp only [G, Nu, compactifiedTimeTrace_top]
    exact ⟨waveRadius.continuous.tendsto (Z n) |>.comp (hZ n),
      waveAmplitude.continuous.tendsto (Z n) |>.comp (hZ n), hNh n⟩
  · intro n t ht u
    change ρ ≤ waveRadius (G n t) u ∧ Alo ≤ waveAmplitude (G n t) u ∧ waveAmplitude (G n t) u ≤ Ahi
    by_cases htTop : t = ⊤
    · subst t
      rw [show G n ⊤ = Z n from compactifiedTimeTrace_top (hXc n) (hZ n)]
      exact ⟨hR n u, hAh n u⟩
    · rw [show G n t = renormalizedWaveRow hε k (X n) t.toReal from
        compactifiedTimeTrace_finite (hXc n) (hZ n) htTop]
      refine ⟨?_, hA n t.toReal ((ENNReal.ofReal_le_iff_le_toReal htTop).1 ht) u⟩
      change ρ ≤ renormalizedWaveRow hε k (X n) t.toReal u 0
      rw [renormalizedWaveRow_apply hε (X n) (hX n)
        ⟨t.toReal, ENNReal.toReal_nonneg⟩ ENNReal.toReal_nonneg le_rfl]
      simpa using hfloor n ⟨t.toReal, ENNReal.toReal_nonneg⟩
        ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t.toReal, ENNReal.toReal_nonneg, le_rfl⟩

end CauchyHorizon
