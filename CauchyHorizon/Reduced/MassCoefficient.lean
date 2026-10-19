import CauchyHorizon.Reduced.AmplitudeTrace
import CauchyHorizon.Reduced.RadialBoundary
import CauchyHorizon.Reduced.RadiationHalfline

/-! The mass-density coefficient in the actual renormalized geometry. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

noncomputable def waveMassCoefficient {K : Type*} [TopologicalSpace K] [CompactSpace K] :
    C(C(K, ℝ) × C(K, WaveVector), C(K, ℝ)) :=
  ⟨fun p => (-2 : ℝ) • (p.1 * waveAmplitude (-p.2)), by
    exact (continuous_fst.mul (waveAmplitude.continuous.comp continuous_snd.neg)).const_smul (-2 : ℝ)⟩

noncomputable def massCoefficientRow {U ε : ℝ} (hε : 0 ≤ ε) (k : ℝ)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ))) (t : ℝ) : C(Icc ε U, ℝ) :=
  waveMassCoefficient (scalarBoundaryRow hε N t, renormalizedWaveRow hε k X t)

def MassCoefficientControl {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (C : ℕ → ℝ → C(K, ℝ)) : Prop :=
  ∃ T M L η : ℝ, 0 ≤ T ∧ 0 ≤ M ∧ 0 ≤ L ∧ 0 < η ∧ ∃ Q : ℕ → C(K, ℝ),
    (∀ n, Tendsto (C n) atTop (𝓝 (Q n))) ∧
    (∀ n t, T ≤ t → ‖C n t‖ ≤ M ∧ ‖C n t - Q n‖ ≤ L * Real.exp (-η * t)) ∧
    (∀ n u, 0 ≤ Q n u) ∧ Tendsto Q atTop (𝓝 (Q 0)) ∧
      TendstoUniformlyOn C (C 0) atTop (Ici T)

theorem waveMassCoefficient_norm_sub_le {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {N M : C(K, ℝ)} {f g : C(K, WaveVector)} {A L : ℝ}
    (hA : 0 < A) (hM : ‖M‖ ≤ L)
    (hf : ∀ u, A ≤ waveAmplitude f u) (hg : ∀ u, A ≤ waveAmplitude g u) :
    ‖waveMassCoefficient (N, f) - waveMassCoefficient (M, g)‖ ≤
      (2 / A) * (‖N - M‖ + L * ‖f - g‖) := by
  have hAf (u : K) : waveAmplitude (-f) u ≤ 1 / A := by
    change Real.exp (-f u 2) ≤ 1 / A
    rw [Real.exp_neg]
    simpa only [one_div, waveAmplitude, ContinuousMap.coe_mk, ContinuousMap.comp_apply] using
      one_div_le_one_div_of_le hA (hf u)
  have hAg (u : K) : waveAmplitude (-g) u ≤ 1 / A := by
    change Real.exp (-g u 2) ≤ 1 / A
    rw [Real.exp_neg]
    simpa only [one_div, waveAmplitude, ContinuousMap.coe_mk, ContinuousMap.comp_apply] using
      one_div_le_one_div_of_le hA (hg u)
  have hAfN : ‖waveAmplitude (-f)‖ ≤ 1 / A := (ContinuousMap.norm_le _ (by positivity)).2 (by
    intro u
    rw [Real.norm_eq_abs, abs_of_pos (show 0 < waveAmplitude (-f) u from Real.exp_pos _)]
    exact hAf u)
  have hdiff : ‖waveAmplitude (-f) - waveAmplitude (-g)‖ ≤ (1 / A) * ‖f - g‖ := by
    have hh := waveAmplitude_norm_sub_le (one_div_pos.2 hA) hAf hAg
    simpa only [show -f - -g = -(f - g) by abel, norm_neg] using hh
  have hid : waveMassCoefficient (N, f) - waveMassCoefficient (M, g) =
      (-2 : ℝ) • ((N - M) * waveAmplitude (-f) + M * (waveAmplitude (-f) - waveAmplitude (-g))) := by
    ext u
    simp only [waveMassCoefficient, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply, smul_eq_mul]
    ring
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]
  have hL : 0 ≤ L := (norm_nonneg M).trans hM
  calc
    _ ≤ 2 * (‖N - M‖ * ‖waveAmplitude (-f)‖ + ‖M‖ * ‖waveAmplitude (-f) - waveAmplitude (-g)‖) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) (by norm_num)
    _ ≤ 2 * (‖N - M‖ * (1 / A) + L * ((1 / A) * ‖f - g‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hAfN (norm_nonneg _))
        (mul_le_mul hM hdiff (norm_nonneg _) hL)) (by norm_num)
    _ = _ := by ring

theorem massCoefficientRow_apply {U ε k : ℝ} (hε : 0 ≤ ε)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)))
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hN : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      N S u v = N T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (V : Ici (0 : ℝ)) {t : ℝ} (ht : 0 ≤ t) (htV : t ≤ V) (u : Icc ε U) :
    let w : Icc 0 U := ⟨u, hε.trans u.property.1, u.property.2⟩
    let v : Icc 0 (V : ℝ) := ⟨t, ht, htV⟩
    massCoefficientRow hε k X N t u = -2 * N V w v /
        (Real.exp (2 * k * t) * Real.exp ((X V).1 w v 2)) ∧
      massCoefficientRow hε k X N t u * (radiationRow k X t w) ^ 2 =
        -2 * ((X V).1 w v 0) ^ 2 * N V w v * Real.exp (-(X V).1 w v 2) * ((X V).2.1 w v 1) ^ 2 := by
  dsimp only
  have hc : massCoefficientRow hε k X N t u =
      -2 * N V ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htV⟩ *
        Real.exp (-((X V).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htV⟩ 2 + 2 * k * t)) := by
    change -2 * (scalarBoundaryRow hε N t u * Real.exp (-renormalizedWaveRow hε k X t u 2)) = _
    rw [scalarBoundaryRow_apply hε N hN V ht htV u, renormalizedWaveRow_apply hε X hX V ht htV u 2]
    simp only [ite_true, mul_assoc]
  constructor
  · rw [hc, Real.exp_neg, Real.exp_add]
    simp only [div_eq_mul_inv, mul_comm (Real.exp _) (Real.exp _)]
  · rw [hc, radiationRow_eq X hX V htV]
    simp only [spatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
      projIcc_of_mem V.property (show t ∈ Icc 0 (V : ℝ) from ⟨ht, htV⟩), zero_mul, sub_zero]
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
      show 2 * k * t = k * t + k * t by ring, Real.exp_add]
    field_simp [Real.exp_ne_zero]

end CauchyHorizon
