import CauchyHorizon.Characteristic.RadiationComparison
import CauchyHorizon.Characteristic.RadiationPhase
import CauchyHorizon.Reduced.MassCoefficient
import CauchyHorizon.Characteristic.MassDensityComparison
import CauchyHorizon.Characteristic.MassResponse
import CauchyHorizon.Characteristic.MassProfile

open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction

namespace CauchyHorizon.Tests

-- Opposite phase signs retain the squared displacement and the inverse time Jacobian.
example (P Q : ℝ →ᵇ ℝ) (hd : ∀ x, HasDerivAt P (Q x) x)
    (hQi : Integrable (fun x => Q x ^ 2)) :
    MemLp (fun v => P (2 * v + 3) - P (2 * v - 1)) 2 (volume.restrict (Ici 0)) ∧
      (∫ v in Ici (0 : ℝ), (P (2 * v + 3) - P (2 * v - 1)) ^ 2) ≤ 8 * ∫ x, Q x ^ 2 := by
  have h := phaseChange_l2_halfline (l := 0) (η := 2) (ε := 4) (by norm_num) (by norm_num)
    (show ContinuousOn (fun v : ℝ => 2 * v - 1) (Ici 0) by fun_prop)
    (show ContinuousOn (fun v : ℝ => 2 * v + 3) (Ici 0) by fun_prop)
    (fun v _ => by simpa using ((hasDerivAt_id v).const_mul 2).sub_const 1)
    (fun v _ => by simpa using ((hasDerivAt_id v).const_mul 2).add_const 3)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun v _ => by rw [show 2 * v + 3 - (2 * v - 1) = 4 by ring]; norm_num)
    P.continuous Q.continuous hd hQi
  norm_num at h
  exact h

-- The unshifted comparison uses the same actual family and the entire original half-line.
example {U ε k c a ℓ : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (P Q : ℕ → ℝ →ᵇ ℝ)
    (hd : ∀ n x, HasDerivAt (P n) (Q n x) x)
    (hQi : ∀ n, Integrable (fun x => Q n x ^ 2))
    (hQlim : Tendsto (fun n => ∫ x, Q n x ^ 2) atTop (𝓝 0))
    (hF : (∀ n, MemLp (radiationComparisonRow hε k c X (fun n v => P n (a * v + ℓ)) n)
        2 (volume.restrict (Ici 0))) ∧
      Tendsto (fun n => ∫ v in Ici (0 : ℝ),
        ‖radiationComparisonRow hε k c X (fun n v => P n (a * v + ℓ)) n v‖ ^ 2)
        atTop (𝓝 0)) :
    (∀ n, MemLp (radiationComparisonRow hε k c X (fun n v => P n (a * v)) n)
        2 (volume.restrict (Ici 0))) ∧
      Tendsto (fun n => ∫ v in Ici (0 : ℝ),
        ‖radiationComparisonRow hε k c X (fun n v => P n (a * v)) n v‖ ^ 2)
        atTop (𝓝 0) := by
  simpa only [add_zero] using radiation_comparison_phase hε ha X P Q hd hQi hQlim hF 0

-- Restriction retains the same physical ray for both solutions and the model.
example {U ε : ℝ} (hε : 0 ≤ ε) (k c : ℝ)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (P : ℕ → ℝ → ℝ)
    (n : ℕ) (t : ℝ) (u : Icc ε U) :
    radiationComparisonRow hε k c X P n t u =
      radiationRow k (X n) t ⟨u, hε.trans u.property.1, u.property.2⟩ -
        radiationRow k (X 0) t ⟨u, hε.trans u.property.1, u.property.2⟩ - c * P n t := rfl

-- A repeated actual solution with zero model has identically zero mixed error.
example {U ε : ℝ} (hε : 0 ≤ ε) (k c : ℝ)
    (X : (V : Ici (0 : ℝ)) → WaveState U V) (n : ℕ) (t : ℝ) :
    radiationComparisonRow hε k c (fun _ => X) (fun _ _ => 0) n t = 0 := by
  ext u
  simp only [radiationComparisonRow, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    mul_zero, sub_self, ContinuousMap.zero_apply]

-- The nonnegative-weight endpoint gives a bounded tail without claiming decay.
example {U k β T₀ E : ℝ} (hU : 0 ≤ U)
    (X : (V : Ici (0 : ℝ)) → WaveState U V) (g : ℝ → ℝ)
    (hD : LateRadiationHalfline hU k β T₀ 0 E X g) :
    ∃ D : C(ℝ, C(Icc (0 : ℝ) U, ℝ)),
      (∀ t u,
        let z := projIcc 0 U hU (g (max T₀ (t / (1 + β))))
        D t u = radiationRow k X t (max z u) - radiationRow k X t z) ∧
      ∀ T : ℝ, 0 ≤ T → MemLp D 2 (volume.restrict (Ici T)) ∧
        (∫ t in Ici T, ‖D t‖ ^ 2) ≤ E := by
  obtain ⟨D, heq, _hi, _hE, htail⟩ := hD
  refine ⟨D, heq, ?_⟩
  intro T hT
  simpa only [mul_zero, neg_zero, zero_mul, Real.exp_zero, one_mul] using htail T hT

-- The coefficient is the physical negative radial derivative divided by the amplitude.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (N : C(K, ℝ)) (Z : C(K, WaveVector)) (u : K) :
    waveMassCoefficient (N, Z) u = -2 * N u / waveAmplitude Z u := by
  change -2 * (N u * Real.exp (-Z u 2)) = -2 * N u / Real.exp (Z u 2)
  rw [Real.exp_neg, div_eq_mul_inv, mul_assoc]

-- A zero limiting radial derivative gives zero coefficient, not strict positivity.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (Z : C(K, WaveVector)) : waveMassCoefficient (0, Z) = 0 := by
  ext u
  simp only [waveMassCoefficient, ContinuousMap.coe_mk, ContinuousMap.zero_apply, zero_mul, smul_zero]

-- At fixed radial derivative the logarithmic geometry has a uniform Lipschitz factor.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (N : C(K, ℝ)) (f g : C(K, WaveVector)) {A : ℝ} (hA : 0 < A)
    (hf : ∀ u, A ≤ waveAmplitude f u) (hg : ∀ u, A ≤ waveAmplitude g u) :
    ‖waveMassCoefficient (N, f) - waveMassCoefficient (N, g)‖ ≤
      (2 / A) * (‖N‖ * ‖f - g‖) := by
  simpa only [sub_self, norm_zero, zero_add] using
    waveMassCoefficient_norm_sub_le (N := N) (M := N) hA le_rfl hf hg

-- The exact model still leaves a signed reference cross term in the density.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (C R H : C(K, ℝ)) :
    C * (R + H) ^ 2 - C * R ^ 2 - C * H ^ 2 = (2 : ℝ) • (C * (R * H)) := by
  ext u
  simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
    ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

-- No nonempty-space hypothesis is needed for the quadratic norm estimate.
example {K : Type*} [TopologicalSpace K] [CompactSpace K] (F : C(K, ℝ)) :
    ‖F ^ 2‖ ≤ ‖F‖ ^ 2 := by
  simpa only [pow_two] using norm_mul_le F F

-- The mass-density conclusion retains integrability of every actual flux.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {C R H : ℕ → ℝ → C(K, ℝ)} (h : MassDensityLimit C R H) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ n, IntegrableOn (fun t => C n t * R n t ^ 2) (Ici T) := by
  obtain ⟨T, hT, _Q, _hQ, hi, _hl⟩ := h
  exact ⟨T, hT, fun n => (hi n).1⟩

-- Unit time scaling retains exactly the squared amplitude factor.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (Q : C(K, ℝ)) (P : ℝ → ℝ) (c T t : ℝ) :
    (∫ s in T..t, Q * (ContinuousMap.const K (c * P s)) ^ 2) =
      (c ^ 2 * ∫ s in T..t, P s ^ 2) • Q := by
  simpa only [one_mul, add_zero, div_one] using
    (mass_profile_integrals (by norm_num : (0 : ℝ) < 1) Q P c 0 T t).1

-- The horizon formula has the same positive time Jacobian as finite endpoints.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (Q : C(K, ℝ)) (P : ℝ → ℝ) (T : ℝ) :
    (∫ s in Ici T, Q * (ContinuousMap.const K (P (2 * s))) ^ 2) =
      ((1 / 2 : ℝ) * ∫ s in Ici (2 * T), P s ^ 2) • Q := by
  simpa only [one_mul, one_pow, add_zero] using
    (mass_profile_integrals (by norm_num : (0 : ℝ) < 2) Q P 1 0 T T).2

-- A zero model and repeated constant mass give a zero response, without a sign claim.
example {K : Type*} [TopologicalSpace K] [CompactSpace K] (Q m : C(K, ℝ)) :
    MassResponseLimit (fun _ _ => Q) (fun _ _ => 0) (fun _ _ => m) := by
  refine ⟨0, le_rfl, Q, tendsto_const_nhds, (fun _ => m), (fun _ => tendsto_const_nhds), ?_⟩
  intro d hd
  exact Eventually.of_forall (fun _ => ⟨fun _ _ => by simpa using hd, by simpa using hd⟩)

-- Removing the lower endpoint does not turn a zero profile into a positive response.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (m Γ : C(K, ℝ)) (a : ℝ) (ℓ : ℕ → ℝ) :
    MassProfileLimit (fun _ _ => m) Γ a ℓ (fun _ _ => 0) := by
  refine ⟨0, le_rfl, (fun _ => m), (fun _ => tendsto_const_nhds), ?_⟩
  intro d hd
  exact Eventually.of_forall (fun _ => ⟨fun _ _ => by simpa using hd, by simpa using hd⟩)

-- With nonzero transmission, strict positivity still requires a strict radial sign.
example {a A c N Γ : ℝ} (ha : 0 < a) (hA : 0 < A) (hc : c ≠ 0)
    (hΓ : Γ = (-2 * N / (a * A)) * c ^ 2) : 0 < Γ ↔ N < 0 := by
  rw [hΓ]
  constructor
  · intro hpos
    by_contra hn
    have hn0 : 0 ≤ N := le_of_not_gt hn
    have hle : (-2 * N / (a * A)) * c ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (by linarith only [hn0]) (mul_pos ha hA).le) (sq_nonneg c)
    exact (not_le_of_gt hpos) hle
  · intro hn
    exact mul_pos (div_pos (by linarith only [hn]) (mul_pos ha hA)) (sq_pos_of_ne_zero hc)

end CauchyHorizon.Tests
