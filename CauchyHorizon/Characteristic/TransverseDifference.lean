import CauchyHorizon.Characteristic.EarlyRadiationKernel
import CauchyHorizon.Reduced.SpatialRadiation

/-! The actual transverse difference uses the already bounded total-field energy. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon

noncomputable def transverseRadiationRows {U V : ℝ} (k : ℝ) (x : WaveState U V)
    (z w : C(Icc (0 : ℝ) V, Icc (0 : ℝ) U)) : C(Icc (0 : ℝ) V, C(Icc (0 : ℝ) U, ℝ)) :=
  (⟨fun q : Icc (0 : ℝ) V × Icc (0 : ℝ) U =>
    let u := max (z q.1) (min q.2 (w q.1))
    Real.exp (k * q.1) *
      (x.1 u q.1 0 * x.2.1 u q.1 1 - x.1 (z q.1) q.1 0 * x.2.1 (z q.1) q.1 1),
    by fun_prop⟩ : C(Icc (0 : ℝ) V × Icc (0 : ℝ) U, ℝ)).curry

set_option maxHeartbeats 1600000 in
theorem IsWaveIntegral.transverse_radiation_difference_energy {U V R e Λ φ₀ k ρ N L Lᵧ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hk : 0 < k) (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hLᵧ : 0 ≤ Lᵧ)
    (l b₀ : Icc 0 V) (hl₀ : l ≤ b₀)
    (z w : C(Icc (0 : ℝ) V, Icc (0 : ℝ) U)) (hzw : ∀ b, b₀ ≤ b → z b ≤ w b)
    (A : C(Icc 0 V, ℝ)) (hA0 : ∀ v, 0 ≤ A v) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
    (∀ (b : Icc 0 V), b₀ ≤ b → ∀ (u : Icc 0 U) (hzu : z b < u), u ≤ w b →
      ∃ T : C(Icc (z b : ℝ) u, Icc 0 V),
        let τ := fun t => T (projIcc (z b : ℝ) u hzu.le t)
        τ (z b) = b ∧ l ≤ τ u ∧ (∀ t ∈ Icc (z b : ℝ) u, τ t ≤ b) ∧
        (∀ t ∈ Icc (z b : ℝ) u, ν (projIcc 0 U hU t) (τ t) < 0) ∧
        (∀ t ∈ Icc (z b : ℝ) u, -Lᵧ ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧
          x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0) ∧
        (∀ t ∈ Ioo (z b : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
          (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) ∧
        (∀ t ∈ Icc (z b : ℝ) u, ∀ v ∈ Icc (τ t) b, ρ ≤ x.1 (projIcc 0 U hU t) v 0) ∧
        (∀ t ∈ Icc (z b : ℝ) u, ∀ v ∈ Icc (τ t) b,
          |ν (projIcc 0 U hU t) v| ≤ N * (-ν (projIcc 0 U hU t) (τ t)) *
            Real.exp (-(2 * k) * ((v : ℝ) - τ t))) ∧
        (∀ t ∈ Icc (z b : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
          L * Real.exp (-(2 * k) * ((b : ℝ) - τ t))) ∧
        (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z b : ℝ) u →
          Real.exp (k * τ t) * |x.1 (projIcc 0 U hU t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
            (-ν (projIcc 0 U hU t) (τ t)) * A (τ t))) →
      let M := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 V) U) (fun _ => hU) 0 k 0 x
      let D := transverseRadiationRows k x z w
      (∀ b : Icc 0 V, b₀ ≤ b →
        ‖D b‖ ≤ L * Lᵧ / ρ * causalExpIntegralFrom hV l k A b +
          L * Lᵧ * N / (4 * k * ρ ^ 2) * causalExpIntegralFrom hV l k M b) ∧
      (∫ t in (b₀ : ℝ)..V, ‖D (projIcc 0 V hV t)‖ ^ 2) ≤
        2 * (L * Lᵧ / (ρ * k)) ^ 2 * (∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2) +
          2 * (L * Lᵧ * N / (4 * k ^ 2 * ρ ^ 2)) ^ 2 *
            ∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  intro ν hchart M D
  let CA := L * Lᵧ / ρ
  let CM := L * Lᵧ * N / (4 * k * ρ ^ 2)
  have hM0 (v : Icc 0 V) : 0 ≤ M v := by
    change 0 ≤ ‖movingSpatialRadiationRows (ContinuousMap.const (Icc 0 V) U) (fun _ => hU) 0 k 0 x v‖
    exact norm_nonneg _
  have hM (u : Icc 0 U) (v : Icc 0 V) :
      Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v := by
    simpa only [zero_mul, sub_zero] using
      (movingSpatialRadiationEnvelope_le_iff (a := 0) (k := k) (σ := 0) hU (ContinuousMap.const (Icc 0 V) U)
        (fun _ => hU) x v).1 le_rfl u u.property.2
  have hbound (b : Icc 0 V) (h₀b : b₀ ≤ b) :
      ‖D b‖ ≤ CA * causalExpIntegralFrom hV l k A b + CM * causalExpIntegralFrom hV l k M b := by
    have hlb : l ≤ b := hl₀.trans h₀b
    have : Nonempty (Icc (0 : ℝ) U) := ⟨⟨0, le_rfl, hU⟩⟩
    apply (ContinuousMap.norm_le_of_nonempty (D b)).2
    intro q
    let u := max (z b) (min q (w b))
    have hzu : z b ≤ u := le_max_left _ _
    have huw : u ≤ w b := max_le (hzw b h₀b) (min_le_right _ _)
    change ‖Real.exp (k * b) * (x.1 u b 0 * x.2.1 u b 1 - x.1 (z b) b 0 * x.2.1 (z b) b 1)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rcases eq_or_lt_of_le hzu with hu | hu
    · rw [← hu, sub_self, abs_zero, mul_zero]
      have hQA : 0 ≤ causalExpIntegralFrom hV l k A b := intervalIntegral.integral_nonneg hlb
        (fun _ _ => mul_nonneg (Real.exp_pos _).le (hA0 _))
      have hQM : 0 ≤ causalExpIntegralFrom hV l k M b := intervalIntegral.integral_nonneg hlb
        (fun _ _ => mul_nonneg (Real.exp_pos _).le (hM0 _))
      dsimp only [CA, CM]
      positivity
    · obtain ⟨T, hTz, hlT, hTb, hn, he, hd, hr, hν, hlam, hA⟩ := hchart b h₀b u hu huw
      exact hx.early_radiation_causal hU hV hUR hp hf hk hρ hN hL A M hA0 hM0
        l (z b) u hu.le b T hlT hTz hTb hn he hd hr hν hlam (fun _ _ v _ => hM _ v) hA
  refine ⟨hbound, ?_⟩
  obtain ⟨hQA, hEA⟩ := causalExpIntegralFrom_energy hV hk l.property.1 l.property.2 le_rfl A
  obtain ⟨hQM, hEM⟩ := causalExpIntegralFrom_energy hV hk l.property.1 l.property.2 le_rfl M
  let QA := fun t => causalExpIntegralFrom hV l k A (projIcc 0 V hV t)
  let QM := fun t => causalExpIntegralFrom hV l k M (projIcc 0 V hV t)
  let F := fun t => ‖D (projIcc 0 V hV t)‖
  have hFc : Continuous F := (D.continuous.comp continuous_projIcc).norm
  have hQA2 : IntervalIntegrable (fun t => QA t ^ 2) volume b₀ V :=
    ((hQA.comp continuous_projIcc).pow 2).intervalIntegrable _ _
  have hQM2 : IntervalIntegrable (fun t => QM t ^ 2) volume b₀ V :=
    ((hQM.comp continuous_projIcc).pow 2).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_mono_on (μ := volume) b₀.property.2
    ((hFc.pow 2).intervalIntegrable _ _) ((hQA2.const_mul (2 * CA ^ 2)).add (hQM2.const_mul (2 * CM ^ 2)))
    (fun t ht => by
      have htV : t ∈ Icc 0 V := ⟨b₀.property.1.trans ht.1, ht.2⟩
      have hh : F t ≤ CA * QA t + CM * QM t := hbound (projIcc 0 V hV t)
        (by rw [projIcc_of_mem hV htV]; exact ht.1)
      have hF0 : 0 ≤ F t := norm_nonneg _
      have hsq := (sq_le_sq₀ hF0 (hF0.trans hh)).2 hh
      change F t ^ 2 ≤ 2 * CA ^ 2 * QA t ^ 2 + 2 * CM ^ 2 * QM t ^ 2
      nlinarith only [hsq, sq_nonneg (CA * QA t - CM * QM t)])
  change (∫ t in (b₀ : ℝ)..V, F t ^ 2) ≤
    ∫ t in (b₀ : ℝ)..V, 2 * CA ^ 2 * QA t ^ 2 + 2 * CM ^ 2 * QM t ^ 2 at hsum
  rw [intervalIntegral.integral_add (hQA2.const_mul _) (hQM2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hsum
  have hAQ := intervalIntegral.integral_mono_interval (μ := volume) (show (l : ℝ) ≤ b₀ from hl₀)
    b₀.property.2 le_rfl (Filter.Eventually.of_forall (fun t => sq_nonneg (QA t)))
    (((hQA.comp continuous_projIcc).pow 2).intervalIntegrable _ _)
  have hMQ := intervalIntegral.integral_mono_interval (μ := volume) (show (l : ℝ) ≤ b₀ from hl₀)
    b₀.property.2 le_rfl (Filter.Eventually.of_forall (fun t => sq_nonneg (QM t)))
    (((hQM.comp continuous_projIcc).pow 2).intervalIntegrable _ _)
  have hAbound := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hAQ (sq_nonneg k)).trans hEA) (sq_nonneg (CA / k))
  have hMbound := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hMQ (sq_nonneg k)).trans hEM) (sq_nonneg (CM / k))
  have hcancel (C : ℝ) : (C / k) ^ 2 * k ^ 2 = C ^ 2 := by field_simp [hk.ne']
  rw [← mul_assoc, hcancel] at hAbound hMbound
  change CA ^ 2 * (∫ t in (b₀ : ℝ)..V, QA t ^ 2) ≤ _ at hAbound
  change CM ^ 2 * (∫ t in (b₀ : ℝ)..V, QM t ^ 2) ≤ _ at hMbound
  have hCA : CA / k = L * Lᵧ / (ρ * k) := by dsimp only [CA]; ring
  have hCM : CM / k = L * Lᵧ * N / (4 * k ^ 2 * ρ ^ 2) := by dsimp only [CM]; ring
  rw [hCA] at hAbound
  rw [hCM] at hMbound
  linarith only [hsum, hAbound, hMbound]

end CauchyHorizon
