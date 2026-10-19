import CauchyHorizon.Characteristic.EarlyRadiationKernel
import CauchyHorizon.Reduced.SpatialRadiation

/-! The mixed early envelope includes the finite band and all vertical histories. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.early_moving_radiation_energy {U V R e Λ φ₀ k ρ N L Lᵧ α : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hk : 0 < k) (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hLᵧ : 0 ≤ Lᵧ)
    (hsmall : L * Lᵧ * N ≤ 2 * k ^ 2 * ρ ^ 2) (hα : 1 ≤ α)
    (l : Icc 0 V) (w : C(Icc 0 V, ℝ)) (hw0 : ∀ v, 0 ≤ w v) (hw : Antitone w)
    (A : C(Icc 0 V, ℝ)) (hA0 : ∀ v, 0 ≤ A v) :
    let W : C(Icc 0 V, ℝ) := ⟨fun v => w (projIcc 0 V hV ((v : ℝ) / α)), by fun_prop⟩
    let hW0 := fun v : Icc 0 V => hw0 (projIcc 0 V hV ((v : ℝ) / α))
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
    (∀ (u : Icc 0 U) (b : Icc 0 V), w b < (u : ℝ) → (u : ℝ) ≤ W b →
      ∃ (z : Icc 0 U) (hzu : z ≤ u) (T : C(Icc (z : ℝ) u, Icc 0 V)),
        (z : ℝ) ≤ w b ∧
        let τ := fun t => T (projIcc (z : ℝ) u hzu t)
        τ z = b ∧ l ≤ τ u ∧ (∀ t ∈ Icc (z : ℝ) u, τ t ≤ b) ∧
        (∀ t ∈ Icc (z : ℝ) u, ν (projIcc 0 U hU t) (τ t) < 0) ∧
        (∀ t ∈ Icc (z : ℝ) u, -Lᵧ ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧
          x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0) ∧
        (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
          (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) ∧
        (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b, ρ ≤ x.1 (projIcc 0 U hU t) v 0) ∧
        (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b,
          |ν (projIcc 0 U hU t) v| ≤ N * (-ν (projIcc 0 U hU t) (τ t)) *
            Real.exp (-(2 * k) * ((v : ℝ) - τ t))) ∧
        (∀ t ∈ Icc (z : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
          L * Real.exp (-(2 * k) * ((b : ℝ) - τ t))) ∧
        (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
          Real.exp (k * τ t) * |x.1 (projIcc 0 U hU t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
            (-ν (projIcc 0 U hU t) (τ t)) * A (τ t))) →
      let H := movingSpatialRadiationEnvelope w hw0 0 k 0 x
      let M := movingSpatialRadiationEnvelope W hW0 0 k 0 x
      (∀ v, H v ≤ M v) ∧
      (∀ v, v ≤ l → M v = H v) ∧
      (∀ v, l ≤ v → M v ≤ H v + L * Lᵧ / ρ * causalExpIntegralFrom hV l k A v +
        L * Lᵧ * N / (4 * k * ρ ^ 2) * causalExpIntegralFrom hV l k M v) ∧
      (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
        8 * (∫ t in (0 : ℝ)..V, (H (projIcc 0 V hV t)) ^ 2) +
          8 * (L * Lᵧ / ρ / k) ^ 2 * ∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2 := by
  let W : C(Icc 0 V, ℝ) := ⟨fun v => w (projIcc 0 V hV ((v : ℝ) / α)), by fun_prop⟩
  have hW0 (v) : 0 ≤ W v := hw0 _
  let H := movingSpatialRadiationEnvelope w hw0 0 k 0 x
  let M := movingSpatialRadiationEnvelope W hW0 0 k 0 x
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hW : Antitone W := fun v b hvb => hw
    (monotone_projIcc hV (div_le_div_of_nonneg_right hvb hα0.le))
  have hwW (v : Icc 0 V) : w v ≤ W v := by
    apply hw
    have hh := monotone_projIcc hV (div_le_self v.property.1 hα)
    simpa only [projIcc_of_mem hV v.property] using hh
  have hM0 (v) : 0 ≤ M v := norm_nonneg (movingSpatialRadiationRows W hW0 0 k 0 x v)
  have hmajor (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ W v) :
      Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v := by
    simpa only [zero_mul, sub_zero] using
      (movingSpatialRadiationEnvelope_le_iff (a := 0) (k := k) (σ := 0) hU W hW0 x v).1 le_rfl u hu
  have hband (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ w v) :
      Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ H v := by
    simpa only [zero_mul, sub_zero] using
      (movingSpatialRadiationEnvelope_le_iff (a := 0) (k := k) (σ := 0) hU w hw0 x v).1 le_rfl u hu
  dsimp only
  intro hchart
  have hHM (v : Icc 0 V) : H v ≤ M v := by
    apply (movingSpatialRadiationEnvelope_le_iff hU w hw0 x v).2
    intro u hu
    simpa only [zero_mul, sub_zero] using hmajor u v (hu.trans (hwW v))
  have hcausal (b : Icc 0 V) (hlb : l ≤ b) :
      M b ≤ H b + L * Lᵧ / ρ * causalExpIntegralFrom hV l k A b +
        L * Lᵧ * N / (4 * k * ρ ^ 2) * causalExpIntegralFrom hV l k M b := by
    apply (movingSpatialRadiationEnvelope_le_iff hU W hW0 x b).2
    intro u hu
    simp only [zero_mul, sub_zero]
    by_cases hub : (u : ℝ) ≤ w b
    · have hQa : 0 ≤ causalExpIntegralFrom hV l k A b := intervalIntegral.integral_nonneg hlb
        (fun t _ => mul_nonneg (Real.exp_pos _).le (hA0 _))
      have hQm : 0 ≤ causalExpIntegralFrom hV l k M b := intervalIntegral.integral_nonneg hlb
        (fun t _ => mul_nonneg (Real.exp_pos _).le (hM0 _))
      have hfa : 0 ≤ L * Lᵧ / ρ * causalExpIntegralFrom hV l k A b := by positivity
      have hfm : 0 ≤ L * Lᵧ * N / (4 * k * ρ ^ 2) * causalExpIntegralFrom hV l k M b := by positivity
      linarith only [hband u b hub, hfa, hfm]
    · obtain ⟨z, hzu, T, hzw, hTb, hlτ, hTbound, hn, he, hd, hr, hν, hlam, hA⟩ :=
        hchart u b (not_le.1 hub) hu
      have hh := hx.early_radiation_causal hU hV hUR hp hf hk hρ hN hL A M hA0 hM0
        l z u hzu b T hlτ hTb hTbound hn he hd hr hν hlam (fun t ht v hv => by
          apply hmajor
          have htU : t ∈ Icc 0 U := ⟨z.property.1.trans ht.1, ht.2.trans u.property.2⟩
          rw [projIcc_of_mem hU htU]
          exact (ht.2.trans hu).trans (hW hv.2)) hA
      have htriangle := mul_le_mul_of_nonneg_left
        (abs_sub_le (x.1 u b 0 * x.2.1 u b 1) (x.1 z b 0 * x.2.1 z b 1) 0) (Real.exp_pos (k * b)).le
      simp only [sub_zero, mul_add] at htriangle
      linarith only [hh, htriangle, hband z b hzw]
  have hpre (b : Icc 0 V) (hbl : b ≤ l) : M b = H b := by
    apply le_antisymm _ (hHM b)
    by_cases hbe : b = l
    · subst b
      simpa only [causalExpIntegralFrom, intervalIntegral.integral_same, mul_zero, add_zero] using
        hcausal l le_rfl
    · apply (movingSpatialRadiationEnvelope_le_iff hU W hW0 x b).2
      intro u hu
      simp only [zero_mul, sub_zero]
      by_cases hub : (u : ℝ) ≤ w b
      · exact hband u b hub
      · obtain ⟨z, hzu, T, _hzw, _hTb, hlτ, hTbound, _⟩ := hchart u b (not_le.1 hub) hu
        exact (hbe (le_antisymm hbl (hlτ.trans (hTbound u ⟨hzu, le_rfl⟩)))).elim
  refine ⟨hHM, hpre, hcausal, ?_⟩
  have hpost := early_radiation_energy hV hk hρ hN hL hLᵧ hsmall l H A M hM0 hcausal
  have hmc : Continuous (fun t => (M (projIcc 0 V hV t)) ^ 2) := by fun_prop
  have hhc : Continuous (fun t => (H (projIcc 0 V hV t)) ^ 2) := by fun_prop
  have hjoinM := intervalIntegral.integral_add_adjacent_intervals
    (hmc.intervalIntegrable (μ := volume) 0 l) (hmc.intervalIntegrable (l : ℝ) V)
  have hjoinH := intervalIntegral.integral_add_adjacent_intervals
    (hhc.intervalIntegrable (μ := volume) 0 l) (hhc.intervalIntegrable (l : ℝ) V)
  have hpreE : (∫ t in (0 : ℝ)..l, (M (projIcc 0 V hV t)) ^ 2) =
      ∫ t in (0 : ℝ)..l, (H (projIcc 0 V hV t)) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le l.property.1] at ht
    dsimp only
    rw [hpre (projIcc 0 V hV t)
      (by rw [projIcc_of_mem hV ⟨ht.1, ht.2.trans l.property.2⟩]; exact ht.2)]
  have hpre0 : 0 ≤ ∫ t in (0 : ℝ)..l, (H (projIcc 0 V hV t)) ^ 2 :=
    intervalIntegral.integral_nonneg l.property.1 (fun _ _ => sq_nonneg _)
  linarith only [hpost, hjoinM, hjoinH, hpreE, hpre0]

end CauchyHorizon
