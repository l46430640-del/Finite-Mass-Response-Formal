import CauchyHorizon.Characteristic.EarlyRadiation
import CauchyHorizon.Analysis.EarlyKernel
import CauchyHorizon.Reduced.RadiationEnergy

/-! The actual early radiation estimate with one causal exponential kernel. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem IsWaveIntegral.early_radiation_causal {U V R e Λ φ₀ k ρ N L Lᵧ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hk : 0 < k) (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (A M : C(Icc 0 V, ℝ)) (hA0 : ∀ v, 0 ≤ A v) (hM0 : ∀ v, 0 ≤ M v)
    (l : Icc 0 V) (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (T : C(Icc (z : ℝ) u, Icc 0 V)) :
    let τ := fun t => T (projIcc (z : ℝ) u hzu t)
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
    l ≤ τ u → τ z = b → (∀ t ∈ Icc (z : ℝ) u, τ t ≤ b) →
    (∀ t ∈ Icc (z : ℝ) u, ν (projIcc 0 U hU t) (τ t) < 0) →
    (∀ t ∈ Icc (z : ℝ) u, -Lᵧ ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧
      x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0) →
    (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
      (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b, ρ ≤ x.1 (projIcc 0 U hU t) v 0) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b,
      |ν (projIcc 0 U hU t) v| ≤ N * (-ν (projIcc 0 U hU t) (τ t)) *
        Real.exp (-(2 * k) * ((v : ℝ) - τ t))) →
    (∀ t ∈ Icc (z : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
      L * Real.exp (-(2 * k) * ((b : ℝ) - τ t))) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b,
      Real.exp (k * v) * |x.1 (projIcc 0 U hU t) v 0 * x.2.1 (projIcc 0 U hU t) v 1| ≤ M v) →
    (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      Real.exp (k * τ t) * |x.1 (projIcc 0 U hU t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
        (-ν (projIcc 0 U hU t) (τ t)) * A (τ t)) →
      Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1 - x.1 z b 0 * x.2.1 z b 1| ≤
          L * Lᵧ / ρ * causalExpIntegralFrom hV l k A b +
          L * Lᵧ * N / (4 * k * ρ ^ 2) * causalExpIntegralFrom hV l k M b := by
  dsimp only
  let τ := fun t => T (projIcc (z : ℝ) u hzu t)
  intro hlτ hτz hτb hn hentry hder hr hν hlam hM hA
  have hh := hx.early_radiation_feedback hU hV hUR hp hf hρ hN hL A M z u hzu b T
    hτz hτb hn hentry hder hr hν hlam hM hA
  have hlb : (τ u : ℝ) ≤ b := hτb u ⟨hzu, le_rfl⟩
  have hLᵧ : 0 ≤ Lᵧ := by
    have he := hentry z ⟨le_rfl, hzu⟩
    linarith only [he.1, he.2]
  let m := fun t => M (projIcc 0 V hV t)
  let a := fun t => A (projIcc 0 V hV t)
  let E := fun t => Real.exp (-k * ((b : ℝ) - t))
  let R := fun t => ∫ w in t..b, Real.exp (-(3 * k) * (w - t)) * m w
  have hmc : Continuous m := by fun_prop
  have hac : Continuous a := by fun_prop
  have hEc : Continuous E := by fun_prop
  have hK := early_double_kernel_bound hk hlb hmc (fun t _ => hM0 _)
  have hRi : IntervalIntegrable (fun t => E t * R t) volume (τ u) b :=
    (hEc.continuousOn.mul hK.1).intervalIntegrable_of_Icc hlb
  have hAi : IntervalIntegrable (fun t => E t * a t) volume (τ u) b :=
    (hEc.mul hac).intervalIntegrable (τ u) b
  have hsplit : (∫ t in (τ u : ℝ)..b, E t * (a t + N / ρ * R t)) =
      (∫ t in (τ u : ℝ)..b, E t * a t) + N / ρ * ∫ t in (τ u : ℝ)..b, E t * R t := by
    have he : (fun t => E t * (a t + N / ρ * R t)) =
        fun t => E t * a t + N / ρ * (E t * R t) := by funext t; ring
    rw [he, intervalIntegral.integral_add hAi (hRi.const_mul (N / ρ)),
      intervalIntegral.integral_const_mul]
  have hAm : (∫ t in (τ u : ℝ)..b, E t * a t) ≤ causalExpIntegralFrom hV l k A b :=
    intervalIntegral.integral_mono_interval hlτ hlb le_rfl
      (Filter.Eventually.of_forall (fun t => mul_nonneg (Real.exp_pos _).le (hA0 _)))
      ((hEc.mul hac).intervalIntegrable l b)
  have hMm : (∫ t in (τ u : ℝ)..b, E t * m t) ≤ causalExpIntegralFrom hV l k M b :=
    intervalIntegral.integral_mono_interval hlτ hlb le_rfl
      (Filter.Eventually.of_forall (fun t => mul_nonneg (Real.exp_pos _).le (hM0 _)))
      ((hEc.mul hmc).intervalIntegrable l b)
  have hKR : (∫ t in (τ u : ℝ)..b, E t * R t) ≤
      (1 / (4 * k)) * causalExpIntegralFrom hV l k M b :=
    hK.2.2.trans (mul_le_mul_of_nonneg_left hMm (by positivity))
  change _ ≤ L * Lᵧ / ρ * (∫ t in (τ u : ℝ)..b, E t * (a t + N / ρ * R t)) at hh
  rw [hsplit] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left
    (add_le_add hAm (mul_le_mul_of_nonneg_left hKR (div_nonneg hN hρ.le)))
    (div_nonneg (mul_nonneg hL hLᵧ) hρ.le))
  exact hb.trans_eq (by ring)

theorem early_radiation_energy {V k ρ N L Lᵧ : ℝ}
    (hV : 0 ≤ V) (hk : 0 < k) (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hLᵧ : 0 ≤ Lᵧ)
    (hsmall : L * Lᵧ * N ≤ 2 * k ^ 2 * ρ ^ 2)
    (l : Icc 0 V) (H A M : C(Icc 0 V, ℝ)) (hM : ∀ v, 0 ≤ M v)
    (hb : ∀ v, l ≤ v → M v ≤ H v + L * Lᵧ / ρ * causalExpIntegralFrom hV l k A v +
      L * Lᵧ * N / (4 * k * ρ ^ 2) * causalExpIntegralFrom hV l k M v) :
    (∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
      8 * (∫ t in (l : ℝ)..V, (H (projIcc 0 V hV t)) ^ 2) +
        8 * (L * Lᵧ / ρ / k) ^ 2 * ∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2 := by
  let ε := L * Lᵧ * N / (4 * k * ρ ^ 2)
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hεk : ε ≤ k / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * k * ρ ^ 2)).2
    exact hsmall.trans_eq (by ring)
  exact causalExpIntegralFrom_forcing_energy hV hk hε hεk l H A M hM hb

end CauchyHorizon
