import CauchyHorizon.Characteristic.ScalarWave
import CauchyHorizon.Reduced.TransverseRadiation

/-! Post-entry scalar transport with the actual time-dependent radiation majorant. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.entry_radiation_majorant {U V R e Λ φ₀ k q ρ N : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (M : C(Icc 0 V, ℝ)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ (T b : Icc 0 V), T ≤ b →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
      ν u T < 0 →
      (∀ v ∈ Icc T b, ρ ≤ x.1 u v 0) →
      (∀ v ∈ Icc T b, |ν u v| ≤ N * (-ν u T) * Real.exp (-q * ((v : ℝ) - T))) →
      (∀ v ∈ Icc T b, Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v) →
        Real.exp (k * T) * |x.1 u b 0 * x.2.2 t b 1| ≤
          Real.exp (k * T) * |x.1 u T 0 * x.2.2 t T 1| +
            N * (-ν u T) / ρ * ∫ w in (T : ℝ)..b,
              Real.exp (-(q + k) * (w - T)) * M (projIcc 0 V hV w) := by
  filter_upwards [hx.incoming_zeta_transport hU hV hUR hp hf] with t ht
  intro T b hTb
  dsimp only
  intro hn hr hν hM
  let u := projIcc 0 U hU t
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
  let F := fun w => -ν u (projIcc 0 V hV w) * x.2.1 u (projIcc 0 V hV w) 1
  have hFc : Continuous F := by fun_prop
  have hseg : x.1 u b 0 * x.2.2 t b 1 =
      x.1 u T 0 * x.2.2 t T 1 + ∫ w in (T : ℝ)..b, F w := by
    rw [ht b, ht T]
    change (R - t) * f t + (∫ w in (0 : ℝ)..b, F w) =
      (R - t) * f t + (∫ w in (0 : ℝ)..T, F w) + ∫ w in (T : ℝ)..b, F w
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable (0 : ℝ) T) (hFc.intervalIntegrable (T : ℝ) b)]
    ring
  exact radiation_transport_majorant hV hρ (mul_nonneg hN (neg_pos.2 hn).le)
    ⟨fun v => x.1 u v 0, by fun_prop⟩ (ν u) ⟨fun v => x.2.1 u v 1, by fun_prop⟩ M
      T b hTb hseg hr hν hM

end CauchyHorizon
