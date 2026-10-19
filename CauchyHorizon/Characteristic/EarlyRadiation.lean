import CauchyHorizon.Characteristic.ArrivalRadiation
import CauchyHorizon.Characteristic.EntryRadiation

/-! The early double kernel follows from both actual scalar transports. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem IsWaveIntegral.early_radiation_feedback {U V R e Λ φ₀ k ρ N L Lᵧ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (A M : C(Icc 0 V, ℝ))
    (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (T : C(Icc (z : ℝ) u, Icc 0 V)) :
    let τ := fun t => T (projIcc (z : ℝ) u hzu t)
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
    τ z = b → (∀ t ∈ Icc (z : ℝ) u, τ t ≤ b) →
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
          L * Lᵧ / ρ * ∫ t in (τ u : ℝ)..b, Real.exp (-k * ((b : ℝ) - t)) *
            (A (projIcc 0 V hV t) + N / ρ * ∫ w in t..b,
              Real.exp (-(3 * k) * (w - t)) * M (projIcc 0 V hV w)) := by
  dsimp only
  let τ := fun t => T (projIcc (z : ℝ) u hzu t)
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
  intro hτz hτb hn hentry hder hr hν hlam hM hA
  let G : C(Icc 0 V, ℝ) := ⟨fun t => Real.exp (-(3 * k) * t) * M t, by fun_prop⟩
  let P := continuousPrimitive hV G
  let B : C(Icc 0 V, ℝ) :=
    ⟨fun t => A t + N / ρ * (Real.exp ((3 * k) * t) * (P b - P t)), by fun_prop⟩
  have hBeq (t : Icc 0 V) : B t = A t + N / ρ * ∫ w in (t : ℝ)..b,
      Real.exp (-(3 * k) * (w - t)) * M (projIcc 0 V hV w) := by
    have he : P b - P t = ∫ w in (t : ℝ)..b, intervalExtension hV G w := by
      have hh := intervalIntegral.integral_add_adjacent_intervals
        ((intervalExtension hV G).continuous.intervalIntegrable (μ := volume) (0 : ℝ) t)
        ((intervalExtension hV G).continuous.intervalIntegrable (t : ℝ) b)
      change P t + (∫ w in (t : ℝ)..b, intervalExtension hV G w) = P b at hh
      linarith only [hh]
    change A t + N / ρ * (Real.exp ((3 * k) * t) * (P b - P t)) = _
    rw [he, ← intervalIntegral.integral_const_mul]
    congr 2
    apply intervalIntegral.integral_congr
    intro w hw
    have hwV : w ∈ Icc 0 V :=
      ⟨(le_min t.property.1 b.property.1).trans hw.1, hw.2.trans (max_le t.property.2 b.property.2)⟩
    simp only [intervalExtension_apply, G, ContinuousMap.coe_mk, projIcc_of_mem hV hwV]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hζ : ∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1| ≤
        (-ν (projIcc 0 U hU t) (τ t)) * Real.exp (-k * τ t) * B (τ t) := by
    filter_upwards [hx.entry_radiation_majorant hU hV hUR hp hf hρ hN M, hA] with t ht hAt
    intro htm
    have hh := ht (τ t) b (hτb t htm) (hn t htm) (hr t htm) (hν t htm) (hM t htm)
    have hb : Real.exp (k * τ t) * |x.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1| ≤
        (-ν (projIcc 0 U hU t) (τ t)) * B (τ t) := by
      rw [hBeq]
      have he : 2 * k + k = 3 * k := by ring
      rw [he] at hh
      exact (hh.trans (add_le_add_left (hAt htm) _)).trans_eq (by ring)
    have he : Real.exp (-k * τ t) * Real.exp (k * τ t) = 1 := by
      rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
    have hh' := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-k * τ t)).le
    rw [← mul_assoc, he, one_mul] at hh'
    exact hh'.trans_eq (by ring)
  have hrrow (w : Icc 0 U) (hw : w ∈ Icc z u) : ρ ≤ x.1 w b 0 := by
    have hh := hr w hw b ⟨hτb w hw, le_rfl⟩
    simpa only [projIcc_of_mem hU w.property] using hh
  have hh := hx.arrival_radiation_majorant (c := k) (ℓ := 2 * k)
    hU hV hUR hp hf hρ hL B z u hzu b T hτz hn hentry hder hrrow hlam hζ
  have he : 2 * k - k = k := by ring
  rw [he] at hh
  apply hh.trans_eq
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htV : t ∈ Icc 0 V :=
    ⟨(le_min (τ u).property.1 b.property.1).trans ht.1,
      ht.2.trans (max_le (τ u).property.2 b.property.2)⟩
  dsimp only
  rw [projIcc_of_mem hV htV, hBeq]

end CauchyHorizon
