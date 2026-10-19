import CauchyHorizon.Characteristic.ScalarWave
import CauchyHorizon.Characteristic.ConstraintWave
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Scalar transport from a moving entry time, with one null set for all endpoints. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.scalar_segment_bound {U V R₀ φ₀ e Λ ρ R c H : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R₀)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x) (hρ : 0 < ρ) (hc : 0 < c) (hH : 0 ≤ H) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ (a b : Icc 0 V), a ≤ b → ∀ N : ℝ, 0 ≤ N →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
      ρ ≤ x.1 u b 0 → x.1 u a 0 ≤ R →
      (∀ v ∈ Icc a b, |ν u v| ≤ N) →
      (∀ v ∈ Icc a b, |x.2.1 u v 1| ≤ H * Real.exp (-c * v)) →
        |x.2.2 t b 1| ≤ R / ρ * |x.2.2 t a 1| + N * H / (ρ * c) * Real.exp (-c * a) := by
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
  filter_upwards [hx.incoming_zeta_transport hU hV hUR hp hf] with t ht
  intro a b hab N hN
  dsimp only
  intro hrb hra hn hs
  let u := projIcc 0 U hU t
  let F := fun v => -ν u (projIcc 0 V hV v) * x.2.1 u (projIcc 0 V hV v) 1
  have hFc : Continuous F := by fun_prop
  have hIa := ht a
  have hIb := ht b
  change x.1 u a 0 * x.2.2 t a 1 = (R₀ - t) * f t + ∫ v in (0 : ℝ)..a, F v at hIa
  change x.1 u b 0 * x.2.2 t b 1 = (R₀ - t) * f t + ∫ v in (0 : ℝ)..b, F v at hIb
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hFc.intervalIntegrable (0 : ℝ) a) (hFc.intervalIntegrable (a : ℝ) b)
  have htransport : x.1 u b 0 * x.2.2 t b 1 = x.1 u a 0 * x.2.2 t a 1 +
      ∫ v in (a : ℝ)..b, F v := by linarith only [hIa, hIb, hsum]
  have hI : |∫ v in (a : ℝ)..b, F v| ≤ N * H / c * Real.exp (-c * a) := by
    have hG : IntervalIntegrable (fun v : ℝ => N * H * Real.exp (-c * v)) volume (a : ℝ) b :=
      (by fun_prop : Continuous (fun v : ℝ => N * H * Real.exp (-c * v))).intervalIntegrable _ _
    have hb := intervalIntegral.norm_integral_le_of_norm_le (show (a : ℝ) ≤ b from hab)
      (f := F) (g := fun v => N * H * Real.exp (-c * v))
      (Filter.Eventually.of_forall (fun v hv => ?_)) hG
    · rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.2 hc.ne'), integral_exp, smul_eq_mul] at hb
      apply hb.trans
      have hh := mul_nonneg (mul_nonneg (mul_nonneg hN hH) (inv_nonneg.2 hc.le))
        (Real.exp_pos (-c * (b : ℝ))).le
      rw [inv_neg, div_eq_mul_inv]
      nlinarith only [hh]
    · have hvV : v ∈ Icc 0 V := ⟨a.property.1.trans hv.1.le, hv.2.trans b.property.2⟩
      simp only [F, Real.norm_eq_abs, abs_mul, abs_neg, projIcc_of_mem hV hvV]
      exact (mul_le_mul (hn ⟨v, hvV⟩ ⟨hv.1.le, hv.2⟩)
        (hs ⟨v, hvV⟩ ⟨hv.1.le, hv.2⟩) (abs_nonneg _) hN).trans_eq (by ring)
  have hrpa := hx.incoming_radius_pos hU hV hUR hp hf u a
  have hrpb := hρ.trans_le hrb
  have hbound : ρ * |x.2.2 t b 1| ≤ R * |x.2.2 t a 1| + N * H / c * Real.exp (-c * a) := by
    calc
      _ ≤ x.1 u b 0 * |x.2.2 t b 1| := mul_le_mul_of_nonneg_right hrb (abs_nonneg _)
      _ = |x.1 u b 0 * x.2.2 t b 1| := by rw [abs_mul, abs_of_pos hrpb]
      _ ≤ |x.1 u a 0 * x.2.2 t a 1| + |∫ v in (a : ℝ)..b, F v| := by
        rw [htransport]
        exact abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_pos hrpa]
        exact add_le_add (mul_le_mul_of_nonneg_right hra (abs_nonneg _)) hI
  apply ((le_div_iff₀ hρ).2 (by simpa only [mul_comm ρ] using hbound)).trans_eq
  ring

end CauchyHorizon
