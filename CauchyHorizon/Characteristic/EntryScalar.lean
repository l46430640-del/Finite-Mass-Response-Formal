import CauchyHorizon.Characteristic.ScalarWave
import CauchyHorizon.Reduced.ScalarHistory

/-! Separate the known pre-entry forcing from the inner scalar amplitude. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.entry_normalized_zeta {U V R e Λ φ₀ a c q n N E H D A : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hc : 0 ≤ c) (hac : c < a) (hqc : 0 < q + c) (hn : 0 < n)
    (hN : 0 ≤ N) (hE : 0 ≤ E) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hca : c ≤ a * (1 - 1 / p.toReal))
    (hpoint : ∀ᵐ t ∂volume.restrict (Icc 0 U), |f t| ≤ A * t ^ (-1 / p.toReal)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ (T b : Icc 0 V), 0 < t → T ≤ b →
      t * Real.exp (a * T) ≤ D →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
      n ≤ t * (-ν u T) →
      (∀ v ≤ T, |ν u v| ≤ N * Real.exp (a * v)) →
      (∀ v ∈ Icc T b, |ν u v| ≤ (-ν u T) * Real.exp (-q * ((v : ℝ) - T))) →
      (∀ v ≤ T, |x.2.1 u v 1| ≤ E * Real.exp (-c * v)) →
      (∀ v ∈ Icc T b, |x.2.1 u v 1| ≤ H * Real.exp (-c * v)) →
        |x.1 u b 0 * x.2.2 t b 1| ≤ (-ν u T) * Real.exp (-c * T) *
          ((R * A * D ^ (1 - 1 / p.toReal) + N * E * D / (a - c)) / n + H / (q + c)) := by
  have ha : 0 < a := hc.trans_lt hac
  have hR : 0 < R := hU.trans_lt hUR
  let s := 1 - 1 / p.toReal
  have hs : 0 ≤ s := by dsimp only [s]; nlinarith only [ha, hc, hca]
  filter_upwards [hx.incoming_zeta_transport hU hV hUR hp hf, hpoint,
    ae_restrict_mem measurableSet_Icc] with t ht hfpt htm
  intro T b ht0 hTb hwidth
  dsimp only
  intro hnT hpre hpost hwpre hwpost
  let u := projIcc 0 U hU t
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
  have hnT0 : 0 < -ν u T := (mul_pos_iff_of_pos_left ht0).1 (hn.trans_le hnT)
  have hD : 0 < D := (mul_pos ht0 (Real.exp_pos _)).trans_le hwidth
  have hscale : t ^ s * Real.exp (c * T) ≤ D ^ s := by
    have hh := Real.rpow_le_rpow (mul_pos ht0 (Real.exp_pos (a * T))).le hwidth hs
    rw [Real.mul_rpow ht0.le (Real.exp_pos _).le, ← Real.exp_mul] at hh
    apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg ht0.le s)).trans hh
    have hh := mul_le_mul_of_nonneg_right hca T.property.1
    dsimp only [s]
    nlinarith only [hh]
  have htpow : t * t ^ (-1 / p.toReal) = t ^ s := by
    conv_lhs => arg 1; rw [← Real.rpow_one t]
    rw [← Real.rpow_add ht0]
    congr 1
    dsimp only [s]
    ring
  let C := R * A * D ^ s + N * E * D / (a - c)
  let P := R * |f t| + N * E / (a - c) * Real.exp ((a - c) * T)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hex : Real.exp ((a - c) * T) * Real.exp (c * T) = Real.exp (a * T) := by
    rw [← Real.exp_add]; congr 1; ring
  have hforce : t * P * Real.exp (c * T) ≤ C := by
    have hi := mul_le_mul_of_nonneg_left hfpt
      (by positivity : 0 ≤ R * t * Real.exp (c * T))
    have hp := mul_le_mul_of_nonneg_left hscale (mul_nonneg hR.le hA)
    have hw := mul_le_mul_of_nonneg_left hwidth
      (div_nonneg (mul_nonneg hN hE) (sub_pos.2 hac).le)
    have hi' : t * (R * |f t|) * Real.exp (c * T) ≤ R * A * D ^ s := by
      calc
        _ ≤ R * A * (t * t ^ (-1 / p.toReal) * Real.exp (c * T)) := by nlinarith only [hi]
        _ ≤ _ := by rw [htpow]; exact hp
    have he : t * P * Real.exp (c * T) =
        t * (R * |f t|) * Real.exp (c * T) + N * E / (a - c) * (t * Real.exp (a * T)) := by
      dsimp only [P]
      rw [← hex]
      ring
    rw [he]
    exact (add_le_add hi' hw).trans_eq (by dsimp only [C]; ring)
  have hnorm : P ≤ (-ν u T) * Real.exp (-c * T) * (C / n) := by
    have hentry := mul_le_mul_of_nonneg_left hnT (div_nonneg hC hn.le)
    rw [div_mul_cancel₀ C hn.ne'] at hentry
    have hh := hforce.trans hentry
    have hh' : P * Real.exp (c * T) ≤ (-ν u T) * (C / n) :=
      (mul_le_mul_iff_right₀ ht0).1 (by nlinarith only [hh])
    have he : Real.exp (c * T) * Real.exp (-c * T) = 1 := by
      rw [← Real.exp_add, show c * (T : ℝ) + -c * T = 0 by ring, Real.exp_zero]
    have hh'' := mul_le_mul_of_nonneg_right hh' (Real.exp_pos (-c * T)).le
    calc
      P = P * Real.exp (c * T) * Real.exp (-c * T) := by rw [mul_assoc, he, mul_one]
      _ ≤ _ := hh''
      _ = _ := by ring
  have hb := scalarTransportCorrection_two_amplitudes (hV := hV) hac hqc hN hnT0.le hE hH
    ν x.2.1 u T b hTb hpre hpost hwpre hwpost
  rw [ht b]
  apply (abs_add_le _ _).trans
  have hin : |(R - t) * f t| ≤ R * |f t| := by
    rw [abs_mul, abs_of_pos (sub_pos.2 (htm.2.trans_lt hUR))]
    exact mul_le_mul_of_nonneg_right (by linarith only [htm.1]) (abs_nonneg _)
  calc
    _ ≤ P + (-ν u T) * H / (q + c) * Real.exp (-c * T) := by
      exact (add_le_add hin hb).trans_eq (by dsimp only [P]; ring)
    _ ≤ (-ν u T) * Real.exp (-c * T) * (C / n) +
        (-ν u T) * H / (q + c) * Real.exp (-c * T) := add_le_add hnorm le_rfl
    _ = _ := by dsimp only [C, s]; ring

end CauchyHorizon
