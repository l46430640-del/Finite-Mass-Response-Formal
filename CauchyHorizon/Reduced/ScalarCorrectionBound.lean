import CauchyHorizon.Reduced.ScalarTransport

/-! Pointwise scalar bounds retain the rough input and estimate only the continuous correction. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem scalarTransportCorrection_bound {N : ℝ} (hN : 0 ≤ N)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (w : WaveRectangle U V)
    (hν : ∀ u v, |ν u v| ≤ N) (u : Icc 0 U) (v : Icc 0 V) :
    |scalarTransportCorrection hV ν w u v| ≤ V * N * ‖waveCoordinateField 1 w u‖ := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (v : ℝ)) (f := fun t => -ν u (projIcc 0 V hV t) * w u (projIcc 0 V hV t) 1)
    (C := N * ‖waveCoordinateField 1 w u‖) (fun t _ => ?_)
  · change |∫ t in (0 : ℝ)..v, -ν u (projIcc 0 V hV t) * w u (projIcc 0 V hV t) 1| ≤ _
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg v.property.1] at hh
    have hv := mul_le_mul_of_nonneg_left v.property.2 (mul_nonneg hN (norm_nonneg (waveCoordinateField 1 w u)))
    exact hh.trans (by nlinarith only [hv])
  · rw [Real.norm_eq_abs, abs_mul, abs_neg]
    have hw : |w u (projIcc 0 V hV t) 1| ≤ ‖waveCoordinateField 1 w u‖ :=
      (waveCoordinateField 1 w u).norm_coe_le_norm _
    exact mul_le_mul (hν u _) hw (abs_nonneg _) hN

theorem IsWaveIntegral.scalar_transverse_bound
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {ρ R N : ℝ} (hρ : 0 < ρ) (hN : 0 ≤ N)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      |x.2.2 u v 1| ≤ R / ρ * |uIn u 1| +
        (V * N / ρ) * ‖waveCoordinateField 1 x.2.1 (projIcc 0 U hU u)‖ := by
  filter_upwards [hx.zeta_transport hr hinu] with u hu
  intro v
  let a := projIcc 0 U hU u
  have hrp : 0 < x.1 a v 0 := hρ.trans_le (hlo a v)
  have hs : x.1 a v 0 * |x.2.2 u v 1| ≤
      R * |uIn u 1| + V * N * ‖waveCoordinateField 1 x.2.1 a‖ := by
    calc
      _ = |x.1 a v 0 * x.2.2 u v 1| := by rw [abs_mul, abs_of_pos hrp]
      _ ≤ |zIn a 0 * uIn u 1| + |scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 a v| := by
        rw [hu v]
        exact abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hin a) (abs_nonneg _))
          (scalarTransportCorrection_bound hN _ _ hν a v)
  have hsmall := mul_le_mul_of_nonneg_right (hlo a v) (abs_nonneg (x.2.2 u v 1))
  calc
    _ ≤ (R * |uIn u 1| + V * N * ‖waveCoordinateField 1 x.2.1 a‖) / ρ := by
      apply (le_div_iff₀ hρ).2
      nlinarith only [hsmall, hs]
    _ = _ := by ring

end CauchyHorizon
