import CauchyHorizon.Characteristic.TrappedTransport
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Bounded actual optical flux turns the conformal corner comparison into a lambda bound. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.lambda_corner_of_optical_flux
    {M e Λ U V k σ Cd Co Jmax : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hCd : 0 ≤ Cd) (hCo : 0 ≤ Co) (u : Icc 0 U) (hu : 0 < (u : ℝ))
    (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0)
    (hentry : -x.2.1 u a 0 / Real.exp (x.1 u a 2) ≤ Cd * (u : ℝ))
    (hcorner : Real.exp (x.1 u b 2) ≤ Co *
      ((u : ℝ) ^ (-1 - σ) * Real.exp (-(2 * k) * b)))
    (hflux : (∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ Jmax) :
    |x.2.1 u b 0| ≤ (Cd * Co * Real.exp Jmax) *
      (u : ℝ) ^ (-σ) * Real.exp (-(2 * k) * b) := by
  let J := ∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
    (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)
  obtain ⟨_hJi, _hJ0, _hq, _hqp, _hqm, htransport⟩ :=
    hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha
  have hb : x.2.1 u b 0 < 0 := by
    have hh : 0 < -x.2.1 u b 0 := by
      rw [htransport]
      exact mul_pos (neg_pos.2 ha) (Real.exp_pos _)
    exact neg_pos.1 hh
  have he : -x.2.1 u b 0 =
      (-x.2.1 u a 0 / Real.exp (x.1 u a 2)) * Real.exp (x.1 u b 2) * Real.exp J := by
    rw [htransport, Real.exp_add, Real.exp_sub]
    ring
  have hpower : (u : ℝ) * (u : ℝ) ^ (-1 - σ) = (u : ℝ) ^ (-σ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (u : ℝ)]
    rw [← Real.rpow_add hu]
    congr 1
    ring
  rw [abs_of_neg hb, he]
  calc
    _ ≤ (Cd * (u : ℝ)) * (Co * ((u : ℝ) ^ (-1 - σ) * Real.exp (-(2 * k) * b))) *
        Real.exp Jmax :=
      mul_le_mul
        (mul_le_mul hentry hcorner (Real.exp_pos _).le (mul_nonneg hCd hu.le))
        (Real.exp_le_exp.2 hflux) (Real.exp_pos _).le (by positivity)
    _ = _ := by
      calc
        _ = (Cd * Co * Real.exp Jmax) * ((u : ℝ) * (u : ℝ) ^ (-1 - σ)) *
            Real.exp (-(2 * k) * b) := by ring
        _ = _ := by rw [hpower]

end CauchyHorizon
