import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Integrable logarithmic error yields a positive, finite exponential amplitude.
The geometric estimate making this error integrable is a separate obligation.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace CauchyHorizon

noncomputable def logarithmicProfile (initial rate origin : ℝ) (error : ℝ → ℝ)
    (t : ℝ) : ℝ :=
  initial - rate * (t - origin) + ∫ s in origin..t, error s

theorem rescaled_logarithmicProfile (initial rate origin t : ℝ) (error : ℝ → ℝ) :
    Real.exp (rate * (t - origin)) *
        Real.exp (logarithmicProfile initial rate origin error t) =
      Real.exp (initial + ∫ s in origin..t, error s) := by
  rw [← Real.exp_add]
  unfold logarithmicProfile
  congr 1
  ring

theorem exact_rate_of_integrable_error {error : ℝ → ℝ} {origin : ℝ}
    (herror : IntegrableOn error (Ioi origin)) (initial rate : ℝ) :
    Tendsto (fun t => Real.exp (rate * (t - origin)) *
        Real.exp (logarithmicProfile initial rate origin error t)) atTop
      (𝓝 (Real.exp (initial + ∫ s in Ioi origin, error s))) := by
  simp_rw [rescaled_logarithmicProfile]
  exact Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.add
    (intervalIntegral_tendsto_integral_Ioi origin herror tendsto_id))

theorem exact_rate_positive_limit {error : ℝ → ℝ} {origin : ℝ}
    (herror : IntegrableOn error (Ioi origin)) (initial rate : ℝ) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      Tendsto (fun t => Real.exp (rate * (t - origin)) *
        Real.exp (logarithmicProfile initial rate origin error t)) atTop (𝓝 amplitude) := by
  exact ⟨_, Real.exp_pos _, exact_rate_of_integrable_error herror initial rate⟩

theorem logarithmicProfile_eq_of_hasDerivAt {ell error : ℝ → ℝ} {origin rate t : ℝ}
    (ht : origin ≤ t) (herror : IntegrableOn error (Ioi origin))
    (hderiv : ∀ s ∈ Ici origin, HasDerivAt ell (-rate + error s) s) :
    logarithmicProfile (ell origin) rate origin error t = ell t := by
  have hint : IntervalIntegrable error volume origin t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
      (herror.mono_set Ioc_subset_Ioi_self)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hderiv s (by
      rw [uIcc_of_le ht] at hs
      exact hs.1)) (intervalIntegrable_const.add hint)
  rw [intervalIntegral.integral_add intervalIntegrable_const hint,
    intervalIntegral.integral_const] at hftc
  simp only [smul_eq_mul] at hftc
  unfold logarithmicProfile
  linarith

theorem exact_rate_of_hasDerivAt {ell error : ℝ → ℝ} {origin rate : ℝ}
    (herror : IntegrableOn error (Ioi origin))
    (hderiv : ∀ s ∈ Ici origin, HasDerivAt ell (-rate + error s) s) :
    Tendsto (fun t => Real.exp (rate * (t - origin)) * Real.exp (ell t)) atTop
      (𝓝 (Real.exp (ell origin + ∫ s in Ioi origin, error s))) := by
  apply (exact_rate_of_integrable_error herror (ell origin) rate).congr'
  filter_upwards [eventually_ge_atTop origin] with t ht
  rw [logarithmicProfile_eq_of_hasDerivAt ht herror hderiv]

theorem exact_blueshift_of_log_derivative {omegaSq error : ℝ → ℝ} {origin k : ℝ}
    (hpositive : ∀ t ∈ Ici origin, 0 < omegaSq t)
    (herror : IntegrableOn error (Ioi origin))
    (hderiv : ∀ t ∈ Ici origin,
      HasDerivAt (fun s => Real.log (omegaSq s)) (-(2 * k) + error t) t) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      Tendsto (fun t => Real.exp (2 * k * t) * omegaSq t) atTop (𝓝 amplitude) := by
  let amplitude := Real.exp (2 * k * origin) *
    Real.exp (Real.log (omegaSq origin) + ∫ s in Ioi origin, error s)
  refine ⟨amplitude, mul_pos (Real.exp_pos _) (Real.exp_pos _), ?_⟩
  have hlim := (exact_rate_of_hasDerivAt herror hderiv).const_mul
    (Real.exp (2 * k * origin))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop origin] with t ht
  rw [Real.exp_log (hpositive t ht), ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end CauchyHorizon
