import CauchyHorizon.Characteristic.ScalarWave
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The actual horizontal increment retains a time-dependent matching majorant. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.arrival_radiation_majorant {U V R e Λ φ₀ c ℓ ρ L Lᵧ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hρ : 0 < ρ) (hL : 0 ≤ L)
    (B : C(Icc 0 V, ℝ))
    (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (T : C(Icc (z : ℝ) u, Icc 0 V)) :
    let τ := fun t => T (projIcc (z : ℝ) u hzu t)
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
    τ z = b →
    (∀ t ∈ Icc (z : ℝ) u, ν (projIcc 0 U hU t) (τ t) < 0) →
    (∀ t ∈ Icc (z : ℝ) u, -Lᵧ ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧
      x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0) →
    (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
      (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) →
    (∀ w ∈ Icc z u, ρ ≤ x.1 w b 0) →
    (∀ t ∈ Icc (z : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
      L * Real.exp (-ℓ * ((b : ℝ) - τ t))) →
    (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1| ≤
        (-ν (projIcc 0 U hU t) (τ t)) * Real.exp (-c * τ t) * B (τ t)) →
      Real.exp (c * b) * |x.1 u b 0 * x.2.1 u b 1 - x.1 z b 0 * x.2.1 z b 1| ≤
          L * Lᵧ / ρ * ∫ t in (τ u : ℝ)..b,
            Real.exp (-(ℓ - c) * ((b : ℝ) - t)) * B (projIcc 0 V hV t) := by
  dsimp only
  let τ := fun t => T (projIcc (z : ℝ) u hzu t)
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
  intro hτz hν hentry hder hr hlam hζ
  change τ z = b at hτz
  let n := fun t => -ν (projIcc 0 U hU t) (τ t)
  let l := fun t => -x.2.1 (projIcc 0 U hU t) (τ t) 0
  let s := ℓ - c
  let g := fun t => Real.exp (s * t) * B (projIcc 0 V hV t)
  let W := fun t => n t / l t * g (τ t)
  have hτ : Continuous (fun t => (τ t : ℝ)) := by fun_prop
  have hn : Continuous n := by fun_prop
  have hl : Continuous l := by fun_prop
  have hgc : Continuous g := by fun_prop
  have hlpos (t) (ht : t ∈ Icc (z : ℝ) u) : 0 < l t := neg_pos.2 (hentry t ht).2
  have hquot : ContinuousOn (fun t => n t / l t) (Icc (z : ℝ) u) :=
    hn.continuousOn.div hl.continuousOn (fun t ht => (hlpos t ht).ne')
  have hWi : IntervalIntegrable W volume z u :=
    (hquot.mul (hgc.comp hτ).continuousOn).intervalIntegrable_of_Icc hzu
  have hsubstitution := intervalIntegral.integral_comp_mul_deriv''
    (a := (z : ℝ)) (b := (u : ℝ))
    (f := fun t => (τ t : ℝ)) (f' := fun t => -(n t / l t)) (g := g)
    hτ.continuousOn (fun t ht => ?_)
    (by
      rw [uIcc_of_le (show (z : ℝ) ≤ u from hzu)]
      exact continuous_neg.comp_continuousOn hquot)
    hgc.continuousOn
  · have hW : (∫ t in (z : ℝ)..u, W t) = ∫ t in (τ u : ℝ)..b, g t := by
      have he : (fun t => (g ∘ fun t => (τ t : ℝ)) t * -(n t / l t)) = fun t => -W t := by
        funext t
        dsimp only [W, Function.comp_apply]
        ring
      rw [he, intervalIntegral.integral_neg, hτz, intervalIntegral.integral_symm (f := g)] at hsubstitution
      exact neg_injective hsubstitution
    let C := L * Lᵧ / ρ * Real.exp (-ℓ * b)
    have hsub : Icc (z : ℝ) u ⊆ Icc 0 U :=
      fun _ ht => ⟨z.property.1.trans ht.1, ht.2.trans u.property.2⟩
    have hsource : ∀ᵐ t ∂volume, t ∈ Ioc (z : ℝ) u →
        ‖-x.2.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1‖ ≤ C * W t := by
      apply (ae_restrict_iff' measurableSet_Ioc).1
      filter_upwards [ae_mono (Measure.restrict_mono
        (Ioc_subset_Icc_self.trans hsub) le_rfl) hζ, ae_restrict_mem measurableSet_Ioc] with t ht htm
      have htm' := Ioc_subset_Icc_self htm
      let w := projIcc 0 U hU t
      have hwm : w ∈ Icc z u := by
        change (z : ℝ) ≤ w ∧ (w : ℝ) ≤ u
        simpa only [w, projIcc_of_mem hU (hsub htm'), mem_Icc] using htm'
      have hn0 : 0 ≤ n t := (neg_pos.2 (hν t htm')).le
      have hBt : 0 ≤ B (τ t) := nonneg_of_mul_nonneg_right
        ((abs_nonneg _).trans (ht htm'))
        (mul_pos (neg_pos.2 (hν t htm')) (Real.exp_pos _))
      have hψ : |x.2.2 t b 1| ≤ n t * Real.exp (-c * τ t) * B (τ t) / ρ := by
        apply (le_div_iff₀ hρ).2
        calc
          _ ≤ x.1 w b 0 * |x.2.2 t b 1| := by
            nlinarith only [mul_le_mul_of_nonneg_right (hr w hwm) (abs_nonneg (x.2.2 t b 1))]
          _ = |x.1 w b 0 * x.2.2 t b 1| := by rw [abs_mul, abs_of_pos (hρ.trans_le (hr w hwm))]
          _ ≤ _ := ht htm'
      have hnL : n t ≤ Lᵧ * (n t / l t) := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ (hlpos t htm')).2
        nlinarith only [mul_le_mul_of_nonneg_left (neg_le.2 (hentry t htm').1) hn0]
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      calc
        _ ≤ (L * Real.exp (-ℓ * ((b : ℝ) - τ t))) *
            (n t * Real.exp (-c * τ t) * B (τ t) / ρ) :=
          mul_le_mul (hlam t htm') hψ (abs_nonneg _) (mul_nonneg hL (Real.exp_pos _).le)
        _ = (L / ρ * Real.exp (-ℓ * b)) * n t * (Real.exp (s * τ t) * B (τ t)) := by
          have he : Real.exp (-ℓ * ((b : ℝ) - τ t)) * Real.exp (-c * τ t) =
              Real.exp (-ℓ * b) * Real.exp (s * τ t) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp only [s]; ring
          calc
            _ = (L / ρ * n t * B (τ t)) *
                (Real.exp (-ℓ * ((b : ℝ) - τ t)) * Real.exp (-c * τ t)) := by ring
            _ = _ := by rw [he]; ring
        _ ≤ (L / ρ * Real.exp (-ℓ * b)) * (Lᵧ * (n t / l t)) *
            (Real.exp (s * τ t) * B (τ t)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnL (by positivity))
            (mul_nonneg (Real.exp_pos _).le hBt)
        _ = C * W t := by
          dsimp only [C, W, g]
          rw [projIcc_of_mem hV (τ t).property]
          ring
    have hbound := intervalIntegral.norm_integral_le_of_norm_le
      (show (z : ℝ) ≤ u from hzu) hsource (hWi.const_mul C)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, hW] at hbound
    let F := fun t => -x.2.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1
    let eval : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (1 : Fin 3)).comp (ContinuousMap.evalCLM ℝ b)
    have hψi : IntervalIntegrable (fun t => x.2.2 t b 1) volume 0 U := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      exact (eval.comp_memLp' (Lp.memLp x.2.2)).integrable (by norm_num)
    have hFi : IntervalIntegrable F volume 0 U := hψi.continuousOn_mul (by fun_prop)
    have h0z : uIcc (0 : ℝ) z ⊆ uIcc (0 : ℝ) U := by
      rw [uIcc_of_le z.property.1, uIcc_of_le hU]
      exact Icc_subset_Icc le_rfl z.property.2
    have hzu' : uIcc (z : ℝ) u ⊆ uIcc (0 : ℝ) U := by
      rw [uIcc_of_le (show (z : ℝ) ≤ u from hzu), uIcc_of_le hU]
      exact hsub
    have hθseg : x.1 u b 0 * x.2.1 u b 1 = x.1 z b 0 * x.2.1 z b 1 + ∫ t in (z : ℝ)..u, F t := by
      rw [hx.theta_integral (c := ![R, φ₀, Real.log 4]) rfl u b,
        hx.theta_integral (c := ![R, φ₀, Real.log 4]) rfl z b]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hFi.mono_set h0z) (hFi.mono_set hzu')]
      ring
    have htotal : |x.1 u b 0 * x.2.1 u b 1 - x.1 z b 0 * x.2.1 z b 1| ≤
        C * ∫ t in (τ u : ℝ)..b, g t := by
      rw [hθseg, add_sub_cancel_left]
      exact hbound
    have he : Real.exp (c * b) * (C * ∫ t in (τ u : ℝ)..b, g t) =
        L * Lᵧ / ρ * ∫ t in (τ u : ℝ)..b,
          Real.exp (-(ℓ - c) * ((b : ℝ) - t)) * B (projIcc 0 V hV t) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [C, g, s]
      have hex : Real.exp (c * b) * Real.exp (-ℓ * b) * Real.exp ((ℓ - c) * t) =
          Real.exp (-(ℓ - c) * ((b : ℝ) - t)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      calc
        _ = L * Lᵧ / ρ * (Real.exp (c * b) * Real.exp (-ℓ * b) *
            Real.exp ((ℓ - c) * t)) * B (projIcc 0 V hV t) := by ring
        _ = _ := by rw [hex]; ring
    have hh := mul_le_mul_of_nonneg_left htotal (Real.exp_pos (c * b)).le
    rwa [he] at hh
  · rw [min_eq_left (show (z : ℝ) ≤ u from hzu), max_eq_right (show (z : ℝ) ≤ u from hzu)] at ht
    apply ((hder t ht).congr_deriv ?_).hasDerivWithinAt
    dsimp only [n, l]
    ring

end CauchyHorizon
