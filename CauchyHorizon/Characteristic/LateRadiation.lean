import CauchyHorizon.Characteristic.EntryRadiation
import CauchyHorizon.Analysis.LateKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Actual late scalar transport with a decaying causal feedback kernel. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem IsWaveIntegral.late_radiation_causal {U V R e Λ φ₀ k ξ χ ρ C D : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hρ : 0 < ρ) (hD : 0 ≤ D) (hgap : 0 < 2 * k - χ)
    (A M : C(Icc 0 V, ℝ)) (hM0 : ∀ v, 0 ≤ M v)
    (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (T : C(Icc (z : ℝ) u, Icc 0 V)) (J : C(Icc (z : ℝ) u, ℝ)) (N : ℝ → ℝ) :
    let τ := fun t => T (projIcc (z : ℝ) u hzu t)
    let j := fun t => J (projIcc (z : ℝ) u hzu t)
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
    τ z = b → (∀ t ∈ Icc (z : ℝ) u, τ t ≤ b) →
    (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ)) (-j t) t) →
    (∀ t ∈ Icc (z : ℝ) u, 0 ≤ N t) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b, ρ ≤ x.1 (projIcc 0 U hU t) v 0) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b, |ν (projIcc 0 U hU t) v| ≤ N t) →
    (∀ t ∈ Icc (z : ℝ) u,
      |x.2.1 (projIcc 0 U hU t) b 0| * N t ≤
        D * j t * Real.exp (-(2 * k) * b + (2 * k - χ) * τ t)) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b,
      Real.exp (k * v) * |x.1 (projIcc 0 U hU t) v 0 * x.2.1 (projIcc 0 U hU t) v 1| ≤ M v) →
    (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.2.1 (projIcc 0 U hU t) b 0| *
        |x.1 (projIcc 0 U hU t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
          C * j t * Real.exp (-(2 * k) * b + (k - ξ) * τ t) * A (τ t)) →
      (Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1 - x.1 z b 0 * x.2.1 z b 1| ≤
          C / ρ * (∫ t in (τ u : ℝ)..b,
            Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-ξ * t) * A (projIcc 0 V hV t)) +
          D / (ρ ^ 2 * (2 * k - χ)) * ∫ t in (τ u : ℝ)..b,
            Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-χ * t) * M (projIcc 0 V hV t)) ∧
      Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1| ≤
        Real.exp (k * b) * |x.1 z b 0 * x.2.1 z b 1| +
          C / ρ * (∫ t in (τ u : ℝ)..b,
            Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-ξ * t) * A (projIcc 0 V hV t)) +
          D / (ρ ^ 2 * (2 * k - χ)) * ∫ t in (τ u : ℝ)..b,
            Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-χ * t) * M (projIcc 0 V hV t) := by
  dsimp only
  let τ := fun t => T (projIcc (z : ℝ) u hzu t)
  let j := fun t => J (projIcc (z : ℝ) u hzu t)
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
  intro hτz hτb hder hN hr hν hfeedback hM hfree
  change τ z = b at hτz
  let G : C(Icc 0 V, ℝ) := ⟨fun v => Real.exp (-k * v) * M v, by fun_prop⟩
  let P := continuousPrimitive hV G
  let Q : C(Icc 0 V, ℝ) := ⟨fun t => P b - P t, by fun_prop⟩
  have hQ (t : Icc 0 V) : Q t = ∫ w in (t : ℝ)..b,
      Real.exp (-k * w) * M (projIcc 0 V hV w) := by
    have hh := intervalIntegral.integral_add_adjacent_intervals
      ((intervalExtension hV G).continuous.intervalIntegrable (μ := volume) (0 : ℝ) t)
      ((intervalExtension hV G).continuous.intervalIntegrable (t : ℝ) b)
    change P t + (∫ w in (t : ℝ)..b, intervalExtension hV G w) = P b at hh
    have he : Q t = ∫ w in (t : ℝ)..b, intervalExtension hV G w := by
      change P b - P t = _
      linarith only [hh]
    rw [he]
    apply intervalIntegral.integral_congr
    intro w hw
    have hwV : w ∈ Icc 0 V :=
      ⟨(le_min t.property.1 b.property.1).trans hw.1, hw.2.trans (max_le t.property.2 b.property.2)⟩
    simp only [intervalExtension_apply, G, ContinuousMap.coe_mk, projIcc_of_mem hV hwV]
  let K : C(Icc 0 V, ℝ) := ⟨fun t =>
    C / ρ * Real.exp (-(2 * k) * b + (k - ξ) * t) * A t +
      D / ρ ^ 2 * Real.exp (-(2 * k) * b + (2 * k - χ) * t) * Q t, by fun_prop⟩
  let W := fun t => j t * K (τ t)
  have hτc : Continuous (fun t => (τ t : ℝ)) := by fun_prop
  have hjc : Continuous j := by fun_prop
  have hKc : Continuous (fun t => K (projIcc 0 V hV t)) := by fun_prop
  have hWc : Continuous W := by fun_prop
  have hsubstitution := intervalIntegral.integral_comp_mul_deriv''
    (a := (z : ℝ)) (b := (u : ℝ)) (f := fun t => (τ t : ℝ))
    (f' := fun t => -j t) (g := fun t => K (projIcc 0 V hV t))
    hτc.continuousOn (fun t ht => (hder t (by
      rwa [min_eq_left (show (z : ℝ) ≤ u from hzu), max_eq_right (show (z : ℝ) ≤ u from hzu)] at ht)).hasDerivWithinAt)
    hjc.neg.continuousOn hKc.continuousOn
  have hW : (∫ t in (z : ℝ)..u, W t) = ∫ t in (τ u : ℝ)..b, K (projIcc 0 V hV t) := by
    have he : (fun t => K (projIcc 0 V hV (τ t)) * -j t) = fun t => -W t := by
      funext t
      rw [projIcc_of_mem hV (τ t).property]
      dsimp only [W]
      ring
    change (∫ t in (z : ℝ)..u, K (projIcc 0 V hV (τ t)) * -j t) = _ at hsubstitution
    rw [he, intervalIntegral.integral_neg, hτz, intervalIntegral.integral_symm
      (f := fun t => K (projIcc 0 V hV t))] at hsubstitution
    exact neg_injective hsubstitution
  have hsub : Icc (z : ℝ) u ⊆ Icc 0 U := Icc_subset_Icc z.property.1 u.property.2
  let F := fun t => -x.2.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1
  have hsource : ∀ᵐ t ∂volume, t ∈ Ioc (z : ℝ) u → ‖F t‖ ≤ W t := by
    apply (ae_restrict_iff' measurableSet_Ioc).1
    filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Icc_self.trans hsub) le_rfl)
      (hx.incoming_zeta_transport hU hV hUR hp hf),
      ae_mono (Measure.restrict_mono (Ioc_subset_Icc_self.trans hsub) le_rfl) hfree,
      ae_restrict_mem measurableSet_Ioc] with t ht hft htm
    have htm' := Ioc_subset_Icc_self htm
    let a := τ t
    let y := projIcc 0 U hU t
    let Z := fun v => x.1 y v 0 * x.2.2 t v 1
    let I := fun w => -ν y (projIcc 0 V hV w) * x.2.1 y (projIcc 0 V hV w) 1
    have hIc : Continuous I := by fun_prop
    have hseg : Z b = Z a + ∫ w in (a : ℝ)..b, I w := by
      dsimp only [Z, y]
      rw [ht b, ht a]
      change (R - t) * f t + (∫ w in (0 : ℝ)..b, I w) =
        (R - t) * f t + (∫ w in (0 : ℝ)..a, I w) + ∫ w in (a : ℝ)..b, I w
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hIc.intervalIntegrable (0 : ℝ) a) (hIc.intervalIntegrable (a : ℝ) b)]
      ring
    have hplain (v : Icc 0 V) (hv : v ∈ Icc a b) : |x.1 y v 0 * x.2.1 y v 1| ≤ G v := by
      have hh := mul_le_mul_of_nonneg_left (hM t htm' v hv) (Real.exp_pos (-k * v)).le
      have he : Real.exp (-k * v) * Real.exp (k * v) = 1 := by
        rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
      rw [← mul_assoc, he, one_mul] at hh
      exact hh
    have hz := radiation_transport_majorant (k := 0) (q := 0) hV hρ (hN t htm')
      ⟨fun v => x.1 y v 0, by fun_prop⟩ (ν y) ⟨fun v => x.2.1 y v 1, by fun_prop⟩
      G a b (hτb t htm') hseg (hr t htm')
      (by simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one] using hν t htm')
      (by
        intro v hv
        simpa only [zero_mul, Real.exp_zero, one_mul, ContinuousMap.coe_mk] using hplain v hv)
    simp only [zero_mul, Real.exp_zero, one_mul, neg_zero, zero_add] at hz
    change |Z b| ≤ |Z a| + N t / ρ * ∫ w in (a : ℝ)..b, G (projIcc 0 V hV w) at hz
    have hQG : (∫ w in (a : ℝ)..b, G (projIcc 0 V hV w)) = Q a := by
      rw [hQ]
      apply intervalIntegral.integral_congr
      intro w hw
      have hwV : w ∈ Icc 0 V :=
        ⟨(le_min a.property.1 b.property.1).trans hw.1, hw.2.trans (max_le a.property.2 b.property.2)⟩
      simp only [G, ContinuousMap.coe_mk, projIcc_of_mem hV hwV]
    rw [hQG] at hz
    have hQ0 : 0 ≤ Q a := by
      rw [hQ]
      exact intervalIntegral.integral_nonneg (hτb t htm')
        (fun w _ => mul_nonneg (Real.exp_pos _).le (hM0 _))
    have hψ : |x.2.2 t b 1| ≤ (|Z a| + N t / ρ * Q a) / ρ := by
      apply (le_div_iff₀ hρ).2
      have hh := mul_le_mul_of_nonneg_right (hr t htm' b ⟨hτb t htm', le_rfl⟩)
        (abs_nonneg (x.2.2 t b 1))
      dsimp only [Z] at hz
      rw [abs_mul, abs_of_pos (hρ.trans_le (hr t htm' b ⟨hτb t htm', le_rfl⟩))] at hz
      nlinarith only [hz, hh]
    have hh := mul_le_mul_of_nonneg_left hψ (abs_nonneg (x.2.1 y b 0))
    have hb := mul_le_mul_of_nonneg_right (hfeedback t htm') (div_nonneg hQ0 hρ.le)
    have hf' := hft htm'
    have hsum : |x.2.1 y b 0| * (|Z a| + N t / ρ * Q a) ≤
        C * j t * Real.exp (-(2 * k) * b + (k - ξ) * a) * A a +
          D * j t * Real.exp (-(2 * k) * b + (2 * k - χ) * a) * Q a / ρ := by
      calc
        _ = |x.2.1 y b 0| * |Z a| + |x.2.1 y b 0| * N t * (Q a / ρ) := by ring
        _ ≤ C * j t * Real.exp (-(2 * k) * b + (k - ξ) * a) * A a +
            D * j t * Real.exp (-(2 * k) * b + (2 * k - χ) * a) * (Q a / ρ) :=
          add_le_add hf' hb
        _ = _ := by ring
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    apply hh.trans
    calc
      _ = (|x.2.1 y b 0| * (|Z a| + N t / ρ * Q a)) / ρ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hsum hρ.le
      _ = W t := by dsimp only [W, K, ContinuousMap.coe_mk, a]; field_simp
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (show (z : ℝ) ≤ u from hzu) hsource (hWc.intervalIntegrable z u)
  rw [Real.norm_eq_abs, hW] at hbound
  let eval : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (1 : Fin 3)).comp (ContinuousMap.evalCLM ℝ b)
  have hψi : IntervalIntegrable (fun t => x.2.2 t b 1) volume 0 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      ((eval.comp_memLp' (Lp.memLp x.2.2)).integrable (by norm_num))
  have hFi : IntervalIntegrable F volume 0 U := hψi.continuousOn_mul (by fun_prop)
  have h0z : uIcc (0 : ℝ) z ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le z.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl z.property.2
  have hzu' : uIcc (z : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le (show (z : ℝ) ≤ u from hzu), uIcc_of_le hU]
    exact hsub
  have hθ : x.1 u b 0 * x.2.1 u b 1 = x.1 z b 0 * x.2.1 z b 1 + ∫ t in (z : ℝ)..u, F t := by
    rw [hx.theta_integral (c := ![R, φ₀, Real.log 4]) rfl u b,
      hx.theta_integral (c := ![R, φ₀, Real.log 4]) rfl z b,
      ← intervalIntegral.integral_add_adjacent_intervals (hFi.mono_set h0z) (hFi.mono_set hzu')]
    ring
  have hsigned : |x.1 u b 0 * x.2.1 u b 1 - x.1 z b 0 * x.2.1 z b 1| ≤
      ∫ t in (τ u : ℝ)..b, K (projIcc 0 V hV t) := by
    rw [hθ, add_sub_cancel_left]
    exact hbound
  have htotal' := mul_le_mul_of_nonneg_left hsigned (Real.exp_pos (k * b)).le
  rw [← intervalIntegral.integral_const_mul] at htotal'
  let fA := fun t => Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-ξ * t) * A (projIcc 0 V hV t)
  let fQ := fun t => Real.exp ((2 * k - χ) * t) * Q (projIcc 0 V hV t)
  have hAc : Continuous fA := by fun_prop
  have hQc : Continuous fQ := by fun_prop
  have he (t : ℝ) (ht : t ∈ Icc 0 V) :
      Real.exp (k * b) * K (projIcc 0 V hV t) =
        C / ρ * fA t + D / ρ ^ 2 * Real.exp (-k * b) * fQ t := by
    have heA : Real.exp (k * b) * Real.exp (-(2 * k) * b + (k - ξ) * t) =
        Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-ξ * t) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have heQ : Real.exp (k * b) * Real.exp (-(2 * k) * b + (2 * k - χ) * t) =
        Real.exp (-k * b) * Real.exp ((2 * k - χ) * t) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    dsimp only [K, ContinuousMap.coe_mk, fA, fQ]
    rw [projIcc_of_mem hV ht]
    calc
      _ = C / ρ * (Real.exp (k * b) * Real.exp (-(2 * k) * b + (k - ξ) * t)) * A ⟨t, ht⟩ +
        D / ρ ^ 2 * (Real.exp (k * b) * Real.exp (-(2 * k) * b + (2 * k - χ) * t)) * Q ⟨t, ht⟩ := by ring
      _ = _ := by rw [heA, heQ]; ring
  have hsplit : (∫ t in (τ u : ℝ)..b, Real.exp (k * b) * K (projIcc 0 V hV t)) =
      C / ρ * (∫ t in (τ u : ℝ)..b, fA t) +
        D / ρ ^ 2 * Real.exp (-k * b) * ∫ t in (τ u : ℝ)..b, fQ t := by
    rw [intervalIntegral.integral_congr (fun t ht => he t
      ⟨(le_min (τ u).property.1 b.property.1).trans ht.1,
        ht.2.trans (max_le (τ u).property.2 b.property.2)⟩),
      intervalIntegral.integral_add ((hAc.intervalIntegrable _ _).const_mul _)
        ((hQc.intervalIntegrable _ _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit] at htotal'
  have hkernel := late_double_kernel_bound hgap (show (τ u : ℝ) ≤ b from hτb u ⟨hzu, le_rfl⟩)
    (show Continuous (fun t => M (projIcc 0 V hV t)) by fun_prop) (fun t _ => hM0 _)
  have hQeq : (∫ t in (τ u : ℝ)..b, fQ t) =
      ∫ t in (τ u : ℝ)..b, Real.exp ((2 * k - χ) * t) *
        ∫ w in t..b, Real.exp (-k * w) * M (projIcc 0 V hV w) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htV : t ∈ Icc 0 V :=
      ⟨(le_min (τ u).property.1 b.property.1).trans ht.1, ht.2.trans (max_le (τ u).property.2 b.property.2)⟩
    dsimp only [fQ]
    rw [hQ, projIcc_of_mem hV htV]
  rw [← hQeq] at hkernel
  have hh := mul_le_mul_of_nonneg_left hkernel (div_nonneg hD (sq_nonneg ρ))
  have he : D / ρ ^ 2 * (1 / (2 * k - χ)) = D / (ρ ^ 2 * (2 * k - χ)) := by
    field_simp [hρ.ne', hgap.ne']
  simp only [← mul_assoc, he] at hh
  have hfinal := htotal'.trans (add_le_add_right hh _)
  dsimp only [fA, τ] at hfinal
  refine ⟨hfinal, ?_⟩
  have htri := abs_add_le (x.1 u b 0 * x.2.1 u b 1 - x.1 z b 0 * x.2.1 z b 1)
    (x.1 z b 0 * x.2.1 z b 1)
  rw [sub_add_cancel] at htri
  have hh := mul_le_mul_of_nonneg_left htri (Real.exp_pos (k * b)).le
  nlinarith only [hh, hfinal]

end CauchyHorizon
