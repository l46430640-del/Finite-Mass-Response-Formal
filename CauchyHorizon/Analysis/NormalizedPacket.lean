import CauchyHorizon.Analysis.LogarithmicRegularity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Normalized translations and dilations of a fixed smooth packet shape. -/

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology ContDiff

namespace CauchyHorizon

noncomputable def normalizedPacket (E : ℝ) (ψ : ℝ →ᵇ ℝ) (t L : ℝ) : ℝ →ᵇ ℝ :=
  Real.sqrt (E / ((∫ x, ψ x ^ 2) * L)) •
    ψ.compContinuous ⟨fun x => (x - t) / L, by fun_prop⟩

noncomputable def normalizedPacketDerivative (E : ℝ) (ψ ψ' : ℝ →ᵇ ℝ) (t L : ℝ) : ℝ →ᵇ ℝ :=
  (Real.sqrt (E / ((∫ x, ψ x ^ 2) * L)) / L) •
    ψ'.compContinuous ⟨fun x => (x - t) / L, by fun_prop⟩

theorem normalizedPacket_norm_tendsto (E : ℝ) (ψ : ℝ →ᵇ ℝ) (t L : ℕ → ℝ)
    (hLtop : Tendsto L atTop atTop) :
    Tendsto (fun n => ‖normalizedPacket E ψ (t n) (L n)‖) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => E / ((∫ x, ψ x ^ 2) * L n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_inv, ← mul_assoc, mul_zero] using
      (tendsto_inv_atTop_zero.comp hLtop).const_mul (E / (∫ x, ψ x ^ 2))
  have hs := (Real.continuous_sqrt.tendsto 0).comp hi
  have hlim : Tendsto (fun n => Real.sqrt (E / ((∫ x, ψ x ^ 2) * L n)) * ‖ψ‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, zero_mul] using hs.mul_const ‖ψ‖
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro n
  dsimp only [normalizedPacket]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (ψ.norm_compContinuous_le _) (Real.sqrt_nonneg _)

theorem normalizedPacket_moment {E L : ℝ} (hE : 0 ≤ E) (hL : 0 < L)
    (ψ : ℝ →ᵇ ℝ) (hM : 0 < ∫ x, ψ x ^ 2) (q t : ℝ)
    (hψ : Integrable (fun x => |ψ x| ^ q)) :
    Integrable (fun x => |normalizedPacket E ψ t L x| ^ q) ∧
      (∫ x, |normalizedPacket E ψ t L x| ^ q) =
        (E / (∫ x, ψ x ^ 2)) ^ (q / 2) * L ^ (1 - q / 2) * ∫ x, |ψ x| ^ q := by
  let M := ∫ x, ψ x ^ 2
  let A := Real.sqrt (E / (M * L))
  have he (x : ℝ) : |normalizedPacket E ψ t L x| ^ q = A ^ q * |ψ ((x-t)/L)| ^ q := by
    change |A * ψ ((x-t)/L)| ^ q = _
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), Real.mul_rpow (Real.sqrt_nonneg _) (abs_nonneg _)]
  have hscale : A ^ q * L = (E / M) ^ (q / 2) * L ^ (1 - q / 2) := by
    have hA : A ^ q = (E / M) ^ (q / 2) * L ^ (-(q / 2)) := by
      dsimp only [A]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (div_nonneg hE (mul_pos hM hL).le)]
      rw [show 1 / 2 * q = q / 2 by ring, div_mul_eq_div_div,
        Real.div_rpow (div_nonneg hE hM.le) hL.le, Real.rpow_neg hL.le]
      rfl
    have hLp : L ^ (-(q / 2)) * L = L ^ (1 - q / 2) := by
      calc
        _ = L ^ (-(q / 2)) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring
    rw [hA, mul_assoc, hLp]
  refine ⟨?_, ?_⟩
  · simp_rw [he]
    exact ((hψ.comp_div hL.ne').comp_sub_right t).const_mul (A ^ q)
  · simp_rw [he]
    rw [integral_const_mul, integral_sub_right_eq_self (fun x => |ψ (x/L)| ^ q) t,
      Measure.integral_comp_div (fun x => |ψ x| ^ q) L, smul_eq_mul, abs_of_pos hL,
      ← mul_assoc, hscale]

theorem normalizedPacket_moment_tendsto {E : ℝ} (hE : 0 ≤ E)
    (ψ : ℝ →ᵇ ℝ) (hM : 0 < ∫ x, ψ x ^ 2) {q : ℝ} (hq : 2 < q)
    (hψ : Integrable (fun x => |ψ x| ^ q)) (t L : ℕ → ℝ)
    (hL : ∀ n, 0 < L n) (hLtop : Tendsto L atTop atTop) :
    Tendsto (fun n => ∫ x, |normalizedPacket E ψ (t n) (L n) x| ^ q) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => L n ^ (1 - q / 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (show 0 < q / 2 - 1 by linarith)).comp hLtop
  have hlim := (hh.const_mul ((E / (∫ x, ψ x ^ 2)) ^ (q / 2))).mul_const (∫ x, |ψ x| ^ q)
  simpa only [(fun n => (normalizedPacket_moment hE (hL n) ψ hM q (t n) hψ).2), mul_zero, zero_mul] using hlim

theorem normalizedPacket_energy {E L : ℝ} (hE : 0 ≤ E) (hL : 0 < L)
    (ψ : ℝ →ᵇ ℝ) (hψ : Integrable (fun x => ψ x ^ 2))
    (hM : 0 < ∫ x, ψ x ^ 2) (t : ℝ) :
    Integrable (fun x => normalizedPacket E ψ t L x ^ 2) ∧
      (∫ x, normalizedPacket E ψ t L x ^ 2) = E := by
  have hh := normalizedPacket_moment hE hL ψ hM 2 t
    (by simpa only [Real.rpow_two, sq_abs] using hψ)
  simpa only [Real.rpow_two, sq_abs, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_one, sub_self, Real.rpow_zero, mul_one, div_mul_cancel₀ _ hM.ne'] using hh

theorem normalizedPacket_derivative {E L : ℝ} (hE : 0 ≤ E) (hL : 0 < L)
    (ψ ψ' : ℝ →ᵇ ℝ) (hd : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hψ' : Integrable (fun x => ψ' x ^ 2)) (hM : 0 < ∫ x, ψ x ^ 2) (t : ℝ) :
    (∀ x, HasDerivAt (normalizedPacket E ψ t L) (normalizedPacketDerivative E ψ ψ' t L x) x) ∧
      Integrable (fun x => normalizedPacketDerivative E ψ ψ' t L x ^ 2) ∧
      (∫ x, normalizedPacketDerivative E ψ ψ' t L x ^ 2) =
        (E / (∫ x, ψ x ^ 2)) * (1 / L) ^ 2 * ∫ x, ψ' x ^ 2 := by
  have hs := Real.sq_sqrt (div_nonneg hE (mul_pos hM hL).le)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hh := ((hd ((x - t) / L)).comp x
      (((hasDerivAt_id x).sub_const t).div_const L)).const_mul
        (Real.sqrt (E / ((∫ y, ψ y ^ 2) * L)))
    exact hh.congr_deriv (by dsimp [normalizedPacketDerivative]; ring)
  · change Integrable (fun x =>
      (Real.sqrt (E / ((∫ y, ψ y ^ 2) * L)) / L * ψ' ((x-t)/L)) ^ 2)
    simpa only [mul_pow] using
      ((hψ'.comp_div hL.ne').comp_sub_right t).const_mul
        ((Real.sqrt (E / ((∫ x, ψ x ^ 2) * L)) / L) ^ 2)
  · change (∫ x, (Real.sqrt (E / ((∫ y, ψ y ^ 2) * L)) / L * ψ' ((x-t)/L)) ^ 2) = _
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_sub_right_eq_self (fun x => ψ' (x/L) ^ 2) t,
      Measure.integral_comp_div (fun x => ψ' x ^ 2) L, smul_eq_mul, abs_of_pos hL,
      div_pow, hs]
    field_simp

theorem normalizedPacket_support {L : ℝ} (hL : 0 < L) (E : ℝ) (ψ : ℝ →ᵇ ℝ)
    (hψ : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) (t x : ℝ)
    (hx : x ≤ t ∨ t + L ≤ x) : normalizedPacket E ψ t L x = 0 := by
  have hz : ψ ((x - t) / L) = 0 := by
    apply hψ
    intro hh
    rcases hx with hx | hx
    · have := (div_pos_iff_of_pos_right hL).1 hh.1
      linarith
    · have := (div_lt_one hL).1 hh.2
      linarith
  change Real.sqrt (E / ((∫ y, ψ y ^ 2) * L)) * ψ ((x - t) / L) = 0
  rw [hz, mul_zero]

theorem normalizedPacket_contDiff {n : WithTop ℕ∞} {ψ : ℝ →ᵇ ℝ}
    (hψ : ContDiff ℝ n ψ) (E t L : ℝ) : ContDiff ℝ n (normalizedPacket E ψ t L) := by
  exact contDiff_const.mul (hψ.comp ((contDiff_id.sub contDiff_const).div_const L))

theorem smooth_packet_shape {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hcomp : HasCompactSupport ψ) {x : ℝ} (hx : ψ x ≠ 0) :
    ∃ P Q : ℝ →ᵇ ℝ, (∀ y, P y = ψ y) ∧ (∀ y, Q y = deriv ψ y) ∧
      (∀ y, HasDerivAt P (Q y) y) ∧ Integrable (fun y => P y ^ 2) ∧
      Integrable (fun y => Q y ^ 2) ∧ 0 < ∫ y, P y ^ 2 := by
  have hc := hψ.continuous
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  let P : ℝ →ᵇ ℝ := (⟨⟨ψ, hc⟩, hcomp⟩ : CompactlySupportedContinuousMap ℝ ℝ).toBoundedContinuousFunction
  let Q : ℝ →ᵇ ℝ := (⟨⟨deriv ψ, hdc⟩, hcomp.deriv⟩ : CompactlySupportedContinuousMap ℝ ℝ).toBoundedContinuousFunction
  have hsq : HasCompactSupport (fun y => ψ y ^ 2) := by
    exact hcomp.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have hdsq : HasCompactSupport (fun y => deriv ψ y ^ 2) := by
    exact hcomp.deriv.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact ⟨P, Q, fun _ => rfl, fun _ => rfl,
    fun y => (hψ.differentiable (by simp) y).hasDerivAt,
    (hc.pow 2).integrable_of_hasCompactSupport hsq,
    (hdc.pow 2).integrable_of_hasCompactSupport hdsq,
    (hc.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero hsq
      (fun y => sq_nonneg (ψ y)) (pow_ne_zero _ hx)⟩

theorem normalizedPacket_sequence {E : ℝ} (hE : 0 < E) (ψ ψ' : ℝ →ᵇ ℝ)
    (hd : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hψ : Integrable (fun x => ψ x ^ 2)) (hψ' : Integrable (fun x => ψ' x ^ 2))
    (hM : 0 < ∫ x, ψ x ^ 2) (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop) :
    ∃ P Q : ℕ → ℝ →ᵇ ℝ, P 0 = 0 ∧ Q 0 = 0 ∧
      (∀ n, n ≠ 0 → P n = normalizedPacket E ψ (t n) (L n)) ∧
      (∀ n, n ≠ 0 → Q n = normalizedPacketDerivative E ψ ψ' (t n) (L n)) ∧
      (∀ n x, HasDerivAt (P n) (Q n x) x) ∧
      (∀ n, ContDiff ℝ 1 (P n)) ∧
      (∀ n, Integrable (fun x => P n x ^ 2) ∧ (∫ x, P n x ^ 2) ≤ E) ∧
      (∀ n, n ≠ 0 → (∫ x, P n x ^ 2) = E) ∧
      (∀ n, Integrable (fun x => Q n x ^ 2)) ∧
      (∀ n, n ≠ 0 → (∫ x, Q n x ^ 2) =
        (E / (∫ x, ψ x ^ 2)) * (1 / L n) ^ 2 * ∫ x, ψ' x ^ 2) ∧
      Tendsto (fun n => ∫ x, Q n x ^ 2) atTop (𝓝 0) ∧
      (∀ n x, x ≤ t n ∨ t n + L n ≤ x → P n x = 0) ∧
      ∀ T : ℝ, ∀ᶠ n in atTop, ∀ x ≤ T, P n x = 0 := by
  let P : ℕ → ℝ →ᵇ ℝ := fun n => if n = 0 then 0 else normalizedPacket E ψ (t n) (L n)
  let Q : ℕ → ℝ →ᵇ ℝ := fun n => if n = 0 then 0 else normalizedPacketDerivative E ψ ψ' (t n) (L n)
  have henergy n := normalizedPacket_energy hE.le (hL n) ψ hψ hM (t n)
  have hderiv n := normalizedPacket_derivative hE.le (hL n) ψ ψ' hd hψ' hM (t n)
  have hPQ (n : ℕ) (x : ℝ) : HasDerivAt (P n) (Q n x) x := by
    by_cases hn : n = 0
    · subst n
      change HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x
      exact hasDerivAt_const x 0
    · simpa only [P, Q, if_neg hn] using (hderiv n).1 x
  have hsupport (n : ℕ) (x : ℝ) (hx : x ≤ t n ∨ t n + L n ≤ x) : P n x = 0 := by
    by_cases hn : n = 0
    · simp only [P, if_pos hn, BoundedContinuousFunction.coe_zero, Pi.zero_apply]
    · simpa only [P, if_neg hn] using normalizedPacket_support (hL n) E ψ hsupp (t n) x hx
  refine ⟨P, Q, by simp [P], by simp [Q], (fun n hn => if_neg hn), (fun n hn => if_neg hn),
    hPQ, ?_, ?_, ?_, ?_, ?_, ?_, hsupport, ?_⟩
  · intro n
    apply contDiff_one_iff_deriv.2
    refine ⟨fun x => (hPQ n x).differentiableAt, ?_⟩
    have he : deriv (P n) = (Q n : ℝ → ℝ) := funext (fun x => (hPQ n x).deriv)
    rw [he]
    exact (Q n).continuous
  · intro n
    by_cases hn : n = 0
    · simpa only [P, if_pos hn, BoundedContinuousFunction.coe_zero, Pi.zero_apply, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero] using
        (show Integrable (fun _ : ℝ => (0 : ℝ)) ∧ 0 ≤ E from ⟨integrable_zero _ _ _, hE.le⟩)
    · simpa only [P, if_neg hn] using ⟨(henergy n).1, (henergy n).2.le⟩
  · intro n hn
    simpa only [P, if_neg hn] using (henergy n).2
  · intro n
    by_cases hn : n = 0
    · simpa only [Q, if_pos hn, BoundedContinuousFunction.coe_zero, Pi.zero_apply, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
        (show Integrable (fun _ : ℝ => (0 : ℝ)) from integrable_zero _ _ _)
    · simpa only [Q, if_neg hn] using (hderiv n).2.1
  · intro n hn
    simpa only [Q, if_neg hn] using (hderiv n).2.2
  · have hinv : Tendsto (fun n => 1 / L n) atTop (𝓝 (0 : ℝ)) := by
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hLtop
    have hlim := ((hinv.pow 2).const_mul (E / (∫ x, ψ x ^ 2))).mul_const (∫ x, ψ' x ^ 2)
    have heq : (fun n => ∫ x, Q n x ^ 2) =ᶠ[atTop]
        (fun n => (E / (∫ x, ψ x ^ 2)) * (1 / L n) ^ 2 * ∫ x, ψ' x ^ 2) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      simpa only [Q, if_neg hn.ne'] using (hderiv n).2.2
    have hlim0 : Tendsto (fun n => (E / (∫ x, ψ x ^ 2)) * (1 / L n) ^ 2 * ∫ x, ψ' x ^ 2)
        atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using hlim
    exact hlim0.congr' heq.symm
  · intro T
    filter_upwards [(tendsto_atTop.1 htop) T] with n hn x hx
    exact hsupport n x (Or.inl (hx.trans hn))

end CauchyHorizon
