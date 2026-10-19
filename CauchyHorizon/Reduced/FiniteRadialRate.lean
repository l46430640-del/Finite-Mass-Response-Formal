import CauchyHorizon.Reduced.FiniteRadialFlux
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exact logarithmic evolution and two-sided finite-time bounds for the radial derivative. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}

theorem IsWaveIntegral.radialNu_exponential
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v < 0)
    (u : Icc 0 U) (v : Icc 0 V) :
    radialNuField hV e Λ zIn x.1 hr u v = -Real.exp (∫ t in (0 : ℝ)..v,
      Real.exp (intervalExtension hV (x.1 u) t 2) *
        radialPotential (intervalExtension hV (x.1 u) t 0) e Λ /
          intervalExtension hV (radialNuField hV e Λ zIn x.1 hr u) t -
        intervalExtension hV (x.2.1 u) t 0 / intervalExtension hV (x.1 u) t 0) := by
  let N := radialNuField hV e Λ zIn x.1 hr u
  let G : ℝ → ℝ := fun t => Real.exp (intervalExtension hV (x.1 u) t 2) *
    radialPotential (intervalExtension hV (x.1 u) t 0) e Λ / intervalExtension hV N t -
      intervalExtension hV (x.2.1 u) t 0 / intervalExtension hV (x.1 u) t 0
  have hn (t : ℝ) : intervalExtension hV N t ≠ 0 := ne_of_lt (hnu u (projIcc 0 V hV t))
  have hrn (t : ℝ) : intervalExtension hV (x.1 u) t 0 ≠ 0 := hr u (projIcc 0 V hV t)
  have hG : Continuous G := by
    have hF := (continuous_apply (0 : Fin 3)).comp
      (intervalExtension hV (wavePotentialField e Λ (x.1 u) (hr u))).continuous
    have hwc := (continuous_apply (0 : Fin 3)).comp (intervalExtension hV (x.2.1 u)).continuous
    have hrc := (continuous_apply (0 : Fin 3)).comp (intervalExtension hV (x.1 u)).continuous
    exact (hF.div (intervalExtension hV N).continuous hn).sub (hwc.div hrc hrn)
  have hlog : Continuous (fun t => Real.log (-intervalExtension hV N t)) := by
    exact (intervalExtension hV N).continuous.neg.log (fun t => neg_ne_zero.2 (hn t))
  have hd (t : ℝ) (ht : t ∈ Icc 0 V) :
      HasDerivWithinAt (fun s => Real.log (-intervalExtension hV N s)) (G t) (Icc 0 V) t := by
    have hh := (hx.radialNu_hasDerivWithinAt hr u ⟨t, ht⟩).neg.log (neg_ne_zero.2 (hn t))
    apply hh.congr_deriv
    simp only [radialSourceField_apply, G, Pi.neg_apply, intervalExtension_apply, projIcc_of_mem hV ht]
    change -(Real.exp (x.1 u ⟨t, ht⟩ 2) * radialPotential (x.1 u ⟨t, ht⟩ 0) e Λ -
      N ⟨t, ht⟩ * x.2.1 u ⟨t, ht⟩ 0 / x.1 u ⟨t, ht⟩ 0) / (-N ⟨t, ht⟩) = _
    have hn' : N ⟨t, ht⟩ ≠ 0 := ne_of_lt (hnu u ⟨t, ht⟩)
    field_simp [hn', hr u ⟨t, ht⟩]
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le v.property.1 hlog.continuousOn
    (fun t ht => (hd t ⟨ht.1.le, ht.2.le.trans v.property.2⟩).hasDerivAt
      (Icc_mem_nhds ht.1 (ht.2.trans_le v.property.2))) (hG.intervalIntegrable (0 : ℝ) v)
  simp only [intervalExtension_apply, projIcc_of_mem hV v.property,
    projIcc_of_mem hV (show (0 : ℝ) ∈ Icc 0 V from ⟨le_rfl, hV⟩)] at hp
  have hzero : N ⟨0, le_rfl, hV⟩ = -1 := hx.radialNu_incoming hr u
  rw [hzero, neg_neg, Real.log_one, sub_zero] at hp
  have he := congrArg Real.exp hp
  rw [Real.exp_log (neg_pos.2 (hnu u v))] at he
  change N v = -Real.exp (∫ t in (0 : ℝ)..v, G t)
  linarith only [he]

theorem IsWaveIntegral.radialNu_kappa_exponential
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v < 0)
    (u : Icc 0 U) (v : Icc 0 V) :
    radialNuField hV e Λ zIn x.1 hr u v = -Real.exp (∫ t in (0 : ℝ)..v,
      (-Real.exp (intervalExtension hV (x.1 u) t 2) /
          (4 * intervalExtension hV (radialNuField hV e Λ zIn x.1 hr u) t)) *
        (1 / intervalExtension hV (x.1 u) t 0 - e ^ 2 / (intervalExtension hV (x.1 u) t 0) ^ 3 -
          Λ * intervalExtension hV (x.1 u) t 0) -
        intervalExtension hV (x.2.1 u) t 0 / intervalExtension hV (x.1 u) t 0) := by
  rw [hx.radialNu_exponential hr hnu u v]
  apply congrArg (fun a => -Real.exp a)
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [intervalExtension_apply, radialPotential]
  field_simp [hr u (projIcc 0 V hV t), ne_of_lt (hnu u (projIcc 0 V hV t))]
  ring

theorem IsWaveIntegral.finite_radial_rate_bound
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {ρ B L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0)
    (hP : ∀ u v, |radialPotential (x.1 u v 0) e Λ| ≤ B)
    (hvel : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v < 0)
    (homega : ∀ u v, Real.exp (x.1 u v 2) ≤ -4 * radialNuField hV e Λ zIn x.1 hr u v)
    (u : Icc 0 U) (v : Icc 0 V) :
    Real.exp (-(4 * B + L / ρ) * v) ≤ -radialNuField hV e Λ zIn x.1 hr u v ∧
      -radialNuField hV e Λ zIn x.1 hr u v ≤ Real.exp ((4 * B + L / ρ) * v) ∧
      Real.exp (x.1 u v 2) ≤ 4 * Real.exp ((4 * B + L / ρ) * v) := by
  let N := radialNuField hV e Λ zIn x.1 hr u
  let G : ℝ → ℝ := fun t => Real.exp (intervalExtension hV (x.1 u) t 2) *
    radialPotential (intervalExtension hV (x.1 u) t 0) e Λ / intervalExtension hV N t -
      intervalExtension hV (x.2.1 u) t 0 / intervalExtension hV (x.1 u) t 0
  have hG (t : ℝ) : |G t| ≤ 4 * B + L / ρ := by
    let w := projIcc 0 V hV t
    have hrp : 0 < x.1 u w 0 := hρ.trans_le (hlo u w)
    have hnp : 0 < -N w := neg_pos.2 (hnu u w)
    have hratio : Real.exp (x.1 u w 2) / (-N w) ≤ 4 := by
      apply (div_le_iff₀ hnp).2
      simpa only [mul_neg, neg_mul] using homega u w
    have hp : |Real.exp (x.1 u w 2) * radialPotential (x.1 u w 0) e Λ / N w| ≤ 4 * B := by
      rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_neg (hnu u w)]
      calc
        _ = (Real.exp (x.1 u w 2) / (-N w)) * |radialPotential (x.1 u w 0) e Λ| := by ring
        _ ≤ _ := mul_le_mul hratio (hP u w) (abs_nonneg _) (by norm_num)
    have hl : |x.2.1 u w 0 / x.1 u w 0| ≤ L / ρ := by
      rw [abs_div, abs_of_pos hrp]
      exact (div_le_div_of_nonneg_right (hvel u w) hrp.le).trans
        (div_le_div_of_nonneg_left hL hρ (hlo u w))
    exact (abs_sub _ _).trans (add_le_add hp hl)
  have hi : |∫ t in (0 : ℝ)..v, G t| ≤ (4 * B + L / ρ) * v := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := G) (C := 4 * B + L / ρ) (a := (0 : ℝ)) (b := (v : ℝ))
      (fun t _ht => by simpa only [Real.norm_eq_abs] using hG t)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg v.property.1, mul_comm] using hh
  have he : -N v = Real.exp (∫ t in (0 : ℝ)..v, G t) := by
    have hh := hx.radialNu_exponential hr hnu u v
    change N v = -Real.exp (∫ t in (0 : ℝ)..v, G t) at hh
    linarith only [hh]
  have hupper : -N v ≤ Real.exp ((4 * B + L / ρ) * v) := by
    rw [he]
    exact Real.exp_le_exp.2 (abs_le.1 hi).2
  refine ⟨?_, hupper, ?_⟩
  · rw [he]
    apply Real.exp_le_exp.2
    simpa only [neg_mul] using (abs_le.1 hi).1
  · have hh := homega u v
    nlinarith only [hh, mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 4)]

theorem radialNuField_flux_exponential (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hrp : ∀ u v, 0 < x.1 u v 0)
    (hν : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v < 0) (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ zIn x.1 hr
    x.1 u v 0 * N u v = -zIn u 0 * Real.exp (∫ t in (0 : ℝ)..v,
      Real.exp (intervalExtension hV (x.1 u) t 2) *
        radialPotential (intervalExtension hV (x.1 u) t 0) e Λ / intervalExtension hV (N u) t) := by
  let N := radialNuField hV e Λ zIn x.1 hr u
  let F := radialFluxField e Λ x.1 hr u
  let W : ℝ → ℝ := fun t => zIn u 0 - intervalExtension hV (continuousPrimitive hV F) t
  let G : ℝ → ℝ := fun t => Real.exp (intervalExtension hV (x.1 u) t 2) *
    radialPotential (intervalExtension hV (x.1 u) t 0) e Λ / intervalExtension hV N t
  have hWeq (t : ℝ) : W t = -x.1 u (projIcc 0 V hV t) 0 * N (projIcc 0 V hV t) := by
    dsimp only [W, N, F]
    rw [radialNuField_apply]
    simp only [intervalExtension_apply]
    field_simp [hr u (projIcc 0 V hV t)]
    ring
  have hWp (t : ℝ) : 0 < W t := by
    rw [hWeq]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (hrp u _)) (hν u _)
  have hWc : Continuous W := continuous_const.sub (intervalExtension hV (continuousPrimitive hV F)).continuous
  have hGc : Continuous G :=
    ((continuous_apply (0 : Fin 3)).comp (intervalExtension hV (wavePotentialField e Λ (x.1 u) (hr u))).continuous).div
      (intervalExtension hV N).continuous (fun t => ne_of_lt (hν u (projIcc 0 V hV t)))
  have hlog : Continuous (fun t => Real.log (W t)) := hWc.log (fun t => (hWp t).ne')
  have hd (t : ℝ) (ht : t ∈ Icc 0 V) : HasDerivWithinAt (fun s => Real.log (W s)) (G t) (Icc 0 V) t := by
    have hh := ((continuousPrimitive_hasDerivWithinAt hV F ht).const_sub (zIn u 0)).log (hWp t).ne'
    apply hh.congr_deriv
    change -F ⟨t, ht⟩ / W t = G t
    rw [hWeq]
    simp only [F, radialFluxField_apply, G, intervalExtension_apply, projIcc_of_mem hV ht]
    field_simp [hr u ⟨t, ht⟩, ne_of_lt (hν u ⟨t, ht⟩)]
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le v.property.1 hlog.continuousOn
    (fun t ht => (hd t ⟨ht.1.le, ht.2.le.trans v.property.2⟩).hasDerivAt
      (Icc_mem_nhds ht.1 (ht.2.trans_le v.property.2))) (hGc.intervalIntegrable (0 : ℝ) v)
  have he := congrArg Real.exp (show (∫ t in (0 : ℝ)..v, G t) + Real.log (W 0) = Real.log (W v) by linarith only [hp])
  rw [Real.exp_add, Real.exp_log (hWp 0), Real.exp_log (hWp v)] at he
  have hW0 : W 0 = zIn u 0 := by
    dsimp only [W]
    rw [intervalExtension_apply, projIcc_of_mem hV (show (0 : ℝ) ∈ Icc 0 V from ⟨le_rfl, hV⟩)]
    change zIn u 0 - (∫ t in (0 : ℝ)..0, intervalExtension hV F t) = zIn u 0
    simp only [intervalIntegral.integral_same, sub_zero]
  rw [hW0, hWeq, projIcc_of_mem hV v.property] at he
  change x.1 u v 0 * N v = -zIn u 0 * Real.exp (∫ t in (0 : ℝ)..v, G t)
  nlinarith only [he]

set_option maxHeartbeats 400000 in
theorem radialNuField_flux_segment_bound (hr : ∀ u v, x.1 u v 0 ≠ 0)
    (hrp : ∀ u v, 0 < x.1 u v 0)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v < 0)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) {P : ℝ}
    (hP : ∀ w ∈ Icc a b, |radialPotential (x.1 u w 0) e Λ| ≤ P)
    (hκ : ∀ w ∈ Icc a b, -Real.exp (x.1 u w 2) /
      (4 * radialNuField hV e Λ zIn x.1 hr u w) ≤ 1) :
    let N := radialNuField hV e Λ zIn x.1 hr
    Real.exp (-(4 * P) * ((b : ℝ) - a)) * (x.1 u a 0 * (-N u a)) ≤ x.1 u b 0 * (-N u b) ∧
      x.1 u b 0 * (-N u b) ≤ Real.exp (4 * P * ((b : ℝ) - a)) * (x.1 u a 0 * (-N u a)) := by
  let N := radialNuField hV e Λ zIn x.1 hr
  let G : ℝ → ℝ := fun t => Real.exp (intervalExtension hV (x.1 u) t 2) *
    radialPotential (intervalExtension hV (x.1 u) t 0) e Λ / intervalExtension hV (N u) t
  have hGc : Continuous G :=
    ((continuous_apply (0 : Fin 3)).comp (intervalExtension hV
      (wavePotentialField e Λ (x.1 u) (hr u))).continuous).div
        (intervalExtension hV (N u)).continuous (fun t => ne_of_lt (hnu u (projIcc 0 V hV t)))
  have hsplit : (∫ t in (0 : ℝ)..b, G t) = (∫ t in (0 : ℝ)..a, G t) + ∫ t in (a : ℝ)..b, G t :=
    (intervalIntegral.integral_add_adjacent_intervals (hGc.intervalIntegrable _ _)
      (hGc.intervalIntegrable _ _)).symm
  have he : x.1 u b 0 * (-N u b) = x.1 u a 0 * (-N u a) * Real.exp (∫ t in (a : ℝ)..b, G t) := by
    have ha := radialNuField_flux_exponential hr hrp hnu u a
    have hb := radialNuField_flux_exponential hr hrp hnu u b
    change x.1 u a 0 * N u a = -zIn u 0 * Real.exp (∫ t in (0 : ℝ)..a, G t) at ha
    change x.1 u b 0 * N u b = -zIn u 0 * Real.exp (∫ t in (0 : ℝ)..b, G t) at hb
    rw [hsplit, Real.exp_add, ← mul_assoc, ← ha] at hb
    nlinarith only [hb]
  have hi : |∫ t in (a : ℝ)..b, G t| ≤ 4 * P * ((b : ℝ) - a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := G) (C := 4 * P) (a := (a : ℝ)) (b := (b : ℝ)) (fun t ht => ?_)
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (show (a : ℝ) ≤ b from hab)), mul_comm] using hh
    rw [uIoc_of_le (show (a : ℝ) ≤ b from hab)] at ht
    have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.trans b.property.2⟩
    let w : Icc 0 V := ⟨t, htV⟩
    have hw : w ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    have hn : N u w < 0 := hnu u w
    have hratio : Real.exp (x.1 u w 2) / (-N u w) ≤ 4 := by
      have hk := (div_le_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hn)).1 (hκ w hw)
      apply (div_le_iff₀ (neg_pos.2 hn)).2
      nlinarith only [hk]
    change |G t| ≤ 4 * P
    simp only [G, intervalExtension_apply, projIcc_of_mem hV htV]
    change |Real.exp (x.1 u w 2) * radialPotential (x.1 u w 0) e Λ / N u w| ≤ 4 * P
    rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_neg hn]
    calc
      _ = (Real.exp (x.1 u w 2) / (-N u w)) * |radialPotential (x.1 u w 0) e Λ| := by ring
      _ ≤ _ := mul_le_mul hratio (hP w hw) (abs_nonneg _) (by norm_num)
  have hpos : 0 ≤ x.1 u a 0 * (-N u a) := (mul_pos (hrp u a) (neg_pos.2 (hnu u a))).le
  change Real.exp (-(4 * P) * ((b : ℝ) - a)) * (x.1 u a 0 * (-N u a)) ≤ x.1 u b 0 * (-N u b) ∧
    x.1 u b 0 * (-N u b) ≤ Real.exp (4 * P * ((b : ℝ) - a)) * (x.1 u a 0 * (-N u a))
  rw [he]
  constructor
  · rw [mul_comm (Real.exp (-(4 * P) * ((b : ℝ) - a)))]
    apply mul_le_mul_of_nonneg_left _ hpos
    apply Real.exp_le_exp.2
    simpa only [neg_mul] using (abs_le.1 hi).1
  · rw [mul_comm (Real.exp (4 * P * ((b : ℝ) - a)))]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (abs_le.1 hi).2) hpos

end CauchyHorizon
