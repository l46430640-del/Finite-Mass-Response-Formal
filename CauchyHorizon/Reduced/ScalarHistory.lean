import CauchyHorizon.Reduced.OuterScalar

/-! The scalar history with growth before entry and decay after entry. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem scalarTransportCorrection_two_amplitudes {U V a c q N M E H : ℝ} {hV : 0 ≤ V}
    (hac : c < a) (hqc : 0 < q + c) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hE : 0 ≤ E) (hH : 0 ≤ H)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (w : WaveRectangle U V)
    (u : Icc 0 U) (T b : Icc 0 V) (hTb : T ≤ b)
    (hpre : ∀ v ≤ T, |ν u v| ≤ N * Real.exp (a * v))
    (hpost : ∀ v ∈ Icc T b,
      |ν u v| ≤ M * Real.exp (-q * ((v : ℝ) - T)))
    (hwpre : ∀ v ≤ T, |w u v 1| ≤ E * Real.exp (-c * v))
    (hwpost : ∀ v ∈ Icc T b, |w u v 1| ≤ H * Real.exp (-c * v)) :
    |scalarTransportCorrection hV ν w u b| ≤
      N * E / (a - c) * Real.exp ((a - c) * T) +
        M * H / (q + c) * Real.exp (-c * T) := by
  let F := fun t => -ν u (projIcc 0 V hV t) * w u (projIcc 0 V hV t) 1
  have hFc : Continuous F := by fun_prop
  have hd : 0 < a - c := sub_pos.2 hac
  have hNE := mul_nonneg hN hE
  have hpreI : |∫ t in (0 : ℝ)..T, F t| ≤
      N * E / (a - c) * Real.exp ((a - c) * T) := by
    have hi : IntervalIntegrable (fun t : ℝ => N * E * Real.exp ((a - c) * t)) volume 0 T :=
      (by fun_prop : Continuous (fun t : ℝ => N * E * Real.exp ((a - c) * t))).intervalIntegrable _ _
    have hb := intervalIntegral.norm_integral_le_of_norm_le T.property.1
      (f := F) (g := fun t => N * E * Real.exp ((a - c) * t))
      (Filter.Eventually.of_forall (fun t ht => ?_)) hi
    · rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left _ hd.ne', integral_exp,
        mul_zero, Real.exp_zero, smul_eq_mul] at hb
      apply hb.trans
      have hp := mul_nonneg hNE (inv_nonneg.2 hd.le)
      rw [div_eq_mul_inv]
      nlinarith only [hp]
    · have htV : t ∈ Icc 0 V := ⟨ht.1.le, ht.2.trans T.property.2⟩
      simp only [F, Real.norm_eq_abs, abs_mul, abs_neg, projIcc_of_mem hV htV]
      calc
        _ ≤ (N * Real.exp (a * t)) * (E * Real.exp (-c * t)) :=
          mul_le_mul (hpre ⟨t, htV⟩ ht.2) (hwpre ⟨t, htV⟩ ht.2)
            (abs_nonneg _) (mul_nonneg hN (Real.exp_pos _).le)
        _ = _ := by rw [mul_mul_mul_comm, ← Real.exp_add]; congr 2; ring
  let C := M * H * Real.exp (q * T)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hM hH) (Real.exp_pos _).le
  have hpostI : |∫ t in (T : ℝ)..b, F t| ≤
      M * H / (q + c) * Real.exp (-c * T) := by
    have hi : IntervalIntegrable (fun t : ℝ => C * Real.exp (-(q + c) * t)) volume T b :=
      (by fun_prop : Continuous (fun t : ℝ => C * Real.exp (-(q + c) * t))).intervalIntegrable _ _
    have hb := intervalIntegral.norm_integral_le_of_norm_le (show (T : ℝ) ≤ b from hTb)
      (f := F) (g := fun t => C * Real.exp (-(q + c) * t))
      (Filter.Eventually.of_forall (fun t ht => ?_)) hi
    · rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.mpr hqc.ne'),
        integral_exp, smul_eq_mul] at hb
      calc
        _ ≤ C * ((-(q + c))⁻¹ *
            (Real.exp (-(q + c) * b) - Real.exp (-(q + c) * T))) := hb
        _ ≤ C / (q + c) * Real.exp (-(q + c) * T) := by
          rw [inv_neg, div_eq_mul_inv]
          have hp := mul_nonneg (mul_nonneg hC (inv_nonneg.2 hqc.le)) (Real.exp_pos (-(q + c) * b)).le
          nlinarith only [hp]
        _ = _ := by
          dsimp only [C]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          calc
            _ = (M * H * (q + c)⁻¹) *
                (Real.exp (q * T) * Real.exp (-(q + c) * T)) := by ring
            _ = _ := by rw [← Real.exp_add]; congr 2; ring
    · have htV : t ∈ Icc 0 V := ⟨T.property.1.trans ht.1.le, ht.2.trans b.property.2⟩
      simp only [F, Real.norm_eq_abs, abs_mul, abs_neg, projIcc_of_mem hV htV]
      calc
        _ ≤ (M * Real.exp (-q * (t - T))) * (H * Real.exp (-c * t)) :=
          mul_le_mul (hpost ⟨t, htV⟩ ⟨ht.1.le, ht.2⟩) (hwpost ⟨t, htV⟩ ⟨ht.1.le, ht.2⟩)
            (abs_nonneg _) (by positivity)
        _ = _ := by
          dsimp only [C]
          calc
            _ = M * H * (Real.exp (-q * (t - T)) * Real.exp (-c * t)) := by ring
            _ = _ := by rw [← Real.exp_add, mul_assoc (M * H), ← Real.exp_add]; congr 2; ring
  change |∫ t in (0 : ℝ)..b, F t| ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hFc.intervalIntegrable (0 : ℝ) T) (hFc.intervalIntegrable (T : ℝ) b)]
  exact (abs_add_le _ _).trans (add_le_add hpreI hpostI)

theorem scalarTransportCorrection_split_bound {U V a c q N H : ℝ} {hV : 0 ≤ V}
    (hac : c < a) (hqc : 0 < q + c) (hN : 0 ≤ N) (hH : 0 ≤ H)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (w : WaveRectangle U V)
    (u : Icc 0 U) (T b : Icc 0 V) (hTb : T ≤ b)
    (hpre : ∀ v ≤ T, |ν u v| ≤ N * Real.exp (a * v))
    (hpost : ∀ v ∈ Icc T b,
      |ν u v| ≤ N * Real.exp (a * T) * Real.exp (-q * ((v : ℝ) - T)))
    (hw : ∀ v ≤ b, |w u v 1| ≤ H * Real.exp (-c * v)) :
    |scalarTransportCorrection hV ν w u b| ≤
      N * H * (1 / (a - c) + 1 / (q + c)) * Real.exp ((a - c) * T) := by
  apply (scalarTransportCorrection_two_amplitudes hac hqc hN
    (mul_nonneg hN (Real.exp_pos _).le) hH hH ν w u T b hTb hpre hpost
    (fun v hv => hw v (hv.trans hTb)) (fun v hv => hw v hv.2)).trans_eq
  have he : Real.exp (a * T) * Real.exp (-c * T) = Real.exp ((a - c) * T) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    _ = N * H / (a - c) * Real.exp ((a - c) * T) +
        N * H / (q + c) * (Real.exp (a * T) * Real.exp (-c * T)) := by ring
    _ = _ := by rw [he]; ring

end CauchyHorizon
