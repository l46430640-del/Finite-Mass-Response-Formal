import CauchyHorizon.Reduced.ScalarTransport
import CauchyHorizon.Reduced.RadialBoundary

/-! Compact transverse scalar traces from the actual vertical transport integral. -/

open Set MeasureTheory

namespace CauchyHorizon

theorem scalarTransportCorrection_prefix_eq {U S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hST : S ≤ T) (N : C(Icc 0 U, C(Icc 0 S, ℝ))) (M : C(Icc 0 U, C(Icc 0 T, ℝ)))
    (w : WaveRectangle U S) (z : WaveRectangle U T)
    (hN : ∀ u v, N u v = M u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (hw : ∀ u v, w u v = z u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (u : Icc 0 U) (v : Icc 0 S) :
    scalarTransportCorrection hS N w u v =
      scalarTransportCorrection hT M z u ⟨v, v.property.1, v.property.2.trans hST⟩ := by
  change (∫ t in (0 : ℝ)..(v : ℝ), _) = ∫ t in (0 : ℝ)..(v : ℝ), _
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le v.property.1] at ht
  have htS : t ∈ Icc 0 S := ⟨ht.1, ht.2.trans v.property.2⟩
  have htT : t ∈ Icc 0 T := ⟨htS.1, htS.2.trans hST⟩
  simp only [intervalExtension_apply, projIcc_of_mem hS htS, projIcc_of_mem hT htT]
  change -N u ⟨t, htS⟩ * w u ⟨t, htS⟩ 1 = -M u ⟨t, htT⟩ * z u ⟨t, htT⟩ 1
  rw [hN, hw]

theorem scalarTransportCorrection_tail_bound {U V C η : ℝ} (hV : 0 ≤ V)
    (N : C(Icc 0 U, C(Icc 0 V, ℝ))) (w : WaveRectangle U V)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (hC : 0 ≤ C) (hη : 0 < η)
    (hdec : ∀ t ∈ Icc a b, |N u t * w u t 1| ≤ C * Real.exp (-η * t)) :
    |scalarTransportCorrection hV N w u b - scalarTransportCorrection hV N w u a| ≤
      C / η * Real.exp (-η * a) := by
  let F := scalarTransportSource N w u
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((intervalExtension hV F).continuous.intervalIntegrable (0 : ℝ) a)
    ((intervalExtension hV F).continuous.intervalIntegrable (a : ℝ) b)
  have hd : scalarTransportCorrection hV N w u b - scalarTransportCorrection hV N w u a =
      ∫ t in (a : ℝ)..b, intervalExtension hV F t := by
    change (∫ t in (0 : ℝ)..(b : ℝ), intervalExtension hV F t) -
      (∫ t in (0 : ℝ)..(a : ℝ), intervalExtension hV F t) = _
    linarith only [hs]
  rw [hd]
  have hec : Continuous (fun t : ℝ => C * Real.exp (-η * t)) := by fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (show (a : ℝ) ≤ b from hab) (f := intervalExtension hV F) (g := fun t => C * Real.exp (-η * t))
    (Filter.Eventually.of_forall (by
      intro t ht
      have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.trans b.property.2⟩
      have hh := hdec ⟨t, htV⟩ ⟨ht.1.le, ht.2⟩
      simp only [Real.norm_eq_abs, intervalExtension_apply, projIcc_of_mem hV htV]
      change |-N u ⟨t, htV⟩ * w u ⟨t, htV⟩ 1| ≤ _
      simpa only [neg_mul, abs_neg] using hh)) (hec.intervalIntegrable _ _)
  rw [Real.norm_eq_abs] at hi
  apply hi.trans
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ (neg_ne_zero.2 hη.ne'), integral_exp, smul_eq_mul]
  have hh := mul_nonneg (div_nonneg hC hη.le) (Real.exp_pos (-η * (b : ℝ))).le
  simp only [inv_neg, div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

end CauchyHorizon
