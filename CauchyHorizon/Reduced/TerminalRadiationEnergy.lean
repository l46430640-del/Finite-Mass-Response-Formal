import CauchyHorizon.Reduced.RadiationEnergy

/-! Time reflection transfers the causal energy bound to a terminal kernel. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem terminalExpIntegral_add_energy {V d C l w : ℝ} (hV : 0 ≤ V) (hd : 0 < d)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hw : w ≤ V) (M : C(Icc 0 V, ℝ))
    {F G : ℝ → ℝ} (hF : ContinuousOn F (Icc l w)) (hG : ContinuousOn G (Icc l w))
    (hb : ∀ t ∈ Icc l w, |F t| ≤ |G t| + C *
      ∫ v in t..V, Real.exp (-d * (v - t)) * M (projIcc 0 V hV v)) :
    (∫ t in l..w, F t ^ 2) ≤ 2 * (∫ t in l..w, G t ^ 2) +
      2 * (C / d) ^ 2 * ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  let R : C(Icc 0 V, ℝ) := ⟨fun v => M (projIcc 0 V hV (V - v)), by fun_prop⟩
  obtain ⟨hQc, hQe⟩ := causalExpIntegral_energy hV hd R
  let Q := fun t => causalExpIntegral hV d R (projIcc 0 V hV (V - t))
  have hQcont : Continuous Q := by dsimp only [Q]; fun_prop
  have heq (t : ℝ) (ht : t ∈ Icc 0 V) : Q t =
      ∫ v in t..V, Real.exp (-d * (v - t)) * M (projIcc 0 V hV v) := by
    have hr : V - t ∈ Icc 0 V := ⟨sub_nonneg.2 ht.2, sub_le_self _ ht.1⟩
    dsimp only [Q, causalExpIntegral]
    rw [projIcc_of_mem hV hr]
    calc
      _ = ∫ s in (0 : ℝ)..(V - t),
          Real.exp (-d * ((V - s) - t)) * M (projIcc 0 V hV (V - s)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hr.1] at hs
        simp only [R, ContinuousMap.coe_mk, projIcc_of_mem hV (Icc_subset_Icc le_rfl hr.2 hs)]
        congr 2
        ring
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left
          (fun v => Real.exp (-d * (v - t)) * M (projIcc 0 V hV v)) V]
        simp only [sub_sub_cancel, sub_zero]
  have hQR : (∫ t in (0 : ℝ)..V, Q t ^ 2) =
      ∫ t in (0 : ℝ)..V, (causalExpIntegral hV d R (projIcc 0 V hV t)) ^ 2 := by
    dsimp only [Q]
    rw [intervalIntegral.integral_comp_sub_left
      (fun t => (causalExpIntegral hV d R (projIcc 0 V hV t)) ^ 2) V]
    simp only [sub_self, sub_zero]
  have hMR : (∫ t in (0 : ℝ)..V, (R (projIcc 0 V hV t)) ^ 2) =
      ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV (V - t))) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hV] at ht
        simp only [R, ContinuousMap.coe_mk, projIcc_of_mem hV ht]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left (fun t => (M (projIcc 0 V hV t)) ^ 2) V]
        simp only [sub_self, sub_zero]
  rw [← hQR, hMR] at hQe
  have hQi := (hQcont.pow 2).intervalIntegrable (μ := volume) l w
  have hGi := (hG.pow 2).intervalIntegrable_of_Icc (μ := volume) hlw
  have hs := intervalIntegral.integral_mono_on hlw ((hF.pow 2).intervalIntegrable_of_Icc hlw)
    ((hGi.const_mul 2).add (hQi.const_mul (2 * C ^ 2))) (fun t ht => ?_)
  · rw [intervalIntegral.integral_add (hGi.const_mul 2) (hQi.const_mul (2 * C ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hs
    have hsub := intervalIntegral.integral_mono_interval (μ := volume) hl hlw hw
      (Filter.Eventually.of_forall (fun t => sq_nonneg (Q t))) ((hQcont.pow 2).intervalIntegrable 0 V)
    have hE := mul_le_mul_of_nonneg_left hQe (by positivity : 0 ≤ 2 * (C / d) ^ 2)
    have hcancel : 2 * (C / d) ^ 2 * d ^ 2 = 2 * C ^ 2 := by field_simp [hd.ne']
    rw [← mul_assoc, hcancel] at hE
    exact hs.trans (add_le_add_right
      ((mul_le_mul_of_nonneg_left hsub (by positivity)).trans hE) _)
  · have hh := hb t ht
    change F t ^ 2 ≤ 2 * G t ^ 2 + 2 * C ^ 2 * Q t ^ 2
    rw [← heq t (Icc_subset_Icc hl hw ht)] at hh
    have hsq := (sq_le_sq₀ (abs_nonneg (F t)) ((abs_nonneg (F t)).trans hh)).2 hh
    nlinarith only [hsq, sq_abs (F t), sq_abs (G t), sq_nonneg (|G t| - C * Q t)]

end CauchyHorizon
