import CauchyHorizon.Reduced.OuterRadiation
import CauchyHorizon.Analysis.IntegratingFactor

/-! The causal exponential kernel has a terminal-time-independent L2 bound. -/

open MeasureTheory Set

namespace CauchyHorizon

noncomputable def causalExpIntegralFrom {V : ℝ} (hV : 0 ≤ V) (l d : ℝ)
    (M : C(Icc 0 V, ℝ)) (v : Icc 0 V) : ℝ :=
  ∫ t in l..v, Real.exp (-d * ((v : ℝ) - t)) * M (projIcc 0 V hV t)

theorem causalExpIntegralFrom_energy {V d l w : ℝ} (hV : 0 ≤ V) (hd : 0 < d)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hw : w ≤ V)
    (M : C(Icc 0 V, ℝ)) :
    Continuous (causalExpIntegralFrom hV l d M) ∧
      d ^ 2 * (∫ t in l..w, (causalExpIntegralFrom hV l d M (projIcc 0 V hV t)) ^ 2) ≤
        ∫ t in l..w, (M (projIcc 0 V hV t)) ^ 2 := by
  let m := fun t => M (projIcc 0 V hV t)
  let g := fun t => Real.exp (d * t) * m t
  let q := fun t => Real.exp (-d * t) * ∫ s in l..t, g s
  have hmc : Continuous m := by fun_prop
  have hgc : Continuous g := by fun_prop
  have hgi := hgc.intervalIntegrable (μ := volume) l w
  have hpc : ContinuousOn (fun t => ∫ s in l..t, g s) (Icc 0 V) := by
    simpa only [uIcc_of_le hV] using
      intervalIntegral.continuousOn_primitive_interval' (hgc.intervalIntegrable (μ := volume) 0 V)
        (show l ∈ uIcc (0 : ℝ) V by rw [uIcc_of_le hV]; exact ⟨hl, hlw.trans hw⟩)
  have hqc : ContinuousOn q (Icc 0 V) := by unfold q; fun_prop
  have hqc' : ContinuousOn q (Icc l w) := hqc.mono (Icc_subset_Icc hl hw)
  have heq (v : Icc 0 V) : causalExpIntegralFrom hV l d M v = q v := by
    unfold causalExpIntegralFrom
    dsimp only [q]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [g, m]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hqd (t : ℝ) (ht : t ∈ Ioo l w) : HasDerivAt q (m t - d * q t) t := by
    have he := ((hasDerivAt_id t).const_mul (-d)).exp
    have hp := primitive_hasDerivAt_interior hgi hgc.continuousOn ht
    have hec : Real.exp (-d * t) * Real.exp (d * t) = 1 := by
      rw [← Real.exp_add, ← add_mul, neg_add_cancel, zero_mul, Real.exp_zero]
    apply (he.mul hp).congr_deriv
    dsimp only [q, g, id_eq]
    nlinarith only [congrArg (fun z => z * m t) hec]
  have hql : q l = 0 := by simp [q]
  have hqi : IntervalIntegrable (fun t => q t ^ 2) volume l w :=
    (hqc'.pow 2).intervalIntegrable_of_Icc hlw
  have hmi : IntervalIntegrable (fun t => m t ^ 2) volume l w :=
    (hmc.pow 2).intervalIntegrable _ _
  have hdi : IntervalIntegrable (fun t => d * (2 * q t * (m t - d * q t))) volume l w := by
    have hdc : ContinuousOn (fun t => d * (2 * q t * (m t - d * q t))) (Icc l w) := by fun_prop
    exact hdc.intervalIntegrable_of_Icc hlw
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun t => d * q t ^ 2) hlw
    ((hqc'.pow 2).const_mul d)
    (fun t ht => by
      exact (((hqd t ht).pow 2).const_mul d).congr_deriv (by norm_num)) hdi
  have hb := intervalIntegral.integral_mono_on hlw hdi (hmi.sub (hqi.const_mul (d ^ 2)))
    (fun t _ => by nlinarith only [sq_nonneg (m t - d * q t)])
  rw [hI, intervalIntegral.integral_sub hmi (hqi.const_mul (d ^ 2)),
    intervalIntegral.integral_const_mul, hql, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, sub_zero] at hb
  have henergy : d ^ 2 * (∫ t in l..w, q t ^ 2) ≤ ∫ t in l..w, m t ^ 2 := by
    nlinarith only [hb, mul_nonneg hd.le (sq_nonneg (q w))]
  refine ⟨hqc.domRestrict.congr (fun v => (heq v).symm), ?_⟩
  have hQ : (∫ t in l..w, (causalExpIntegralFrom hV l d M (projIcc 0 V hV t)) ^ 2) =
      ∫ t in l..w, q t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlw] at ht
    dsimp only
    rw [projIcc_of_mem hV (Icc_subset_Icc hl hw ht), heq]
  rw [hQ]
  exact henergy

theorem causalExpIntegral_energy {V d : ℝ} (hV : 0 ≤ V) (hd : 0 < d)
    (M : C(Icc 0 V, ℝ)) :
    Continuous (causalExpIntegral hV d M) ∧
      d ^ 2 * (∫ t in (0 : ℝ)..V, (causalExpIntegral hV d M (projIcc 0 V hV t)) ^ 2) ≤
        ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 :=
  causalExpIntegralFrom_energy hV hd le_rfl hV le_rfl M

theorem causalExpIntegral_dominated_energy {V d C l w : ℝ} (hV : 0 ≤ V) (hd : 0 < d)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hw : w ≤ V) (M : C(Icc 0 V, ℝ))
    {F : ℝ → ℝ} (hc : ContinuousOn F (Icc l w))
    (hb : ∀ t ∈ Icc l w, |F t| ≤ C * causalExpIntegral hV d M (projIcc 0 V hV t)) :
    (∫ t in l..w, F t ^ 2) ≤
      (C / d) ^ 2 * ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  obtain ⟨hQc, hQe⟩ := causalExpIntegral_energy hV hd M
  let Q := fun t => causalExpIntegral hV d M (projIcc 0 V hV t)
  have hQi : Continuous (fun t => Q t ^ 2) := by dsimp only [Q]; fun_prop
  have hsq (t : ℝ) (ht : t ∈ Icc l w) : F t ^ 2 ≤ C ^ 2 * Q t ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (F t)) ((abs_nonneg (F t)).trans (hb t ht))).2 (hb t ht)
    simpa only [sq_abs, mul_pow] using hh
  have he := intervalIntegral.integral_mono_on (μ := volume) hlw
    ((hc.pow 2).intervalIntegrable_of_Icc hlw)
    ((hQi.const_mul (C ^ 2)).intervalIntegrable _ _) hsq
  rw [intervalIntegral.integral_const_mul] at he
  have he' := intervalIntegral.integral_mono_interval (μ := volume) hl hlw hw
    (Filter.Eventually.of_forall (fun t => sq_nonneg (Q t))) (hQi.intervalIntegrable 0 V)
  have he'' := he.trans (mul_le_mul_of_nonneg_left he' (sq_nonneg C))
  have hk := mul_le_mul_of_nonneg_left hQe (sq_nonneg (C / d))
  have hcancel : (C / d) ^ 2 * d ^ 2 = C ^ 2 := by field_simp [hd.ne']
  rw [← mul_assoc, hcancel] at hk
  exact he''.trans hk

theorem causalExpIntegralFrom_absorb_sq {V d ε l w : ℝ} (hV : 0 ≤ V) (hd : 0 < d)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hw : w ≤ V)
    (hε : 0 ≤ ε) (hsmall : ε ≤ d / 2) (M : C(Icc 0 V, ℝ))
    (hM : ∀ v, 0 ≤ M v) {F : ℝ → ℝ}
    (hF : IntervalIntegrable (fun t => F t ^ 2) volume l w)
    (hb : ∀ v : Icc 0 V, (v : ℝ) ∈ Icc l w → M v ≤ F v + ε * causalExpIntegralFrom hV l d M v) :
    (∫ t in l..w, (M (projIcc 0 V hV t)) ^ 2) ≤
      4 * ∫ t in l..w, F t ^ 2 := by
  obtain ⟨hc, henergy⟩ := causalExpIntegralFrom_energy hV hd hl hlw hw M
  let Q := fun t => causalExpIntegralFrom hV l d M (projIcc 0 V hV t)
  have hQi : IntervalIntegrable (fun t => Q t ^ 2) volume l w :=
    ((hc.comp continuous_projIcc).pow 2).intervalIntegrable _ _
  have hMi : IntervalIntegrable (fun t => (M (projIcc 0 V hV t)) ^ 2) volume l w := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hb2 := intervalIntegral.integral_mono_on hlw hMi
    ((hF.const_mul 2).add (hQi.const_mul (2 * ε ^ 2))) (fun t ht => ?_)
  · rw [intervalIntegral.integral_add (hF.const_mul 2) (hQi.const_mul (2 * ε ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hb2
    have hcoef : 2 * ε ^ 2 ≤ d ^ 2 / 2 := by
      nlinarith only [sq_le_sq₀ hε (by positivity) |>.2 hsmall]
    have hQI0 : 0 ≤ ∫ t in l..w, Q t ^ 2 :=
      intervalIntegral.integral_nonneg hlw (fun t _ => sq_nonneg (Q t))
    have hh := mul_le_mul_of_nonneg_right hcoef hQI0
    change d ^ 2 * (∫ t in l..w, Q t ^ 2) ≤ _ at henergy
    nlinarith only [hb2, hh, henergy]
  · have htV := Icc_subset_Icc hl hw ht
    rw [projIcc_of_mem hV htV]
    have hs := (sq_le_sq₀ (hM ⟨t, htV⟩) ((hM ⟨t, htV⟩).trans (hb ⟨t, htV⟩ ht))).2 (hb ⟨t, htV⟩ ht)
    have hQ : Q t = causalExpIntegralFrom hV l d M ⟨t, htV⟩ := by
      dsimp only [Q]
      rw [projIcc_of_mem hV htV]
    rw [hQ]
    nlinarith only [hs, sq_nonneg (F t - ε * causalExpIntegralFrom hV l d M ⟨t, htV⟩)]

theorem causalExpIntegral_absorb_sq {V d ε : ℝ} (hV : 0 ≤ V) (hd : 0 < d)
    (hε : 0 ≤ ε) (hsmall : ε ≤ d / 2) (M : C(Icc 0 V, ℝ))
    (hM : ∀ v, 0 ≤ M v) {F : ℝ → ℝ}
    (hF : IntervalIntegrable (fun t => F t ^ 2) volume 0 V)
    (hb : ∀ v : Icc 0 V, M v ≤ F v + ε * causalExpIntegral hV d M v) :
    (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
      4 * ∫ t in (0 : ℝ)..V, F t ^ 2 :=
  causalExpIntegralFrom_absorb_sq hV hd le_rfl hV le_rfl hε hsmall M hM hF (fun v _ => hb v)

theorem causalExpIntegralFrom_forcing_energy {V k C ε : ℝ}
    (hV : 0 ≤ V) (hk : 0 < k) (hε : 0 ≤ ε) (hsmall : ε ≤ k / 2)
    (l : Icc 0 V) (H A M : C(Icc 0 V, ℝ)) (hM : ∀ v, 0 ≤ M v)
    (hb : ∀ v, l ≤ v → M v ≤ H v + C * causalExpIntegralFrom hV l k A v +
      ε * causalExpIntegralFrom hV l k M v) :
    (∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
      8 * (∫ t in (l : ℝ)..V, (H (projIcc 0 V hV t)) ^ 2) +
        8 * (C / k) ^ 2 * ∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2 := by
  obtain ⟨hQc, hQE⟩ := causalExpIntegralFrom_energy hV hk l.property.1 l.property.2 le_rfl A
  let Q := fun t => causalExpIntegralFrom hV l k A (projIcc 0 V hV t)
  let h := fun t => H (projIcc 0 V hV t)
  let F := fun t => h t + C * Q t
  have hhc : Continuous h := by fun_prop
  have hqc : Continuous Q := by dsimp only [Q]; fun_prop
  have hFc : Continuous F := by dsimp only [F]; fun_prop
  have hFi : IntervalIntegrable (fun t => F t ^ 2) volume l V := (hFc.pow 2).intervalIntegrable l V
  have hhi : IntervalIntegrable (fun t => h t ^ 2) volume l V := (hhc.pow 2).intervalIntegrable l V
  have hqi : IntervalIntegrable (fun t => Q t ^ 2) volume l V := (hqc.pow 2).intervalIntegrable l V
  have habs := causalExpIntegralFrom_absorb_sq hV hk l.property.1 l.property.2 le_rfl
    hε hsmall M hM hFi (fun v hv => by
      simpa only [F, h, Q, projIcc_of_mem hV v.property] using hb v hv.1)
  have hforce := intervalIntegral.integral_mono_on l.property.2 hFi
    ((hhi.const_mul 2).add (hqi.const_mul (2 * C ^ 2)))
    (fun t _ => by dsimp only [F]; nlinarith only [sq_nonneg (h t - C * Q t)])
  rw [intervalIntegral.integral_add (hhi.const_mul 2) (hqi.const_mul (2 * C ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hforce
  have hQbound := mul_le_mul_of_nonneg_left hQE (sq_nonneg (C / k))
  have hcancel : (C / k) ^ 2 * k ^ 2 = C ^ 2 := by field_simp [hk.ne']
  rw [← mul_assoc, hcancel] at hQbound
  change C ^ 2 * (∫ t in (l : ℝ)..V, Q t ^ 2) ≤ _ at hQbound
  change (∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
    8 * (∫ t in (l : ℝ)..V, h t ^ 2) +
      8 * (C / k) ^ 2 * ∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2
  nlinarith only [habs, hforce, hQbound]

theorem causalExpIntegralFrom_weighted_le {V k q d : ℝ} (hV : 0 ≤ V) (hqd : q ≤ d)
    (l s b : Icc 0 V) (hls : l ≤ s) (hsb : s ≤ b)
    (A : C(Icc 0 V, ℝ)) (hA : ∀ v, 0 ≤ A v) :
    Real.exp (q * b) * (∫ t in (s : ℝ)..b,
      Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-d * t) * A (projIcc 0 V hV t)) ≤
        causalExpIntegralFrom hV l (k - q) A b := by
  let F := fun t => Real.exp (-(k - q) * ((b : ℝ) - t)) * A (projIcc 0 V hV t)
  have hFc : Continuous F := by fun_prop
  rw [← intervalIntegral.integral_const_mul]
  calc
    _ ≤ ∫ t in (s : ℝ)..b, F t := by
      apply intervalIntegral.integral_mono_on (show (s : ℝ) ≤ b from hsb)
        ((by fun_prop : Continuous _).intervalIntegrable _ _) (hFc.intervalIntegrable _ _)
      intro t ht
      have he : Real.exp (q * b) * (Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-d * t)) =
          Real.exp (-(k - q) * ((b : ℝ) - t)) * Real.exp (-(d - q) * t) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [← mul_assoc, he]
      have hw : Real.exp (-(d - q) * t) ≤ 1 := Real.exp_le_one_iff.2
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sub_nonneg.2 hqd)) (s.property.1.trans ht.1))
      simpa only [F, mul_one, mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le) (hA (projIcc 0 V hV t))
    _ ≤ _ := intervalIntegral.integral_mono_interval (show (l : ℝ) ≤ s from hls)
      (show (s : ℝ) ≤ b from hsb) le_rfl
      (Filter.Eventually.of_forall (fun t => mul_nonneg (Real.exp_pos _).le (hA _)))
      (hFc.intervalIntegrable _ _)

theorem causalExpIntegralFrom_sum_energy {V k c d : ℝ} (hV : 0 ≤ V) (hk : 0 < k)
    (l : Icc 0 V) (A M F : C(Icc 0 V, ℝ)) (hF : ∀ v, 0 ≤ F v)
    (hb : ∀ v, l ≤ v → F v ≤ c * causalExpIntegralFrom hV l k A v +
      d * causalExpIntegralFrom hV l k M v) :
    (∫ t in (l : ℝ)..V, (F (projIcc 0 V hV t)) ^ 2) ≤
      2 * (c / k) ^ 2 * (∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2) +
        2 * (d / k) ^ 2 * ∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  obtain ⟨hQA, hEA⟩ := causalExpIntegralFrom_energy hV hk l.property.1 l.property.2 le_rfl A
  obtain ⟨hQM, hEM⟩ := causalExpIntegralFrom_energy hV hk l.property.1 l.property.2 le_rfl M
  let QA := fun t => causalExpIntegralFrom hV l k A (projIcc 0 V hV t)
  let QM := fun t => causalExpIntegralFrom hV l k M (projIcc 0 V hV t)
  have hiA : IntervalIntegrable (fun t => QA t ^ 2) volume l V :=
    ((hQA.comp continuous_projIcc).pow 2).intervalIntegrable _ _
  have hiM : IntervalIntegrable (fun t => QM t ^ 2) volume l V :=
    ((hQM.comp continuous_projIcc).pow 2).intervalIntegrable _ _
  have hsum := intervalIntegral.integral_mono_on (μ := volume) l.property.2
    ((by fun_prop : Continuous (fun t => (F (projIcc 0 V hV t)) ^ 2)).intervalIntegrable _ _)
    ((hiA.const_mul (2 * c ^ 2)).add (hiM.const_mul (2 * d ^ 2))) (fun t ht => by
      have htV : t ∈ Icc 0 V := ⟨l.property.1.trans ht.1, ht.2⟩
      have hbound := hb (projIcc 0 V hV t) (by rw [projIcc_of_mem hV htV]; exact ht.1)
      have hs := (sq_le_sq₀ (hF _) ((hF _).trans hbound)).2 hbound
      change (F (projIcc 0 V hV t)) ^ 2 ≤ 2 * c ^ 2 * QA t ^ 2 + 2 * d ^ 2 * QM t ^ 2
      nlinarith only [hs, sq_nonneg (c * QA t - d * QM t)])
  change (∫ t in (l : ℝ)..V, (F (projIcc 0 V hV t)) ^ 2) ≤
    ∫ t in (l : ℝ)..V, 2 * c ^ 2 * QA t ^ 2 + 2 * d ^ 2 * QM t ^ 2 at hsum
  rw [intervalIntegral.integral_add (hiA.const_mul _) (hiM.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hsum
  have hA := mul_le_mul_of_nonneg_left hEA (sq_nonneg (c / k))
  have hM := mul_le_mul_of_nonneg_left hEM (sq_nonneg (d / k))
  have hcancel (C : ℝ) : (C / k) ^ 2 * k ^ 2 = C ^ 2 := by field_simp [hk.ne']
  rw [← mul_assoc, hcancel] at hA hM
  linarith only [hsum, hA, hM]

end CauchyHorizon
