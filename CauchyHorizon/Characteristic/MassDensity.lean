import CauchyHorizon.Reduced.MassCoefficientContinuity
import CauchyHorizon.Analysis.Quadratic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Strong convergence of the mass density, retaining the actual reference field. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

def MassDensityLimit {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (C R H : ℕ → ℝ → C(K, ℝ)) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧ ∃ Q : C(K, ℝ), Tendsto (C 0) atTop (𝓝 Q) ∧
    (∀ n, IntegrableOn (fun t => C n t * R n t ^ 2) (Ici T) ∧
      IntegrableOn (fun t => C n t * R n t ^ 2 - C 0 t * R 0 t ^ 2 - Q * H n t ^ 2) (Ici T)) ∧
    Tendsto (fun n => ∫ t in Ici T,
      ‖C n t * R n t ^ 2 - C 0 t * R 0 t ^ 2 - Q * H n t ^ 2‖) atTop (𝓝 0)

set_option maxHeartbeats 1600000 in
theorem mass_density_limit {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {C R H : ℕ → ℝ → C(K, ℝ)} {ER EH : ℝ}
    (hC : ∀ n, ContinuousOn (C n) (Ici 0)) (hcontrol : MassCoefficientControl C)
    (hR : ∀ n, MemLp (R n) 2 (volume.restrict (Ici 0)))
    (hH : ∀ n, MemLp (H n) 2 (volume.restrict (Ici 0)))
    (hRE : ∀ n, (∫ t in Ici (0 : ℝ), ‖R n t‖ ^ 2) ≤ ER)
    (hHE : ∀ n, (∫ t in Ici (0 : ℝ), ‖H n t‖ ^ 2) ≤ EH)
    (herror : Tendsto (fun n => ∫ t in Ici (0 : ℝ), ‖R n t - R 0 t - H n t‖ ^ 2) atTop (𝓝 0))
    (hvanish : ∀ S : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) S, H n t = 0) :
    MassDensityLimit C R H := by
  obtain ⟨T, M, L, η, hT, hM, hL, hη, Q, hQt, hbound, _hQpos, hQseq, hCseq⟩ := hcontrol
  let μ := volume.restrict (Ici T)
  have hsub : Ici T ⊆ Ici (0 : ℝ) := Ici_subset_Ici.2 hT
  have hR' (n : ℕ) := (hR n).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hH' (n : ℕ) := (hH n).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hRi (n : ℕ) : IntegrableOn (fun t => ‖R n t‖ ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq_norm (hR n).1).1 (hR n)
  have hHi (n : ℕ) : IntegrableOn (fun t => ‖H n t‖ ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq_norm (hH n).1).1 (hH n)
  have hsqnorm (x : C(K, ℝ)) : ‖x ^ 2‖ ≤ ‖x‖ ^ 2 := by
    simpa only [pow_two] using norm_mul_le x x
  have henergy {F : ℝ → C(K, ℝ)} {E S : ℝ} (hS : 0 ≤ S)
      (hi : IntegrableOn (fun t => ‖F t‖ ^ 2) (Ici 0)) (he : (∫ t in Ici (0 : ℝ), ‖F t‖ ^ 2) ≤ E) :
      (∫ t in Ici S, ‖F t‖ ^ 2) ≤ E :=
    (setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun _ ht => hS.trans ht))).trans he
  have hER : 0 ≤ ER := (integral_nonneg (fun _ => sq_nonneg _)).trans (hRE 0)
  have hEH : 0 ≤ EH := (integral_nonneg (fun _ => sq_nonneg _)).trans (hHE 0)
  have hQb (n : ℕ) : ‖Q n‖ ≤ M := le_of_tendsto (hQt n).norm
    ((eventually_ge_atTop T).mono (fun t ht => (hbound n t ht).1))
  have hCm (n : ℕ) : AEStronglyMeasurable (C n) μ :=
    ((hC n).mono hsub).aestronglyMeasurable measurableSet_Ici
  have hweighted {c f : ℝ → C(K, ℝ)} (hc : AEStronglyMeasurable c μ)
      (hb : ∀ t ∈ Ici T, ‖c t‖ ≤ M) (hf : MemLp f 2 μ) :
      Integrable (fun t => c t * f t ^ 2) μ := by
    apply (((memLp_two_iff_integrable_sq_norm hf.1).1 hf).const_mul M).mono' (hc.mul (hf.1.pow 2))
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact (norm_mul_le _ _).trans (mul_le_mul (hb t ht) (hsqnorm _) (norm_nonneg _) hM)
  have hflux (n : ℕ) : Integrable (fun t => C n t * R n t ^ 2) μ :=
    hweighted (hCm n) (fun t ht => (hbound n t ht).1) (hR' n)
  let D := fun n t => C n t * R n t ^ 2 - C 0 t * R 0 t ^ 2 - Q 0 * H n t ^ 2
  have hDi (n : ℕ) : Integrable (D n) μ :=
    ((hflux n).sub (hflux 0)).sub (hweighted aestronglyMeasurable_const (fun _ _ => hQb 0) (hH' n))
  let E := fun n t => R n t - R 0 t - H n t
  let S := fun n t => ‖R n t‖ + ‖R 0 t‖ + ‖H n t‖
  have hEi (n : ℕ) : MemLp (E n) 2 μ := ((hR' n).sub (hR' 0)).sub (hH' n)
  have hSi (n : ℕ) : MemLp (S n) 2 μ := ((hR' n).norm.add (hR' 0).norm).add (hH' n).norm
  have hS0 (n : ℕ) (t : ℝ) : 0 ≤ S n t := add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hCS {ν : Measure ℝ} {f g : ℝ → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
      (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t) :
      (∫ t, f t * g t ∂ν) ≤ Real.sqrt (∫ t, f t ^ 2 ∂ν) * Real.sqrt (∫ t, g t ^ 2 ∂ν) := by
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Eventually.of_forall hf0) (Eventually.of_forall hg0)
      (by simpa only [ENNReal.ofReal_ofNat] using hf) (by simpa only [ENNReal.ofReal_ofNat] using hg)
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using hh
  have hSE (n : ℕ) : (∫ t, S n t ^ 2 ∂μ) ≤ 3 * (2 * ER + EH) := by
    have hrn : Integrable (fun t => ‖R n t‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm (hR' n).1).1 (hR' n)
    have hr0 : Integrable (fun t => ‖R 0 t‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm (hR' 0).1).1 (hR' 0)
    have hhn : Integrable (fun t => ‖H n t‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm (hH' n).1).1 (hH' n)
    have hrr : Integrable (fun t => ‖R n t‖ ^ 2 + ‖R 0 t‖ ^ 2) μ := hrn.add hr0
    have hsum : Integrable (fun t => ‖R n t‖ ^ 2 + ‖R 0 t‖ ^ 2 + ‖H n t‖ ^ 2) μ := hrr.add hhn
    have hh := integral_mono (hSi n).integrable_sq (hsum.const_mul 3) (fun t => by
      dsimp only [S]
      nlinarith only [sq_nonneg (‖R n t‖ - ‖R 0 t‖), sq_nonneg (‖R n t‖ - ‖H n t‖),
        sq_nonneg (‖R 0 t‖ - ‖H n t‖)])
    change (∫ t, S n t ^ 2 ∂μ) ≤ ∫ t, 3 * (‖R n t‖ ^ 2 + ‖R 0 t‖ ^ 2 + ‖H n t‖ ^ 2) ∂μ at hh
    rw [integral_const_mul, integral_add hrr hhn, integral_add hrn hr0] at hh
    linarith only [hh, henergy hT (hRi n) (hRE n), henergy hT (hRi 0) (hRE 0), henergy hT (hHi n) (hHE n)]
  have hElim : Tendsto (fun n => ∫ t, ‖E n t‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) _ herror
    intro n
    exact henergy hT ((memLp_two_iff_integrable_sq_norm (((hR n).sub (hR 0)).sub (hH n)).1).1
      (((hR n).sub (hR 0)).sub (hH n))) le_rfl
  let A := fun n t => M * (‖E n t‖ * S n t)
  let B := fun n t => ‖C n t - C 0 t‖ * ‖R 0 t‖ ^ 2
  let J := fun n t => ‖R 0 t‖ * ‖H n t‖
  let F := fun n t => ‖C n t - Q 0‖ * ‖H n t‖ ^ 2
  have hAi (n : ℕ) : Integrable (A n) μ :=
    (memLp_one_iff_integrable.1 ((hSi n).mul (hEi n).norm)).const_mul M
  have hJi (n : ℕ) : Integrable (J n) μ :=
    memLp_one_iff_integrable.1 ((hH' n).norm.mul (hR' 0).norm)
  have hcoef (n : ℕ) (t : ℝ) (ht : T ≤ t) :
      ‖C n t - C 0 t‖ ≤ 2 * M ∧ ‖C n t - Q 0‖ ≤ 2 * M := by
    constructor
    · exact (norm_sub_le _ _).trans (by linarith only [(hbound n t ht).1, (hbound 0 t ht).1])
    · exact (norm_sub_le _ _).trans (by linarith only [(hbound n t ht).1, hQb 0])
  have hBi (n : ℕ) : Integrable (B n) μ := by
    apply (((hR' 0).norm.integrable_sq).const_mul (2 * M)).mono'
      (((hCm n).sub (hCm 0)).norm.mul ((hR' 0).1.norm.pow 2))
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    change ‖‖C n t - C 0 t‖ * ‖R 0 t‖ ^ 2‖ ≤ 2 * M * ‖R 0 t‖ ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hcoef n t ht).1 (sq_nonneg _)
  have hFi (n : ℕ) : Integrable (F n) μ := by
    apply (((hH' n).norm.integrable_sq).const_mul (2 * M)).mono'
      (((hCm n).sub aestronglyMeasurable_const).norm.mul ((hH' n).1.norm.pow 2))
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    change ‖‖C n t - Q 0‖ * ‖H n t‖ ^ 2‖ ≤ 2 * M * ‖H n t‖ ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hcoef n t ht).2 (sq_nonneg _)
  have hAlim : Tendsto (fun n => ∫ t, A n t ∂μ) atTop (𝓝 0) := by
    have hl : Tendsto (fun n => M * (Real.sqrt (∫ t, ‖E n t‖ ^ 2 ∂μ) * Real.sqrt (3 * (2 * ER + EH))))
        atTop (𝓝 0) := by simpa only [Real.sqrt_zero, zero_mul, mul_zero] using
      (hElim.sqrt.mul_const (Real.sqrt (3 * (2 * ER + EH)))).const_mul M
    apply squeeze_zero (fun n => integral_nonneg (fun t => mul_nonneg hM (mul_nonneg (norm_nonneg _) (hS0 n t)))) _ hl
    intro n
    rw [show (∫ t, A n t ∂μ) = M * ∫ t, ‖E n t‖ * S n t ∂μ from integral_const_mul _ _]
    exact mul_le_mul_of_nonneg_left ((hCS (hEi n).norm (hSi n) (fun _ => norm_nonneg _) (hS0 n)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hSE n)) (Real.sqrt_nonneg _))) hM
  have hBlim : Tendsto (fun n => ∫ t, B n t ∂μ) atTop (𝓝 0) := by
    apply tendsto_order.2
    refine ⟨fun e he => Eventually.of_forall (fun n => he.trans_le (integral_nonneg (fun _ => by positivity))), ?_⟩
    intro e he
    let d := e / (ER + 1)
    have hd : 0 < d := div_pos he (by positivity)
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hCseq d hd] with n hn
    have hh := integral_mono_ae (hBi n) (((hR' 0).norm.integrable_sq).const_mul d) (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have hp := hn t ht
      rw [dist_comm, dist_eq_norm] at hp
      exact mul_le_mul_of_nonneg_right hp.le (sq_nonneg _))
    change (∫ t, B n t ∂μ) ≤ ∫ t, d * ‖R 0 t‖ ^ 2 ∂μ at hh
    rw [integral_const_mul] at hh
    have hb := hh.trans (mul_le_mul_of_nonneg_left (henergy hT (hRi 0) (hRE 0)) hd.le)
    have heq : d * (ER + 1) = e := div_mul_cancel₀ e (by positivity)
    linarith only [hb, heq, hd]
  have hcut {f : ℝ → ℝ} (hf : IntegrableOn f (Ici T)) {s : ℝ} (hs : T ≤ s)
      (hz : ∀ t ∈ Icc T s, f t = 0) : (∫ t in Ici T, f t) = ∫ t in Ici s, f t := by
    have hh := intervalIntegral.integral_Ici_sub_Ici' hf (hf.mono_set (Ici_subset_Ici.2 hs))
    have h0 : (∫ t in T..s, f t) = 0 := by
      calc
        _ = ∫ _t in T..s, (0 : ℝ) := intervalIntegral.integral_congr (by
          intro t ht
          rw [uIcc_of_le hs] at ht
          exact hz t ht)
        _ = _ := by simp
    linarith only [hh, h0]
  have hJlim : Tendsto (fun n => ∫ t, J n t ∂μ) atTop (𝓝 0) := by
    have hl : Tendsto (fun s : ℝ => Real.sqrt (∫ t in Ici s, ‖R 0 t‖ ^ 2) * Real.sqrt EH) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero, zero_mul] using
        ((tendsto_integral_Ici_zero tendsto_id : Tendsto (fun s : ℝ => ∫ t in Ici s, ‖R 0 t‖ ^ 2) atTop (𝓝 0)).sqrt.mul_const (Real.sqrt EH))
    apply tendsto_order.2
    refine ⟨fun e he => Eventually.of_forall (fun n => he.trans_le (integral_nonneg (fun _ => by positivity))), ?_⟩
    intro e he
    obtain ⟨s, hs, hsmall⟩ := ((eventually_ge_atTop T).and (hl.eventually_lt_const he)).exists
    have hs0 := hT.trans hs
    filter_upwards [hvanish s] with n hn
    rw [hcut (hJi n) hs (fun t ht => by simp only [J, hn t ⟨hT.trans ht.1, ht.2⟩, norm_zero, mul_zero])]
    have hr := (hR 0).mono_measure (Measure.restrict_mono (Ici_subset_Ici.2 hs0) le_rfl)
    have hh := (hH n).mono_measure (Measure.restrict_mono (Ici_subset_Ici.2 hs0) le_rfl)
    exact ((hCS hr.norm hh.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (henergy hs0 (hHi n) (hHE n))) (Real.sqrt_nonneg _))).trans_lt hsmall
  have hFlim : Tendsto (fun n => ∫ t, F n t ∂μ) atTop (𝓝 0) := by
    have hdec : Tendsto (fun s : ℝ => L * Real.exp (-η * s)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, id_eq, mul_zero] using
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hη))).const_mul L
    have hq : Tendsto (fun n => ‖Q n - Q 0‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero (f := Q) (b := Q 0)).1 hQseq
    apply tendsto_order.2
    refine ⟨fun e he => Eventually.of_forall (fun n => he.trans_le (integral_nonneg (fun _ => by positivity))), ?_⟩
    intro e he
    let d := e / (2 * (EH + 1))
    have hd : 0 < d := div_pos he (by positivity)
    obtain ⟨s, hs, hsmall⟩ := ((eventually_ge_atTop T).and (hdec.eventually_lt_const hd)).exists
    filter_upwards [hvanish s, hq.eventually_lt_const hd] with n hn hqn
    rw [hcut (hFi n) hs (fun t ht => by simp only [F, hn t ⟨hT.trans ht.1, ht.2⟩, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero])]
    have hhi := (hHi n).mono_set (Ici_subset_Ici.2 (hT.trans hs))
    have hh := integral_mono_ae (IntegrableOn.mono_set (hFi n) (Ici_subset_Ici.2 hs)) (hhi.const_mul (2 * d)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have htT := hs.trans ht
      have hb := (norm_sub_le_norm_sub_add_norm_sub (C n t) (Q n) (Q 0)).trans
        (add_le_add ((hbound n t htT).2.trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left ht (neg_nonpos.2 hη.le))) hL)) hqn.le)
      have hc : ‖C n t - Q 0‖ ≤ 2 * d := by linarith only [hb, hsmall]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg _))
    change (∫ t in Ici s, F n t) ≤ ∫ t in Ici s, (2 * d) * ‖H n t‖ ^ 2 at hh
    rw [integral_const_mul] at hh
    have hb := hh.trans (mul_le_mul_of_nonneg_left (henergy (hT.trans hs) (hHi n) (hHE n)) (by positivity))
    have heq : d * (2 * (EH + 1)) = e := div_mul_cancel₀ e (by positivity)
    linarith only [hb, heq, hd]
  have hpoint (n : ℕ) (t : ℝ) (ht : T ≤ t) : ‖D n t‖ ≤ A n t + B n t + (2 * M) * J n t + F n t := by
    let W := R 0 t + H n t
    have hquad := norm_quadratic_difference_le (ContinuousLinearMap.mul ℝ C(K, ℝ)) (R n t) W
    have hdiff : R n t - W = E n t := by dsimp only [W, E]; abel
    have hsq : ‖R n t ^ 2 - W ^ 2‖ ≤ ‖E n t‖ * S n t := by
      simp only [ContinuousLinearMap.mul_apply', ← pow_two, hdiff] at hquad
      have hnorm : ‖R n t‖ + ‖W‖ ≤ S n t := by
        simpa only [S, add_assoc] using add_le_add (le_refl ‖R n t‖) (norm_add_le (R 0 t) (H n t))
      apply hquad.trans
      have hb := ContinuousLinearMap.opNorm_mul_le ℝ C(K, ℝ)
      have hb1 : ‖ContinuousLinearMap.mul ℝ C(K, ℝ)‖ * ‖E n t‖ ≤ ‖E n t‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg (E n t))
      exact (mul_le_mul_of_nonneg_right hb1 (add_nonneg (norm_nonneg _) (norm_nonneg _))).trans
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg (E n t)))
    have hid : D n t = C n t * (R n t ^ 2 - W ^ 2) + (C n t - C 0 t) * R 0 t ^ 2 +
        (2 : ℝ) • (C n t * (R 0 t * H n t)) + (C n t - Q 0) * H n t ^ 2 := by
      dsimp only [D, W]
      ext u
      simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
        ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul]
      ring
    rw [hid]
    have ha := (norm_mul_le (C n t) (R n t ^ 2 - W ^ 2)).trans
      (mul_le_mul (hbound n t ht).1 hsq (norm_nonneg _) hM)
    have hb := (norm_mul_le (C n t - C 0 t) (R 0 t ^ 2)).trans
      (mul_le_mul_of_nonneg_left (hsqnorm _) (norm_nonneg _))
    have hj : ‖(2 : ℝ) • (C n t * (R 0 t * H n t))‖ ≤ (2 * M) * J n t := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hh : ‖C n t * (R 0 t * H n t)‖ ≤ M * (‖R 0 t‖ * ‖H n t‖) :=
        (norm_mul_le _ _).trans (mul_le_mul (hbound n t ht).1 (norm_mul_le _ _) (norm_nonneg _) hM)
      simpa only [J, mul_assoc] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
    have hf := (norm_mul_le (C n t - Q 0) (H n t ^ 2)).trans
      (mul_le_mul_of_nonneg_left (hsqnorm _) (norm_nonneg _))
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ha hb)) hj)) hf)
  refine ⟨T, hT, Q 0, hQt 0, fun n => ⟨hflux n, hDi n⟩, ?_⟩
  have hlim : Tendsto (fun n => (∫ t, A n t ∂μ) + (∫ t, B n t ∂μ) +
      (2 * M) * (∫ t, J n t ∂μ) + ∫ t, F n t ∂μ) atTop (𝓝 0) := by
    simpa only [zero_add, mul_zero] using ((hAlim.add hBlim).add (hJlim.const_mul (2 * M))).add hFlim
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _ hlim
  intro n
  have hiAB : Integrable (fun t => A n t + B n t) μ := (hAi n).add (hBi n)
  have hiABC : Integrable (fun t => A n t + B n t + (2 * M) * J n t) μ := hiAB.add ((hJi n).const_mul (2 * M))
  have hh := integral_mono_ae (hDi n).norm (hiABC.add (hFi n)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hpoint n t ht)
  change (∫ t, ‖D n t‖ ∂μ) ≤ ∫ t, A n t + B n t + (2 * M) * J n t + F n t ∂μ at hh
  simpa only [integral_add hiABC (hFi n), integral_add hiAB ((hJi n).const_mul (2 * M)),
    integral_add (hAi n) (hBi n), integral_const_mul] using hh

end CauchyHorizon
