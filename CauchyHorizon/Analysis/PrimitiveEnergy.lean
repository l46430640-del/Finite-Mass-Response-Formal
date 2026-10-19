import CauchyHorizon.Analysis.LogarithmicMatching
import Mathlib.MeasureTheory.Function.L2Space

/-! The physical primitive energy on a fixed incoming interval and its logarithmic limit. -/

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology ENNReal

namespace CauchyHorizon

noncomputable def primitiveEnergy (b : ℝ) (f : ℝ → ℝ) (U : ℝ) : ℝ :=
  ∫ u in Ioc 0 U, (u ^ (-b) * ∫ x in (0 : ℝ)..u, f x) ^ 2 / u

theorem logarithmicIncoming_primitive_energy {b U : ℝ} (hb : 0 < b) (hU : 0 < U)
    (ℓ : ℝ) (B : ℝ →ᵇ ℝ) (hB : Integrable (fun t => B t ^ 2)) :
    IntegrableOn (fun u => (u ^ (-b) * ∫ x in (0 : ℝ)..u,
      logarithmicIncoming b ℓ B x) ^ 2 / u) (Ioc 0 U) ∧
      primitiveEnergy b (logarithmicIncoming b ℓ B) U =
        ∫ t in Ioi (ℓ - Real.log U), (b * terminalGreen hb B t) ^ 2 := by
  let φ := fun t : ℝ => Real.exp (ℓ - t)
  let τ := ℓ - Real.log U
  let F := fun u => (u ^ (-b) * ∫ x in (0 : ℝ)..u, logarithmicIncoming b ℓ B x) ^ 2 / u
  have hprim (u : ℝ) (hu : 0 < u) :
      u ^ (-b) * (∫ x in (0 : ℝ)..u, logarithmicIncoming b ℓ B x) =
        b * terminalGreen hb B (ℓ - Real.log u) := by
    rw [(logarithmicIncoming_primitive hb hu.le ℓ B).2, Real.rpow_neg hu.le]
    field_simp
  have hd (t : ℝ) (_ht : t ∈ Ioi τ) :
      HasDerivWithinAt φ (-Real.exp (ℓ - t)) (Ioi τ) t := by
    exact ((((hasDerivAt_id t).const_sub ℓ).exp).congr_deriv (by simp)).hasDerivWithinAt
  have hinj : InjOn φ (Ioi τ) := by
    intro s _ t _ hst
    have hh := Real.exp_injective hst
    linarith only [hh]
  have himage : φ '' Ioi τ = Ioo 0 U := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      change Real.exp (ℓ - t) < U
      rw [← Real.exp_log hU]
      apply Real.exp_lt_exp.2
      change ℓ - Real.log U < t at ht
      linarith only [ht]
    · intro hu
      refine ⟨ℓ - Real.log u, ?_, ?_⟩
      · have hh := Real.log_lt_log hu.1 hu.2
        change ℓ - Real.log U < ℓ - Real.log u
        linarith only [hh]
      · dsimp only [φ]
        rw [sub_sub_cancel, Real.exp_log hu.1]
  have htrans (t : ℝ) : Real.exp (ℓ - t) * F (φ t) = (b * terminalGreen hb B t) ^ 2 := by
    dsimp only [F, φ]
    rw [hprim _ (Real.exp_pos _), Real.log_exp, sub_sub_cancel]
    field_simp
  have hi := (terminalGreen_l2_contraction hb B hB).1.integrableOn (s := Ioi τ)
  have hFi : IntegrableOn F (Ioo 0 U) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj]
    simpa only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, htrans] using hi
  refine ⟨(integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).2 hFi, ?_⟩
  change (∫ u in Ioc 0 U, F u) = _
  rw [integral_Ioc_eq_integral_Ioo, ← himage,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj]
  simp only [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, htrans, τ]

theorem terminalGreen_restricted_energy {b τ : ℝ} (hb : 0 < b) (B D : ℝ →ᵇ ℝ)
    (hd : ∀ t, HasDerivAt B (D t) t) (hB : Integrable (fun t => B t ^ 2))
    (hD : Integrable (fun t => D t ^ 2)) (hsupp : ∀ t, t ≤ τ → B t = 0) :
    |(∫ t in Ioi τ, (b * terminalGreen hb B t) ^ 2) - ∫ t, B t ^ 2| ≤
      (2 / b) * Real.sqrt (∫ t, B t ^ 2) * Real.sqrt (∫ t, D t ^ 2) := by
  let H := fun t => b * terminalGreen hb B t
  obtain ⟨hHi, hHE⟩ := terminalGreen_l2_contraction hb B hB
  obtain ⟨hEi, hEE⟩ := terminalGreen_approximation_energy hb B D hd hD
  have hHm : Continuous H := by dsimp only [H]; fun_prop
  have hBm : MemLp B 2 volume := (memLp_two_iff_integrable_sq B.continuous.aestronglyMeasurable).2 hB
  have hEm : MemLp (fun t => H t - B t) 2 volume :=
    (memLp_two_iff_integrable_sq (hHm.sub B.continuous).aestronglyMeasurable).2 hEi
  let G := fun t => |B t| * |H t - B t|
  have hGi : Integrable G := hBm.norm.integrable_mul hEm.norm
  have hG0 (t : ℝ) : 0 ≤ G t := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsupport : (∫ t in Ioi τ, B t ^ 2) = ∫ t, B t ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by simp [hsupp t (not_lt.1 ht)])
  have hupper : (∫ t in Ioi τ, H t ^ 2) ≤ ∫ t, B t ^ 2 :=
    (setIntegral_le_integral hHi (Eventually.of_forall fun _ => sq_nonneg _)).trans hHE
  have hdiff : (∫ t, B t ^ 2) - (∫ t in Ioi τ, H t ^ 2) ≤ 2 * ∫ t, G t := by
    have hh := integral_mono (μ := volume.restrict (Ioi τ)) (hB.integrableOn.sub hHi.integrableOn)
      (hGi.integrableOn.const_mul 2) (fun t => show B t ^ 2 - H t ^ 2 ≤ 2 * G t from by
        have hh := neg_le_abs (B t * (H t - B t))
        rw [abs_mul] at hh
        dsimp only [G]
        nlinarith only [hh, sq_nonneg (H t - B t)])
    change (∫ t in Ioi τ, B t ^ 2 - H t ^ 2) ≤ ∫ t in Ioi τ, 2 * G t at hh
    rw [integral_sub hB.integrableOn hHi.integrableOn, hsupport, integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hGi (Eventually.of_forall hG0)) (by norm_num))
  have hCS : (∫ t, G t) ≤ Real.sqrt (∫ t, B t ^ 2) * Real.sqrt (∫ t, (H t - B t) ^ 2) := by
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Eventually.of_forall fun t => norm_nonneg (B t))
      (Eventually.of_forall fun t => norm_nonneg (H t - B t))
      (by simpa only [ENNReal.ofReal_ofNat] using hBm.norm)
      (by simpa only [ENNReal.ofReal_ofNat] using hEm.norm)
    simpa only [G, Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hh
  have hsqrt : Real.sqrt (∫ t, (H t - B t) ^ 2) ≤ (1 / b) * Real.sqrt (∫ t, D t ^ 2) := by
    have hh := Real.sqrt_le_sqrt hEE
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.2 hb)] at hh
  rw [abs_of_nonpos (sub_nonpos.2 hupper), neg_sub]
  exact hdiff.trans ((mul_le_mul_of_nonneg_left
    (hCS.trans (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))) (by norm_num)).trans_eq (by ring))

theorem logarithmicIncoming_primitive_energy_tendsto {b M : ℝ} (hb : 0 < b)
    (P Q : ℕ → ℝ →ᵇ ℝ) (hd : ∀ n t, HasDerivAt (P n) (Q n t) t)
    (hP : ∀ n, Integrable (fun t => P n t ^ 2)) (hM : ∀ n, (∫ t, P n t ^ 2) ≤ M)
    (hQ : ∀ n, Integrable (fun t => Q n t ^ 2))
    (hQlim : Tendsto (fun n => ∫ t, Q n t ^ 2) atTop (𝓝 0))
    (hsupp : ∀ τ : ℝ, ∀ᶠ n in atTop, ∀ t, t ≤ τ → P n t = 0)
    (ℓ : ℝ) {U : ℝ} (hU : 0 < U) :
    (∀ n, 0 ≤ primitiveEnergy b (logarithmicIncoming b ℓ (P n)) U ∧
      primitiveEnergy b (logarithmicIncoming b ℓ (P n)) U ≤ M) ∧
    Tendsto (fun n => primitiveEnergy b (logarithmicIncoming b ℓ (P n)) U - ∫ t, P n t ^ 2)
      atTop (𝓝 0) := by
  have he n := (logarithmicIncoming_primitive_energy hb hU ℓ (P n) (hP n)).2
  refine ⟨fun n => ?_, ?_⟩
  · rw [he]
    exact ⟨integral_nonneg (fun _ => sq_nonneg _),
      ((setIntegral_le_integral (terminalGreen_l2_contraction hb (P n) (hP n)).1
        (Eventually.of_forall fun _ => sq_nonneg _)).trans
        (terminalGreen_l2_contraction hb (P n) (hP n)).2).trans (hM n)⟩
  · have hlim : Tendsto (fun n => (2 / b) * Real.sqrt M * Real.sqrt (∫ t, Q n t ^ 2))
        atTop (𝓝 0) := by simpa using hQlim.sqrt.const_mul ((2 / b) * Real.sqrt M)
    apply squeeze_zero_norm' ?_ hlim
    filter_upwards [hsupp (ℓ - Real.log U)] with n hn
    rw [Real.norm_eq_abs, he]
    exact (terminalGreen_restricted_energy hb (P n) (Q n) (hd n) (hP n) (hQ n) hn).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hM n))
        (by positivity)) (Real.sqrt_nonneg _))

end CauchyHorizon
