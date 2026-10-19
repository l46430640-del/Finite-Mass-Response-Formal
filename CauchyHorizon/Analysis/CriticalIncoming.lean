import CauchyHorizon.Analysis.LogarithmicProfile
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! The critical logarithmic substitution cancels the incoming power with its Jacobian. -/

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ENNReal Topology

namespace CauchyHorizon

theorem logarithmicIncoming_critical_moment {b q : ℝ} (hb : 0 ≤ b)
    (hcrit : (b - 1) * q = -1) (ℓ : ℝ) (P : ℝ → ℝ)
    (hP : Integrable (fun t => |P t| ^ q)) :
    IntegrableOn (fun u => |logarithmicIncoming b ℓ P u| ^ q) (Ioi 0) ∧
      (∫ u in Ioi (0 : ℝ), |logarithmicIncoming b ℓ P u| ^ q) =
        b ^ q * ∫ t, |P t| ^ q := by
  let φ := fun t : ℝ => Real.exp (ℓ - t)
  have hd (t : ℝ) (_ht : t ∈ (univ : Set ℝ)) :
      HasDerivWithinAt φ (-Real.exp (ℓ - t)) univ t := by
    exact ((((hasDerivAt_id t).const_sub ℓ).exp).congr_deriv (by simp)).hasDerivWithinAt
  have hi : InjOn φ univ := by
    intro s _ t _ hst
    have hh := Real.exp_injective hst
    linarith only [hh]
  have himage : φ '' univ = Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨t, _, rfl⟩
      exact Real.exp_pos _
    · intro hu
      refine ⟨ℓ - Real.log u, mem_univ _, ?_⟩
      dsimp only [φ]
      rw [sub_sub_cancel, Real.exp_log hu]
  have htrans (t : ℝ) : Real.exp (ℓ - t) * |logarithmicIncoming b ℓ P (φ t)| ^ q =
      b ^ q * |P t| ^ q := by
    dsimp only [logarithmicIncoming, φ]
    rw [Real.log_exp, sub_sub_cancel, abs_mul, abs_mul, abs_of_nonneg hb,
      abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _),
      Real.mul_rpow (mul_nonneg hb (Real.rpow_nonneg (Real.exp_pos _).le _)) (abs_nonneg _),
      Real.mul_rpow hb (Real.rpow_nonneg (Real.exp_pos _).le _),
      ← Real.rpow_mul (Real.exp_pos _).le, hcrit, Real.rpow_neg_one]
    calc
      _ = (Real.exp (ℓ - t) * (Real.exp (ℓ - t))⁻¹) * (b ^ q * |P t| ^ q) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul]
  constructor
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hi]
    simpa only [IntegrableOn, Measure.restrict_univ, abs_neg,
      abs_of_pos (Real.exp_pos _), smul_eq_mul, htrans] using hP.const_mul (b ^ q)
  · rw [← himage, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hi]
    simp_rw [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, htrans]
    rw [integral_const_mul, Measure.restrict_univ]

theorem logarithmicIncoming_critical_lp {p : ℝ≥0∞} (hp : p ≠ 0) (hpfin : p ≠ ∞)
    {b : ℝ} (hb : 0 ≤ b) (hcrit : (b - 1) * p.toReal = -1)
    (ℓ : ℝ) (P : ℝ →ᵇ ℝ) (hP : Integrable (fun t => |P t| ^ p.toReal)) :
    MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Ici 0)) ∧
      (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Ici 0))).toReal =
        (b ^ p.toReal * ∫ t, |P t| ^ p.toReal) ^ p.toReal⁻¹ ∧
      ∀ δ : ℝ, MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 δ)) ∧
        (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Icc 0 δ))).toReal ≤
          (b ^ p.toReal * ∫ t, |P t| ^ p.toReal) ^ p.toReal⁻¹ := by
  have hm : Measurable (logarithmicIncoming b ℓ P) := by
    unfold logarithmicIncoming
    fun_prop
  obtain ⟨hi, he⟩ := logarithmicIncoming_critical_moment hb hcrit ℓ P hP
  have hmem : MemLp (logarithmicIncoming b ℓ P) p (volume.restrict (Ici 0)) := by
    rw [← restrict_Ioi_eq_restrict_Ici]
    apply (integrable_norm_rpow_iff hm.aestronglyMeasurable hp hpfin).1
    simpa only [IntegrableOn, Real.norm_eq_abs] using hi
  have hnorm : (eLpNorm (logarithmicIncoming b ℓ P) p (volume.restrict (Ici 0))).toReal =
      (b ^ p.toReal * ∫ t, |P t| ^ p.toReal) ^ p.toReal⁻¹ := by
    rw [toReal_eLpNorm hmem.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal hp hpfin hmem.aestronglyMeasurable]
    simp_rw [Real.norm_eq_abs]
    rw [← restrict_Ioi_eq_restrict_Ici, he]
  refine ⟨hmem, hnorm, ?_⟩
  intro δ
  have hsub : volume.restrict (Icc 0 δ) ≤ volume.restrict (Ici (0 : ℝ)) :=
    Measure.restrict_mono (fun _ hu => hu.1) le_rfl
  refine ⟨hmem.mono_measure hsub, ?_⟩
  rw [← hnorm]
  exact ENNReal.toReal_mono hmem.eLpNorm_ne_top (eLpNorm_mono_measure _ hsub)

theorem logarithmicIncoming_critical_tendsto {p : ℝ≥0∞} (hp : p ≠ 0) (hpfin : p ≠ ∞)
    {b : ℝ} (hb : 0 ≤ b) (hcrit : (b - 1) * p.toReal = -1)
    (ℓ : ℕ → ℝ) (P : ℕ → ℝ →ᵇ ℝ)
    (hP : ∀ n, Integrable (fun t => |P n t| ^ p.toReal))
    (hlim : Tendsto (fun n => ∫ t, |P n t| ^ p.toReal) atTop (𝓝 0)) (δ : ℝ) :
    (∀ n, MemLp (logarithmicIncoming b (ℓ n) (P n)) p (volume.restrict (Icc 0 δ))) ∧
      Tendsto (fun n => (eLpNorm (logarithmicIncoming b (ℓ n) (P n)) p
        (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) := by
  have hdata n := (logarithmicIncoming_critical_lp hp hpfin hb hcrit (ℓ n) (P n) (hP n)).2.2 δ
  refine ⟨fun n => (hdata n).1, ?_⟩
  have hbase : Tendsto (fun n => b ^ p.toReal * ∫ t, |P n t| ^ p.toReal) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (b ^ p.toReal)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => (hdata n).2)
    (hbase.rpow_const_nhds_zero (inv_pos.2 (ENNReal.toReal_pos hp hpfin)))

end CauchyHorizon
