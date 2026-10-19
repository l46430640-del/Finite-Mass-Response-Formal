import CauchyHorizon.Analysis.RegularTime
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The exact energy Jacobian on every terminal interval of the regular coordinate. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

theorem IsRegularTimeCoordinate.energy_change {E : Type*} [NormedAddCommGroup E]
    {a χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate a 0 χ) {T : ℝ} (hT : 0 ≤ T)
    (F : ℝ → E) :
    (IntegrableOn (fun w => ‖F w‖ ^ 2) (Ioo (regularTime a T) 0) ↔
      IntegrableOn (fun t => a t * ‖F (regularTime a t)‖ ^ 2) (Ioi T)) ∧
    (∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) =
      ∫ t in Ioi T, a t * ‖F (regularTime a t)‖ ^ 2 := by
  obtain ⟨_hc, hp, _hi, hm, hd, hn, _hl, _himage, _hχc, _hχl, hr, _hleft⟩ := hχ
  have himage : regularTime a '' Ioi T = Ioo (regularTime a T) 0 := by
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨hm ht, hn t⟩
    · intro hw
      obtain ⟨_hpos, he, _hdχ⟩ := hr w ⟨(hm.monotone hT).trans_lt hw.1, hw.2⟩
      refine ⟨χ w, ?_, he⟩
      exact hm.lt_iff_lt.1 (by simpa only [he] using hw.1)
  have hderiv := fun t (_ : t ∈ Ioi T) => (hd t).hasDerivWithinAt (s := Ioi T)
  constructor
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hm.injective.injOn]
    simp only [abs_of_pos (hp _), smul_eq_mul]
  · rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hm.injective.injOn]
    simp only [abs_of_pos (hp _), smul_eq_mul]

theorem IsRegularTimeCoordinate.energy_of_majorant {E : Type*} [NormedAddCommGroup E]
    {a χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate a 0 χ) {T₀ : ℝ} (hT₀ : 0 ≤ T₀)
    {F : ℝ → E} (hF : ContinuousOn F (Ioo (regularTime a 0) 0))
    {G : ℝ → ℝ} (hG : IntegrableOn G (Ici 0))
    (hb : ∀ t, T₀ ≤ t → 0 < t → a t * ‖F (regularTime a t)‖ ^ 2 ≤ G t) :
    (∀ T, T₀ ≤ T → MemLp F 2 (volume.restrict (Ioo (regularTime a T) 0)) ∧
      (∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) ≤ ∫ t in Ioi T, G t) ∧
    Tendsto (fun T => ∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) atTop (𝓝 0) := by
  have hchange (T : ℝ) (hT : 0 ≤ T) := hχ.energy_change hT F
  obtain ⟨hac, hp, _hi, hm, hd, hn, _hl, _himage, _hχc, _hχl, _hright, _hleft⟩ := hχ
  have hVc : Continuous (regularTime a) := continuous_iff_continuousAt.2 (fun t => (hd t).continuousAt)
  have htail (T : ℝ) (hT : T₀ ≤ T) :
      MemLp F 2 (volume.restrict (Ioo (regularTime a T) 0)) ∧
        (∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) ≤ ∫ t in Ioi T, G t := by
    have hT0 := hT₀.trans hT
    have hsub : Ioo (regularTime a T) 0 ⊆ Ioo (regularTime a 0) 0 :=
      fun w hw => ⟨(hm.monotone hT0).trans_lt hw.1, hw.2⟩
    have hc : ContinuousOn (fun t => a t * ‖F (regularTime a t)‖ ^ 2) (Ioi T) :=
      hac.continuousOn.mul ((hF.comp hVc.continuousOn
        (fun t ht => ⟨hm (hT0.trans_lt ht), hn t⟩)).norm.pow 2)
    have hiG := hG.mono_set (show Ioi T ⊆ Ici (0 : ℝ) from fun t ht => hT0.trans ht.le)
    have hiW : IntegrableOn (fun t => a t * ‖F (regularTime a t)‖ ^ 2) (Ioi T) := by
      apply hiG.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp t).le (sq_nonneg _))]
      exact hb t (hT.trans ht.le) (hT0.trans_lt ht)
    obtain ⟨hiff, heq⟩ := hchange T hT0
    refine ⟨(memLp_two_iff_integrable_sq_norm ((hF.mono hsub).aestronglyMeasurable measurableSet_Ioo)).2
      (hiff.2 hiW), ?_⟩
    rw [heq]
    apply integral_mono_ae hiW hiG
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hb t (hT.trans ht.le) (hT0.trans_lt ht)
  refine ⟨htail, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun T => integral_nonneg (fun _ => sq_nonneg _)))
    ((eventually_ge_atTop T₀).mono (fun T hT => (htail T hT).2))
  exact tendsto_integral_Ioi_zero (f := G) (μ := volume) tendsto_id

end CauchyHorizon
