import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Ring

/-! The future integral solving y' = c y - f, with its sharp supremum bound. -/

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace CauchyHorizon

noncomputable def futureExtension (f : ℝ → ℝ) (t : ℝ) : ℝ := f (max t 0)

theorem futureExtension_eq {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    futureExtension f t = f t := by simp [futureExtension, max_eq_left ht]

theorem futureExtension_continuous {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) :
    Continuous (futureExtension f) :=
  hf.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 0)

theorem futureExtension_exponential_bound {d C : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hb : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ C * Real.exp (-d * t)) (t : ℝ) :
    ‖futureExtension f t‖ ≤ C * Real.exp (-d * t) := by
  apply (hb (max t 0) (le_max_right t 0)).trans
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
    (mul_le_mul_of_nonpos_left (le_max_left t 0) (neg_nonpos.2 hd.le))) hC

theorem exponentialTail_integrable {d C : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hc : Continuous f) (hb : ∀ t, ‖f t‖ ≤ C * Real.exp (-d * t)) (t : ℝ) :
    IntegrableOn f (Ioi t) :=
  ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hd) t).const_mul C).mono'
    hc.aestronglyMeasurable (ae_of_all _ hb)

theorem exponentialTail_norm_le {d C : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hb : ∀ t, ‖f t‖ ≤ C * Real.exp (-d * t)) (t : ℝ) :
    ‖∫ s in Ioi t, f s‖ ≤ C / d * Real.exp (-d * t) := by
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hd) t).const_mul C) (ae_of_all _ hb)
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hd), neg_div_neg_eq] at h
  convert h using 1
  ring

theorem futureIntegral_hasDerivAt {f : ℝ → ℝ} (hc : Continuous f)
    (hi : ∀ t, IntegrableOn f (Ioi t)) (t : ℝ) :
    HasDerivAt (fun x => ∫ s in Ioi x, f s) (-f t) t := by
  have heq : (fun x => ∫ s in Ioi x, f s) =
      (fun x => (∫ s in Ioi 0, f s) - ∫ s in 0..x, f s) := by
    funext x
    exact eq_sub_of_add_eq' (intervalIntegral.integral_interval_add_Ioi (hi 0) (hi x))
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt).const_sub _

noncomputable def terminalIntegral (c : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (c * t) * ∫ s in Ioi t, Real.exp (-c * s) * f s

theorem discounted_integrable {c : ℝ} (hc : 0 < c) (f : ℝ →ᵇ ℝ) (t : ℝ) :
    IntegrableOn (fun s => Real.exp (-c * s) * f s) (Ioi t) :=
  (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) t).mul_bdd
    f.continuous.aestronglyMeasurable (ae_of_all _ (fun s => f.norm_coe_le_norm s))

theorem terminalIntegral_norm_le {c : ℝ} (hc : 0 < c) (f : ℝ →ᵇ ℝ) (t : ℝ) :
    ‖terminalIntegral c f t‖ ≤ ‖f‖ / c := by
  have hb : ‖∫ s in Ioi t, Real.exp (-c * s) * f s‖ ≤
      (∫ s in Ioi t, Real.exp (-c * s)) * ‖f‖ := by
    rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) t).mul_const ‖f‖)
    apply ae_of_all
    intro s
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm s) (Real.exp_pos _).le
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hc), neg_div_neg_eq] at hb
  have hm : Real.exp (c * t) * Real.exp (-c * t) = 1 := by
    rw [← Real.exp_add]
    rw [show c * t + -c * t = 0 by ring, Real.exp_zero]
  unfold terminalIntegral
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (c * t) * (Real.exp (-c * t) / c * ‖f‖) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = (Real.exp (c * t) * Real.exp (-c * t)) * (‖f‖ / c) := by ring
    _ = _ := by rw [hm, one_mul]

theorem terminalIntegral_hasDerivAt {c : ℝ} (hc : 0 < c) (f : ℝ →ᵇ ℝ) (t : ℝ) :
    HasDerivAt (terminalIntegral c f) (c * terminalIntegral c f t - f t) t := by
  have hcont : Continuous (fun s => Real.exp (-c * s) * f s) := by fun_prop
  have hd := futureIntegral_hasDerivAt hcont (discounted_integrable hc f) t
  have he := (((hasDerivAt_id t).const_mul c).exp).mul hd
  apply he.congr_deriv
  dsimp
  have hm : Real.exp (c * t) * Real.exp (-c * t) = 1 := by
    rw [← Real.exp_add]
    rw [show c * t + -c * t = 0 by ring, Real.exp_zero]
  unfold terminalIntegral
  calc
    _ = c * (Real.exp (c * t) * ∫ s in Ioi t, Real.exp (-c * s) * f s) -
        (Real.exp (c * t) * Real.exp (-c * t)) * f t := by ring
    _ = _ := by rw [hm, one_mul]

noncomputable def terminalGreen {c : ℝ} (hc : 0 < c) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (terminalIntegral c f)
    (continuous_iff_continuousAt.2 (fun t => (terminalIntegral_hasDerivAt hc f t).continuousAt))
    (‖f‖ / c) (terminalIntegral_norm_le hc f)

theorem terminalGreen_norm_le {c : ℝ} (hc : 0 < c) (f : ℝ →ᵇ ℝ) :
    ‖terminalGreen hc f‖ ≤ ‖f‖ / c :=
  (BoundedContinuousFunction.norm_le (div_nonneg (norm_nonneg _) hc.le)).2
    (terminalIntegral_norm_le hc f)

theorem terminalGreen_sub {c : ℝ} (hc : 0 < c) (f g : ℝ →ᵇ ℝ) :
    terminalGreen hc (f - g) = terminalGreen hc f - terminalGreen hc g := by
  ext t
  change Real.exp (c * t) * (∫ s in Ioi t, Real.exp (-c * s) * (f s - g s)) = _
  simp_rw [mul_sub]
  rw [integral_sub (discounted_integrable hc f t) (discounted_integrable hc g t), mul_sub]
  rfl

theorem terminalGreen_lipschitz {c : ℝ} (hc : 0 < c) :
    LipschitzWith ⟨1 / c, one_div_nonneg.2 hc.le⟩ (terminalGreen hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [dist_eq_norm, ← terminalGreen_sub]
  change ‖terminalGreen hc (f - g)‖ ≤ (1 / c) * ‖f - g‖
  convert terminalGreen_norm_le hc (f - g) using 1
  ring

theorem terminalGreen_const {c : ℝ} (hc : 0 < c) (k t : ℝ) :
    terminalGreen hc (BoundedContinuousFunction.const ℝ k) t = k / c := by
  change Real.exp (c * t) * (∫ s in Ioi t, Real.exp (-c * s) * k) = k / c
  rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos hc), neg_div_neg_eq]
  have hm : Real.exp (c * t) * Real.exp (-c * t) = 1 := by
    rw [← Real.exp_add, show c * t + -c * t = 0 by ring, Real.exp_zero]
  calc
    _ = (Real.exp (c * t) * Real.exp (-c * t)) * (k / c) := by ring
    _ = _ := by rw [hm, one_mul]

end CauchyHorizon
