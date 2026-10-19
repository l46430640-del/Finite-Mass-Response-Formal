import CauchyHorizon.Algebra
import CauchyHorizon.Analysis.TerminalIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Horizon mass and compatible outgoing constraints. Radius existence is a separate obligation. -/

open MeasureTheory Set
open scoped Topology

namespace CauchyHorizon

noncomputable def horizonMass (M : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  M - (∫ s in Ioi t, h s ^ 2) / 2

noncomputable def horizonK (r m e Λ : ℝ) : ℝ := m / r ^ 2 - e ^ 2 / r ^ 3 - Λ * r / 3

noncomputable def horizonLogOmega (K : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log 4 + ∫ s in 0..t, 2 * K s

noncomputable def horizonNu (K : ℝ → ℝ) (t : ℝ) : ℝ :=
  -Real.exp (∫ s in 0..t, 2 * K s)

noncomputable def horizonPhi (h r : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(∫ s in Ioi t, h s / r s)

theorem horizonMass_congr_future {h g : ℝ → ℝ} (he : EqOn h g (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) (M : ℝ) : horizonMass M h t = horizonMass M g t := by
  unfold horizonMass
  congr 2
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w hw
  dsimp only
  rw [he (le_of_lt (lt_of_le_of_lt ht hw))]

theorem horizonPhi_congr_future {h g : ℝ → ℝ} (he : EqOn h g (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ → ℝ) : horizonPhi h r t = horizonPhi g r t := by
  unfold horizonPhi
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w hw
  dsimp only
  rw [he (le_of_lt (lt_of_le_of_lt ht hw))]

theorem horizon_square_bound {s H : ℝ} (hH : 0 ≤ H) {h : ℝ → ℝ}
    (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t)) (t : ℝ) :
    ‖h t ^ 2‖ ≤ H ^ 2 * Real.exp (-(2 * s) * t) := by
  rw [norm_pow]
  calc
    _ ≤ (H * Real.exp (-s * t)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hH (Real.exp_pos _).le)).2 (hb t)
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

theorem horizon_mass_integrable {s H : ℝ} (hs : 0 < s) (hH : 0 ≤ H) {h : ℝ → ℝ}
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t)) (t : ℝ) :
    IntegrableOn (fun w => h w ^ 2) (Ioi t) :=
  exponentialTail_integrable (by positivity : 0 < 2 * s) (hc.pow 2)
    (horizon_square_bound hH hb) t

theorem horizonMass_bounds {s H : ℝ} (hs : 0 < s) (hH : 0 ≤ H) {h : ℝ → ℝ}
    (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t)) (M t : ℝ) :
    0 ≤ M - horizonMass M h t ∧
      M - horizonMass M h t ≤ H ^ 2 / (4 * s) * Real.exp (-(2 * s) * t) := by
  have hi : 0 ≤ ∫ w in Ioi t, h w ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have he := exponentialTail_norm_le (by positivity : 0 < 2 * s) (horizon_square_bound hH hb) t
  rw [Real.norm_of_nonneg hi] at he
  unfold horizonMass
  constructor
  · linarith
  · calc
      _ = (∫ w in Ioi t, h w ^ 2) / 2 := by ring
      _ ≤ (H ^ 2 / (2 * s) * Real.exp (-(2 * s) * t)) / 2 := div_le_div_of_nonneg_right he (by norm_num)
      _ = _ := by ring

theorem horizonMass_hasDerivAt {h : ℝ → ℝ} (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t)) (M t : ℝ) :
    HasDerivAt (horizonMass M h) (h t ^ 2 / 2) t := by
  have hd := ((futureIntegral_hasDerivAt (hc.pow 2) hi t).div_const 2).const_sub M
  simpa only [horizonMass, neg_div, neg_neg] using! hd

theorem horizonFunction_hasDerivWithinAt {r m : ℝ → ℝ} {r' m' t : ℝ} {s : Set ℝ}
    (hr : HasDerivWithinAt r r' s t) (hm : HasDerivWithinAt m m' s t) (hr0 : r t ≠ 0) (e Λ : ℝ) :
    HasDerivWithinAt (fun w => horizonFunction (r w) (m w) e Λ)
      (2 * horizonK (r t) (m t) e Λ * r' - 2 * m' / r t) s t := by
  have hd := (((hasDerivWithinAt_const t s 1).sub ((hm.const_mul 2).div hr hr0)).add
    ((hasDerivWithinAt_const t s (e ^ 2)).div (hr.pow 2) (pow_ne_zero 2 hr0))).sub
      (((hr.pow 2).const_mul Λ).div_const 3)
  apply hd.congr_deriv
  unfold horizonK
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem horizonFunction_hasDerivAt {r m : ℝ → ℝ} {r' m' t : ℝ}
    (hr : HasDerivAt r r' t) (hm : HasDerivAt m m' t) (hr0 : r t ≠ 0) (e Λ : ℝ) :
    HasDerivAt (fun w => horizonFunction (r w) (m w) e Λ)
      (2 * horizonK (r t) (m t) e Λ * r' - 2 * m' / r t) t :=
  hasDerivWithinAt_univ.mp (horizonFunction_hasDerivWithinAt hr.hasDerivWithinAt hm.hasDerivWithinAt hr0 e Λ)

theorem horizon_normalization (K : ℝ → ℝ) (t : ℝ) :
    horizonNu K t < 0 ∧
      Real.exp (horizonLogOmega K t) = -4 * horizonNu K t ∧
      -Real.exp (horizonLogOmega K t) / (4 * horizonNu K t) = 1 := by
  have he : Real.exp (horizonLogOmega K t) = -4 * horizonNu K t := by
    simp [horizonLogOmega, horizonNu, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  refine ⟨neg_neg_of_pos (Real.exp_pos _), he, ?_⟩
  rw [he, neg_mul, neg_neg]
  exact div_self (mul_ne_zero (by norm_num) (neg_ne_zero.2 (Real.exp_ne_zero _)))

theorem horizon_corner (K : ℝ → ℝ) :
    horizonNu K 0 = -1 ∧ Real.exp (horizonLogOmega K 0) = 4 := by
  simp [horizonNu, horizonLogOmega, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

theorem horizonLogOmega_hasDerivAt {K : ℝ → ℝ} (hK : Continuous K) (t : ℝ) :
    HasDerivAt (horizonLogOmega K) (2 * K t) t := by
  have hc : Continuous (fun w => 2 * K w) := continuous_const.mul hK
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt).const_add (Real.log 4)

theorem horizonNu_hasDerivAt {K : ℝ → ℝ} (hK : Continuous K) (t : ℝ) :
    HasDerivAt (horizonNu K) (2 * K t * horizonNu K t) t := by
  have hc : Continuous (fun w => 2 * K w) := continuous_const.mul hK
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt).exp.neg
  apply hd.congr_deriv
  unfold horizonNu
  ring

theorem horizonPhi_integrable {s H R : ℝ} (hs : 0 < s) (hH : 0 ≤ H) (hR : 0 < R)
    {h r : ℝ → ℝ} (hc : Continuous h) (hr : Continuous r)
    (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t)) (hrb : ∀ t, R ≤ r t) (t : ℝ) :
    IntegrableOn (fun w => h w / r w) (Ioi t) := by
  apply exponentialTail_integrable (C := H / R) hs
    (hc.div hr (fun w => (hR.trans_le (hrb w)).ne')) _ t
  intro w
  change ‖h w / r w‖ ≤ H / R * Real.exp (-s * w)
  rw [norm_div, Real.norm_of_nonneg (hR.le.trans (hrb w))]
  calc
    _ ≤ (H * Real.exp (-s * w)) / r w :=
      div_le_div_of_nonneg_right (hb w) (hR.le.trans (hrb w))
    _ ≤ (H * Real.exp (-s * w)) / R :=
      div_le_div_of_nonneg_left (mul_nonneg hH (Real.exp_pos _).le) hR (hrb w)
    _ = (H / R) * Real.exp (-s * w) := by ring

theorem horizonPhi_hasDerivAt {h r : ℝ → ℝ} (hc : Continuous h) (hr : Continuous r)
    (hr0 : ∀ t, r t ≠ 0) (hi : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t)) (t : ℝ) :
    HasDerivAt (horizonPhi h r) (h t / r t) t := by
  simpa only [horizonPhi, neg_neg] using! (futureIntegral_hasDerivAt (hc.div hr hr0) hi t).neg

theorem outgoing_constraint {M e Λ : ℝ} {h r : ℝ → ℝ} (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r)
    (hr : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt r (horizonFunction (r t) (horizonMass M h t) e Λ) t)
    (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t)) {t : ℝ} (ht : 0 < t) :
    deriv (deriv r) t -
      deriv (horizonLogOmega (fun w => horizonK (r w) (horizonMass M h w) e Λ)) t * deriv r t =
        -r t * (deriv (horizonPhi h r) t) ^ 2 := by
  have hr' : deriv r =ᶠ[nhds t] fun w => horizonFunction (r w) (horizonMass M h w) e Λ := by
    filter_upwards [Ioi_mem_nhds ht] with w hw using (hr w hw).deriv
  have hm : Continuous (horizonMass M h) :=
    continuous_iff_continuousAt.2 (fun w => (horizonMass_hasDerivAt hc hi M w).continuousAt)
  have hK : Continuous (fun w => horizonK (r w) (horizonMass M h w) e Λ) :=
    ((hm.div (hrc.pow 2) (fun w => pow_ne_zero 2 (hr0 w))).sub
      (continuous_const.div (hrc.pow 3) (fun w => pow_ne_zero 3 (hr0 w)))).sub
      ((continuous_const.mul hrc).div_const 3)
  have hd := horizonFunction_hasDerivAt (hr t ht) (horizonMass_hasDerivAt hc hi M t) (hr0 t) e Λ
  rw [hr'.deriv_eq, (hr t ht).deriv, hd.deriv, (horizonLogOmega_hasDerivAt hK t).deriv,
    (horizonPhi_hasDerivAt hc hrc hr0 hφ t).deriv]
  field_simp
  ring

end CauchyHorizon
