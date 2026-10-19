import CauchyHorizon.Analysis.TerminalIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact logarithmic normalization of the incoming primitive. -/

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace CauchyHorizon

noncomputable def logarithmicIncoming (b ℓ : ℝ) (B : ℝ → ℝ) (u : ℝ) : ℝ :=
  b * u ^ (b - 1) * B (ℓ - Real.log u)

theorem terminalGreen_eq_shifted_integral {b : ℝ} (hb : 0 < b) (B : ℝ →ᵇ ℝ) (t : ℝ) :
    terminalGreen hb B t = ∫ z in Ioi (0 : ℝ), Real.exp (-b * z) * B (t + z) := by
  have himage : (fun z : ℝ => t + z) '' Ioi 0 = Ioi t := by
    ext s
    constructor
    · rintro ⟨z, hz, rfl⟩
      change t < t + z
      exact lt_add_of_pos_right t hz
    · intro hs
      refine ⟨s - t, ?_, by ring⟩
      change t < s at hs
      change 0 < s - t
      exact sub_pos.2 hs
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun z (_hz : z ∈ Ioi (0 : ℝ)) => ((hasDerivAt_id z).const_add t).hasDerivWithinAt)
    (fun _ _ _ _ hh => add_left_cancel hh) (fun s => Real.exp (-b * s) * B s)
  simp only [id_eq] at hi
  rw [himage] at hi
  change Real.exp (b * t) * (∫ s in Ioi t, Real.exp (-b * s) * B s) = _
  rw [hi, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z _
  simp only [abs_one, one_smul]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem logarithmicIncoming_primitive {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u)
    (ℓ : ℝ) (B : ℝ →ᵇ ℝ) :
    IntervalIntegrable (logarithmicIncoming b ℓ B) volume 0 u ∧
      (∫ x in (0 : ℝ)..u, logarithmicIncoming b ℓ B x) =
        b * u ^ b * terminalGreen hb B (ℓ - Real.log u) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [Real.zero_rpow hb.ne']
  let τ := ℓ - Real.log u
  let φ := fun t => Real.exp (ℓ - t)
  have hφd (t : ℝ) (_ht : t ∈ Ioi τ) : HasDerivWithinAt φ (-Real.exp (ℓ - t)) (Ioi τ) t := by
    exact ((((hasDerivAt_id t).const_sub ℓ).exp).congr_deriv (by simp)).hasDerivWithinAt
  have hφi : InjOn φ (Ioi τ) := by
    intro s _ t _ hst
    have hh := Real.exp_injective hst
    linarith only [hh]
  have himage : φ '' Ioi τ = Ioo 0 u := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      change Real.exp (ℓ - t) < u
      rw [← Real.exp_log hu]
      apply Real.exp_lt_exp.2
      change ℓ - Real.log u < t at ht
      linarith only [ht]
    · intro hx
      refine ⟨ℓ - Real.log x, ?_, ?_⟩
      · have hh := Real.log_lt_log hx.1 hx.2
        change ℓ - Real.log u < ℓ - Real.log x
        linarith only [hh]
      · dsimp only [φ]
        rw [sub_sub_cancel, Real.exp_log hx.1]
  have htrans (t : ℝ) : Real.exp (ℓ - t) * logarithmicIncoming b ℓ B (φ t) =
      (b * Real.exp (b * ℓ)) * (Real.exp (-b * t) * B t) := by
    dsimp only [logarithmicIncoming, φ]
    rw [Real.log_exp, sub_sub_cancel, ← Real.exp_mul]
    have he : Real.exp (ℓ - t) * Real.exp ((ℓ - t) * (b - 1)) =
        Real.exp (b * ℓ) * Real.exp (-b * t) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = b * (Real.exp (ℓ - t) * Real.exp ((ℓ - t) * (b - 1))) * B t := by ring
      _ = _ := by rw [he]; ring
  have hfi : IntegrableOn (logarithmicIncoming b ℓ B) (Ioo 0 u) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hφd hφi]
    simpa only [IntegrableOn, abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, htrans] using
      (discounted_integrable hb B τ).const_mul (b * Real.exp (b * ℓ))
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hu.le).2
    ((integrableOn_Ioc_iff_integrableOn_Ioo (by finiteness)).2 hfi), ?_⟩
  rw [intervalIntegral.integral_of_le hu.le, integral_Ioc_eq_integral_Ioo, ← himage,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφd hφi]
  simp_rw [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul, htrans]
  rw [integral_const_mul]
  change (b * Real.exp (b * ℓ)) * (∫ t in Ioi τ, Real.exp (-b * t) * B t) =
    b * u ^ b * (Real.exp (b * τ) * ∫ t in Ioi τ, Real.exp (-b * t) * B t)
  have he : Real.exp (b * ℓ) = u ^ b * Real.exp (b * τ) := by
    rw [Real.rpow_def_of_pos hu, ← Real.exp_add]
    congr 1
    dsimp only [τ]
    ring
  rw [he]
  ring

theorem logarithmicIncoming_outer_source {U δ a b k : ℝ} (hU : 0 ≤ U) (hδ : 0 < δ)
    (hb : 0 < b) (hcrit : k = a * b) (ℓ : ℝ) (B : ℝ →ᵇ ℝ) (v : ℝ) :
    Real.exp (k * v) *
        (∫ u in (0 : ℝ)..min U (δ * Real.exp (-a * v)), |logarithmicIncoming b ℓ B u|) ≤
      δ ^ b * (b * terminalGreen hb |B| (ℓ - Real.log δ + a * v)) := by
  let w := δ * Real.exp (-a * v)
  have hw : 0 < w := mul_pos hδ (Real.exp_pos _)
  have hmin : 0 ≤ min U w := le_min hU hw.le
  have hi := (logarithmicIncoming_primitive hb hw.le ℓ B).1.abs
  have hmono := intervalIntegral.integral_mono_interval le_rfl hmin (min_le_right U w)
    (Filter.Eventually.of_forall (fun u => abs_nonneg (logarithmicIncoming b ℓ B u))) hi
  have hEq : (∫ u in (0 : ℝ)..w, |logarithmicIncoming b ℓ B u|) =
      b * w ^ b * terminalGreen hb |B| (ℓ - Real.log w) := by
    rw [← (logarithmicIncoming_primitive hb hw.le ℓ |B|).2]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hw.le] at hu
    dsimp only [logarithmicIncoming]
    rw [abs_mul, abs_mul, abs_of_pos hb, abs_of_nonneg (Real.rpow_nonneg hu.1 _)]
    rfl
  have hlog : ℓ - Real.log w = ℓ - Real.log δ + a * v := by
    rw [show w = δ * Real.exp (-a * v) from rfl, Real.log_mul hδ.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hweight : Real.exp (k * v) * w ^ b = δ ^ b := by
    dsimp only [w]
    rw [Real.mul_rpow hδ.le (Real.exp_pos _).le, ← Real.exp_mul]
    have he : Real.exp (k * v) * Real.exp (-a * v * b) = 1 := by
      rw [← Real.exp_add, hcrit]
      convert Real.exp_zero using 1
      congr 1
      ring
    calc
      _ = δ ^ b * (Real.exp (k * v) * Real.exp (-a * v * b)) := by ring
      _ = _ := by rw [he, mul_one]
  have hh := mul_le_mul_of_nonneg_left hmono (Real.exp_pos (k * v)).le
  rw [hEq, hlog] at hh
  exact hh.trans_eq (by calc
    _ = (Real.exp (k * v) * w ^ b) * (b * terminalGreen hb |B| (ℓ - Real.log δ + a * v)) := by ring
    _ = _ := by rw [hweight])

theorem logarithmicIncoming_outer_energy {U V δ a b k : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b) (hcrit : k = a * b)
    (ℓ : ℝ) (B : ℝ →ᵇ ℝ) :
    (∫ v in (0 : ℝ)..V, (Real.exp (k * v) *
      (∫ u in (0 : ℝ)..min U (δ * Real.exp (-a * v)), |logarithmicIncoming b ℓ B u|)) ^ 2) ≤
      δ ^ (2 * b) / a * ∫ t in (ℓ - Real.log δ)..(ℓ - Real.log δ + a * V),
        (b * terminalGreen hb |B| t) ^ 2 := by
  let G := fun v => Real.exp (k * v) *
    (∫ u in (0 : ℝ)..min U (δ * Real.exp (-a * v)), |logarithmicIncoming b ℓ B u|)
  let H := fun t => b * terminalGreen hb |B| t
  let τ := ℓ - Real.log δ
  have hi := (logarithmicIncoming_primitive hb hU ℓ B).1.abs
  have hpc : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, |logarithmicIncoming b ℓ B u|) (Icc 0 U) := by
    simpa only [uIcc_of_le hU] using
      intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  let S : ℝ → Icc 0 U := fun v => ⟨min U (δ * Real.exp (-a * v)),
    le_min hU (mul_nonneg hδ.le (Real.exp_pos _).le), min_le_left _ _⟩
  have hGc : Continuous G := by
    have hSc : Continuous S := by fun_prop
    have hp := hpc.domRestrict.comp hSc
    change Continuous (fun v => ∫ u in (0 : ℝ)..min U (δ * Real.exp (-a * v)),
      |logarithmicIncoming b ℓ B u|) at hp
    unfold G
    fun_prop
  have hHc : Continuous H := by unfold H; fun_prop
  have hpw : (δ ^ b) ^ 2 = δ ^ (2 * b) := by
    rw [mul_comm (2 : ℝ) b, Real.rpow_mul hδ.le, Real.rpow_two]
  have hbound (v : ℝ) : G v ^ 2 ≤ δ ^ (2 * b) * H (a * v + τ) ^ 2 := by
    have hG0 : 0 ≤ G v := mul_nonneg (Real.exp_pos _).le
      (intervalIntegral.integral_nonneg (le_min hU (mul_nonneg hδ.le (Real.exp_pos _).le))
        (fun u _ => abs_nonneg _))
    have hh : G v ≤ δ ^ b * H (a * v + τ) := by
      simpa only [G, H, τ, add_comm (a * v)] using
        logarithmicIncoming_outer_source hU hδ hb hcrit ℓ B v
    have hs := (sq_le_sq₀ hG0 (hG0.trans hh)).2 hh
    simpa only [mul_pow, hpw] using hs
  have hright : Continuous (fun v => δ ^ (2 * b) * H (a * v + τ) ^ 2) := by fun_prop
  have hI := intervalIntegral.integral_mono_on (μ := volume) hV ((hGc.pow 2).intervalIntegrable _ _)
    (hright.intervalIntegrable _ _) (fun v _ => hbound v)
  rw [intervalIntegral.integral_const_mul] at hI
  have hchange := intervalIntegral.integral_comp_mul_add (fun t => H t ^ 2) ha.ne' τ
    (a := (0 : ℝ)) (b := V)
  rw [mul_zero, zero_add, smul_eq_mul] at hchange
  rw [hchange, add_comm (a * V) τ] at hI
  exact hI.trans_eq (by dsimp only [H, τ]; ring)

end CauchyHorizon
