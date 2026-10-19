import CauchyHorizon.Characteristic.IncomingWave
import CauchyHorizon.Analysis.Quadratic

/-! The actual incoming velocity is a continuous quadratic map from scalar L4 to vector L2. -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CauchyHorizon

local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

local instance : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [show (4 : ℝ≥0∞) = (↑(4 : ℝ≥0)) by norm_cast,
    ← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_add, ← ENNReal.coe_inv_two]
  norm_num⟩

variable {U : ℝ}

noncomputable def l4Product (μ : Measure ℝ) : Lp ℝ 4 μ →L[ℝ] Lp ℝ 4 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ 4 4 2

theorem l4Product_norm_le (μ : Measure ℝ) : ‖l4Product μ‖ ≤ 1 :=
  (ContinuousLinearMap.norm_holderL_le _).trans (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

theorem l4Product_ae {μ : Measure ℝ} (f g : Lp ℝ 4 μ) :
    l4Product μ f g =ᵐ[μ] fun t => f t * g t :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) f g

noncomputable def waveCoordinateLp (i : Fin 3) (μ : Measure ℝ) : Lp ℝ 2 μ →L[ℝ] Lp WaveVector 2 μ :=
  (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) i).compLpL 2 μ

theorem waveCoordinateLp_norm_le (i : Fin 3) (μ : Measure ℝ) (f : Lp ℝ 2 μ) :
    ‖waveCoordinateLp i μ f‖ ≤ ‖f‖ := by
  have h := (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) i).norm_compLp_le f
  have hs := ContinuousLinearMap.norm_single_le_one (𝕜 := ℝ) (E := fun _ : Fin 3 => ℝ) i
  exact h.trans (by simpa using mul_le_mul_of_nonneg_right hs (norm_nonneg f))

noncomputable def incomingWeight (hU : 0 ≤ U) (R : ℝ) : Lp ℝ ∞ (volume.restrict (Icc 0 U)) :=
  intervalToLp hU ∞ ⟨fun t => -(R - (t : ℝ)), by fun_prop⟩

theorem incomingWeight_norm_le (hU : 0 ≤ U) {R : ℝ} (hUR : U < R) : ‖incomingWeight hU R‖ ≤ R := by
  have hR : 0 ≤ R := hU.trans hUR.le
  refine (intervalToLinf_norm_le hU _).trans ?_
  apply (ContinuousMap.norm_le _ hR).2
  intro t
  change ‖-(R - (t : ℝ))‖ ≤ R
  rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by linarith [t.property.2])]
  linarith [t.property.1]

noncomputable def incomingMultiplier (hU : 0 ≤ U) (R : ℝ) :
    Lp ℝ 2 (volume.restrict (Icc 0 U)) →L[ℝ] Lp ℝ 2 (volume.restrict (Icc 0 U)) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (volume.restrict (Icc 0 U)) ∞ 2 2 (incomingWeight hU R)

theorem incomingMultiplier_norm_le (hU : 0 ≤ U) {R : ℝ} (hUR : U < R)
    (f : Lp ℝ 2 (volume.restrict (Icc 0 U))) : ‖incomingMultiplier hU R f‖ ≤ R * ‖f‖ := by
  have h := (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le (r := 2) (incomingWeight hU R) f
  change ‖incomingMultiplier hU R f‖ ≤ _ at h
  refine h.trans ?_
  have hmul := mul_le_mul (ContinuousLinearMap.opNorm_mul_le ℝ ℝ) (incomingWeight_norm_le hU hUR)
    (norm_nonneg (incomingWeight hU R)) zero_le_one
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hmul (norm_nonneg f)

noncomputable def incomingL4Map (hU : 0 ≤ U) (R : ℝ)
    (f : Lp ℝ 4 (volume.restrict (Icc 0 U))) : Lp WaveVector 2 (volume.restrict (Icc 0 U)) :=
  intervalToLp hU 2 (ContinuousMap.const _ ![-1, 0, 0]) +
    waveCoordinateLp 1 _ (l4Product _ f (intervalToLp hU 4 (ContinuousMap.const _ 1))) +
    waveCoordinateLp 2 _ (incomingMultiplier hU R (l4Product _ f f))

theorem incomingL4Map_ae (hU : 0 ≤ U) (R : ℝ) (f : Lp ℝ 4 (volume.restrict (Icc 0 U))) :
    incomingL4Map hU R f =ᵐ[volume.restrict (Icc 0 U)] incomingVelocity R f := by
  let μ := volume.restrict (Icc 0 U)
  let b := intervalToLp hU 2 (ContinuousMap.const _ (![-1, 0, 0] : WaveVector))
  let c := intervalToLp hU 4 (ContinuousMap.const _ (1 : ℝ))
  let l := waveCoordinateLp 1 μ (l4Product μ f c)
  let q := waveCoordinateLp 2 μ (incomingMultiplier hU R (l4Product μ f f))
  have hl := (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) 1).coeFn_compLpL (l4Product μ f c)
  have hq := (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) 2).coeFn_compLpL (incomingMultiplier hU R (l4Product μ f f))
  filter_upwards [Lp.coeFn_add (b + l) q, Lp.coeFn_add b l,
    intervalToLp_ae hU 2 (ContinuousMap.const _ (![-1, 0, 0] : WaveVector)),
    intervalToLp_ae hU 4 (ContinuousMap.const _ (1 : ℝ)), hl, hq,
    l4Product_ae f c, l4Product_ae f f,
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (incomingWeight hU R) (l4Product μ f f),
    intervalToLp_ae hU ∞ (⟨fun t => -(R - (t : ℝ)), by fun_prop⟩ : C(Icc 0 U, ℝ)),
    ae_restrict_mem measurableSet_Icc] with t ha hb hb0 hc hl hq hlf hff hw hwt ht
  change incomingL4Map hU R f t = (b + l) t + q t at ha
  change (b + l) t = b t + l t at hb
  change b t = ![-1, 0, 0] at hb0
  change c t = 1 at hc
  change l t = Pi.single 1 (l4Product μ f c t) at hl
  change q t = Pi.single 2 (incomingMultiplier hU R (l4Product μ f f) t) at hq
  change incomingMultiplier hU R (l4Product μ f f) t = incomingWeight hU R t * l4Product μ f f t at hw
  change incomingWeight hU R t = -(R - (projIcc 0 U hU t : ℝ)) at hwt
  rw [projIcc_of_mem hU ht] at hwt
  change l4Product μ f c t = f t * c t at hlf
  change l4Product μ f f t = f t * f t at hff
  rw [ha, hb, hb0, hl, hq, hw, hwt, hlf, hff, hc]
  ext i
  fin_cases i <;> simp [incomingVelocity, Matrix.vecHead, Matrix.vecTail, pow_two]

theorem incomingL4Map_eq_velocity {R : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    incomingL4Map hU R ((hf.mono_exponent hp).toLp f) = incomingWaveVelocity hUR hp hf := by
  apply Lp.ext
  filter_upwards [incomingL4Map_ae hU R ((hf.mono_exponent hp).toLp f),
    (hf.mono_exponent hp).coeFn_toLp, incomingWaveVelocity_ae hUR hp hf] with t hm hf hv
  rw [hm, hv]
  simp only [incomingVelocity, hf]

theorem intervalOneL4_norm_le (hU : 0 ≤ U) (hU1 : U ≤ 1) :
    ‖intervalToLp hU 4 (ContinuousMap.const _ (1 : ℝ))‖ ≤ 1 := by
  have hc : ‖(ContinuousMap.const (Icc 0 U) (1 : ℝ))‖ ≤ 1 :=
    (ContinuousMap.norm_le _ zero_le_one).2 (fun _ => by norm_num)
  have h := intervalToLp_norm_le hU 4 (ContinuousMap.const _ (1 : ℝ))
  simp only [sub_zero, ENNReal.toReal_ofNat] at h
  exact h.trans (by simpa using mul_le_mul (Real.rpow_le_one hU hU1 (by positivity)) hc (norm_nonneg _) zero_le_one)

theorem incomingL4Map_difference (hU : 0 ≤ U) (hU1 : U ≤ 1) {R : ℝ} (hUR : U < R)
    (f g : Lp ℝ 4 (volume.restrict (Icc 0 U))) :
    ‖incomingL4Map hU R f - incomingL4Map hU R g‖ ≤
      (1 + R * (‖f‖ + ‖g‖)) * ‖f - g‖ := by
  let μ := volume.restrict (Icc 0 U)
  let c := intervalToLp hU 4 (ContinuousMap.const _ (1 : ℝ))
  have hlin : ‖l4Product μ (f - g) c‖ ≤ ‖f - g‖ := by
    refine ((l4Product μ).le_opNorm₂ _ _).trans ?_
    have hc := intervalOneL4_norm_le hU hU1
    calc
      _ ≤ 1 * ‖f - g‖ * 1 := mul_le_mul (mul_le_mul_of_nonneg_right (l4Product_norm_le μ) (norm_nonneg _)) hc
        (norm_nonneg c) (by positivity)
      _ = _ := by ring
  have hquad : ‖l4Product μ f f - l4Product μ g g‖ ≤ ‖f - g‖ * (‖f‖ + ‖g‖) := by
    refine (norm_quadratic_difference_le (l4Product μ) f g).trans ?_
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (l4Product_norm_le μ) (norm_nonneg _)) (add_nonneg (norm_nonneg f) (norm_nonneg g))
  have he : incomingL4Map hU R f - incomingL4Map hU R g =
      waveCoordinateLp 1 μ (l4Product μ (f - g) c) +
        waveCoordinateLp 2 μ (incomingMultiplier hU R (l4Product μ f f - l4Product μ g g)) := by
    simp only [incomingL4Map, map_sub, sub_apply]
    abel
  rw [he]
  refine (norm_add_le _ _).trans ?_
  have hq := (waveCoordinateLp_norm_le 2 μ _).trans ((incomingMultiplier_norm_le hU hUR _).trans
    (mul_le_mul_of_nonneg_left hquad (hU.trans hUR.le)))
  calc
    _ ≤ ‖f - g‖ + R * (‖f - g‖ * (‖f‖ + ‖g‖)) := add_le_add ((waveCoordinateLp_norm_le 1 μ _).trans hlin) hq
    _ = _ := by ring

theorem incomingL4Map_zero_norm_le (hU : 0 ≤ U) : ‖incomingL4Map hU 0 0‖ ≤ Real.sqrt U := by
  simp only [incomingL4Map, map_zero, zero_apply, add_zero]
  have h := intervalToL2_norm_le hU (ContinuousMap.const _ (![-1, 0, 0] : WaveVector))
  rw [sub_zero] at h
  refine h.trans ?_
  have hc : ‖(ContinuousMap.const (Icc 0 U) (![-1, 0, 0] : WaveVector))‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).2
    intro t
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    fin_cases i <;> norm_num
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg U)

theorem incomingL4Map_norm_le (hU : 0 ≤ U) (hU1 : U ≤ 1) {R : ℝ} (hUR : U < R)
    (f : Lp ℝ 4 (volume.restrict (Icc 0 U))) :
    ‖incomingL4Map hU R f‖ ≤ 1 + ‖f‖ + R * ‖f‖ ^ 2 := by
  have hd := incomingL4Map_difference hU hU1 hUR f 0
  have hz : incomingL4Map hU R 0 = incomingL4Map hU 0 0 := by simp [incomingL4Map]
  have hn := norm_le_insert (incomingL4Map hU R 0) (incomingL4Map hU R f)
  rw [norm_sub_rev] at hn
  simp only [sub_zero, norm_zero, add_zero] at hd
  have hzero := (incomingL4Map_zero_norm_le hU).trans (Real.sqrt_le_one.2 hU1)
  rw [hz] at hn hd
  nlinarith

theorem incomingL4Map_continuous (hU : 0 ≤ U) (R : ℝ) : Continuous (incomingL4Map hU R) := by
  unfold incomingL4Map
  fun_prop

theorem incomingL4_norm_le_lp (hU1 : U ≤ 1) {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    ‖(hf.mono_exponent hp).toLp f‖ ≤ (eLpNorm f p (volume.restrict (Icc 0 U))).toReal := by
  have hμ : (volume.restrict (Icc 0 U)) univ ≤ 1 := by
    simpa only [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_le_one] using hU1
  have hexp : 0 ≤ 1 / (4 : ℝ≥0∞).toReal - 1 / p.toReal := by
    by_cases ht : p = ∞
    · simp [ht]
    · have hp' : (4 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono ht hp
      simpa using sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hp')
  have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable
  have hle : eLpNorm f 4 (volume.restrict (Icc 0 U)) ≤ eLpNorm f p (volume.restrict (Icc 0 U)) := by
    refine he.trans ?_
    simpa using mul_le_mul_of_nonneg_left (ENNReal.rpow_le_one hμ hexp)
      (zero_le : 0 ≤ eLpNorm f p (volume.restrict (Icc 0 U)))
  rw [Lp.norm_toLp]
  exact ENNReal.toReal_mono hf.2.ne hle

theorem incoming_integral_abs_le_lp_power (hU : 0 ≤ U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    (∫ t in (0 : ℝ)..U, |f t|) ≤
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal * U ^ (1 - 1 / p.toReal) := by
  have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    by_cases ht : p = ∞
    · simp [ht]
    · have hp' : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono ht hp
      simpa using sub_nonneg.mpr (one_div_le_one_div_of_le zero_lt_one hp')
  have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable
  have heq : (∫ t in (0 : ℝ)..U, |f t|) = (eLpNorm f 1 (volume.restrict (Icc 0 U))).toReal := by
    rw [intervalIntegral.integral_of_le hU, ← integral_Icc_eq_integral_Ioc]
    simp only [← Real.norm_eq_abs, integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm]
  rw [heq]
  have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.2.ne
    (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top _ _))) he
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hU, ENNReal.toReal_one, div_one] using hb

theorem incoming_integral_abs_le_lp (hU : 0 ≤ U) (hU1 : U ≤ 1) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    (∫ t in (0 : ℝ)..U, |f t|) ≤ (eLpNorm f p (volume.restrict (Icc 0 U))).toReal := by
  have hexp : 0 ≤ 1 - 1 / p.toReal := by
    by_cases ht : p = ∞
    · simp [ht]
    · have hp' : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono ht hp
      simpa using sub_nonneg.2 (one_div_le_one_div_of_le zero_lt_one hp')
  exact (incoming_integral_abs_le_lp_power hU hp hf).trans
    (mul_le_of_le_one_right ENNReal.toReal_nonneg (Real.rpow_le_one hU hU1 hexp))

theorem incoming_integral_sq_le_lp_power {p : ℝ≥0∞} (hp : 2 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U))) (u : Icc 0 U) :
    (∫ t in (0 : ℝ)..u, f t ^ 2) ≤
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ^ 2 * (u : ℝ) ^ (1 - 2 / p.toReal) := by
  have hmeasure := Measure.restrict_mono (Icc_subset_Icc (le_rfl : (0 : ℝ) ≤ 0) u.property.2) (le_rfl : volume ≤ volume)
  have hfu := hf.mono_measure hmeasure
  have hsq : MemLp (fun t => f t ^ 2) (p / 2) (volume.restrict (Icc (0 : ℝ) u)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hfu.norm_rpow_div (2 : ℝ≥0∞)
  have hhalf : (1 : ℝ≥0∞) ≤ p / 2 := by
    have hh := ENNReal.div_le_div_right hp 2
    rw [ENNReal.div_self (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)] at hh
    exact hh
  have hn : eLpNorm (fun t => f t ^ 2) (p / 2) (volume.restrict (Icc (0 : ℝ) u)) =
      eLpNorm f p (volume.restrict (Icc (0 : ℝ) u)) ^ (2 : ℕ) := by
    have he := eLpNorm_norm_rpow (p := p / 2) (μ := volume.restrict (Icc (0 : ℝ) u)) f (by norm_num : (0 : ℝ) < 2)
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_ofNat,
      ENNReal.div_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
      ENNReal.rpow_two] using he
  have hb := incoming_integral_abs_le_lp_power u.property.1 hhalf hsq
  simp only [abs_pow, sq_abs, hn, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    one_div_div] at hb
  have hnorm := ENNReal.toReal_mono hf.2.ne (eLpNorm_mono_measure f hmeasure)
  exact hb.trans (mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).2 hnorm) (Real.rpow_nonneg u.property.1 _))

theorem incoming_integral_sq_le_lp (hU : 0 ≤ U) (hU1 : U ≤ 1) {p : ℝ≥0∞}
    (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    (∫ t in (0 : ℝ)..U, (f t) ^ 2) ≤ (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ^ 2 := by
  have hp2 : (2 : ℝ≥0∞) ≤ p := (by norm_num : (2 : ℝ≥0∞) ≤ 4).trans hp
  have hexp : 0 ≤ 1 - 2 / p.toReal := by
    by_cases ht : p = ∞
    · simp [ht]
    · have hp' : (2 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono ht hp2
      have hb := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 2) hp'
      norm_num at hb
      linarith only [hb]
  exact (incoming_integral_sq_le_lp_power hp2 hf ⟨U, hU, le_rfl⟩).trans
    (mul_le_of_le_one_right (sq_nonneg _) (Real.rpow_le_one hU hU1 hexp))

theorem incomingWaveVelocity_norm_le (hU : 0 ≤ U) (hU1 : U ≤ 1) {R : ℝ} (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {A : ℝ} (hA : (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A) :
    ‖incomingWaveVelocity hUR hp hf‖ ≤ 1 + A + R * A ^ 2 := by
  rw [← incomingL4Map_eq_velocity hU hUR hp hf]
  refine (incomingL4Map_norm_le hU hU1 hUR _).trans ?_
  have hfA := (incomingL4_norm_le_lp hU1 hp hf).trans hA
  have hsq := sq_le_sq₀ (norm_nonneg ((hf.mono_exponent hp).toLp f)) ((norm_nonneg _).trans hfA) |>.2 hfA
  have hR : 0 ≤ R := hU.trans hUR.le
  linarith [mul_le_mul_of_nonneg_left hsq hR]

theorem incomingWaveVelocity_difference (hU : 0 ≤ U) (hU1 : U ≤ 1) {R : ℝ} (hUR : U < R)
    {f g : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    (hg : MemLp g 4 (volume.restrict (Icc 0 U))) :
    ‖incomingWaveVelocity hUR le_rfl hf - incomingWaveVelocity hUR le_rfl hg‖ ≤
      (1 + R * (‖hf.toLp f‖ + ‖hg.toLp g‖)) * ‖hf.toLp f - hg.toLp g‖ := by
  rw [← incomingL4Map_eq_velocity hU hUR le_rfl hf, ← incomingL4Map_eq_velocity hU hUR le_rfl hg]
  exact incomingL4Map_difference hU hU1 hUR _ _

theorem incomingWaveVelocity_tendsto {ι : Type*} {l : Filter ι} (hU : 0 ≤ U) {R : ℝ}
    (hUR : U < R) {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) 4 (volume.restrict (Icc 0 U)))
    (hg : MemLp g 4 (volume.restrict (Icc 0 U)))
    (hlim : Filter.Tendsto (fun i => (hf i).toLp (f i)) l (nhds (hg.toLp g))) :
    Filter.Tendsto (fun i => incomingWaveVelocity hUR le_rfl (hf i)) l
      (nhds (incomingWaveVelocity hUR le_rfl hg)) := by
  have heq (i : ι) : incomingL4Map hU R ((hf i).toLp (f i)) =
      incomingWaveVelocity hUR le_rfl (hf i) := incomingL4Map_eq_velocity hU hUR le_rfl (hf i)
  have hgq : incomingL4Map hU R (hg.toLp g) = incomingWaveVelocity hUR le_rfl hg :=
    incomingL4Map_eq_velocity hU hUR le_rfl hg
  simpa only [Function.comp_def, heq, hgq] using
    (incomingL4Map_continuous hU R).continuousAt.tendsto.comp hlim

theorem incomingWaveCurve_difference (hU : 0 ≤ U) (hU1 : U ≤ 1) {R : ℝ} (hUR : U < R)
    {f g : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    (hg : MemLp g 4 (volume.restrict (Icc 0 U))) (φ₀ : ℝ) :
    ‖incomingWaveCurve hU hUR le_rfl hf φ₀ - incomingWaveCurve hU hUR le_rfl hg φ₀‖ ≤
      Real.sqrt U * ((1 + R * (‖hf.toLp f‖ + ‖hg.toLp g‖)) * ‖hf.toLp f - hg.toLp g‖) := by
  simp only [incomingWaveCurve, add_sub_add_left_eq_sub, ← horizontalPrimitive_sub]
  refine (horizontalPrimitive_norm_le hU _).trans ?_
  simpa only [sub_zero] using
    (mul_le_mul_of_nonneg_left (incomingWaveVelocity_difference hU hU1 hUR hf hg) (Real.sqrt_nonneg U))

end CauchyHorizon
