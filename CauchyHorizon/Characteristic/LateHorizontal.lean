import CauchyHorizon.Characteristic.LateScalar
import CauchyHorizon.Characteristic.IncomingEstimates
import CauchyHorizon.Analysis.PowerKernel

/-! Actual horizontal transport with the late kernel and its small incoming-width factor. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 800000 in
theorem IsWaveIntegral.late_horizontal_bound {U V R₀ φ₀ e Λ ρ σ s δ C G L J H q : ℝ}
    {p : ℝ≥0∞} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R₀) (hpq : p.toReal.HolderConjugate q)
    (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hρ : 0 < ρ) (hσ : 1 / q < σ) (hs : 0 < s) (hsσ : s < σ) (hδ : 0 < δ)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hL : 0 ≤ L) (hJ : 0 ≤ J)
    (z u : Icc 0 U) (hz : 0 < (z : ℝ)) (hzu : z ≤ u) (b : Icc 0 V)
    (hr : ρ ≤ x.1 u b 0) (hentry : |x.1 z b 0 * x.2.1 z b 1| ≤ H)
    (hlam : ∀ t ∈ Icc (z : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
      L * ((z : ℝ) ^ σ * t ^ (-σ)) + J)
    (hψ : ∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.2.2 t b 1| ≤ C * |f t| + G * t ^ (δ + s - 1)) :
    let M := (eLpNorm f p (volume.restrict (Icc 0 U))).toReal
    |x.2.1 u b 1| ≤ H / ρ +
      L / ρ * (C * M * (z : ℝ) ^ (1 / q) / (σ * q - 1) ^ (1 / q) +
        G * U ^ δ * (z : ℝ) ^ s / (σ - s)) +
      J / ρ * (C * M * U ^ (1 / q) + G * U ^ (δ + s) / (δ + s)) := by
  dsimp only
  let M := (eLpNorm f p (volume.restrict (Icc 0 U))).toReal
  let w := fun t : ℝ => (z : ℝ) ^ σ * t ^ (-σ)
  have hsub : Icc (z : ℝ) u ⊆ Icc 0 U := Icc_subset_Icc z.property.1 u.property.2
  have hsub' : uIcc (z : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le (show (z : ℝ) ≤ u from hzu), uIcc_of_le hU]
    exact hsub
  have hpi (a : ℝ) : IntervalIntegrable (fun t : ℝ => t ^ a) volume (z : ℝ) u :=
    (continuousOn_id.rpow_const (fun t ht => Or.inl (hz.trans_le ht.1).ne')).intervalIntegrable_of_Icc hzu
  have hpc (a : ℝ) : ContinuousOn (fun t : ℝ => t ^ a) (uIcc (z : ℝ) u) := by
    rw [uIcc_of_le (show (z : ℝ) ≤ u from hzu)]
    exact continuousOn_id.rpow_const (fun t ht => Or.inl (hz.trans_le ht.1).ne')
  have hfi : IntervalIntegrable (fun t => |f t|) volume 0 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      (hf.integrable ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp)).abs
  have hfzu := hfi.mono_set hsub'
  have hwfi : IntervalIntegrable (fun t => w t * |f t|) volume (z : ℝ) u :=
    hfzu.continuousOn_mul ((hpc (-σ)).const_mul _)
  have hki : IntervalIntegrable (fun t : ℝ => (z : ℝ) ^ σ * t ^ (s - σ - 1)) volume (z : ℝ) u :=
    (hpi _).const_mul _
  have hpfin : p ≠ ∞ := by
    intro htop
    have hh := hpq.pos
    simp [htop] at hh
  have hfreal : MemLp f (ENNReal.ofReal p.toReal) (volume.restrict (Icc 0 U)) := by
    rwa [ENNReal.ofReal_toReal hpfin]
  have hweighted := power_kernel_holder hz (show (z : ℝ) ≤ u from hzu) u.property.2 hpq hσ hfreal
  rw [ENNReal.ofReal_toReal hpfin] at hweighted
  have hkernel := power_kernel_integral hz (show (z : ℝ) ≤ u from hzu) hsσ
  have hplain : (∫ t in (z : ℝ)..u, |f t|) ≤ M * U ^ (1 / q) := by
    have hh := (intervalIntegral.integral_mono_interval z.property.1 hzu u.property.2
      (Filter.Eventually.of_forall (fun t => abs_nonneg (f t))) hfi).trans
      (incoming_integral_abs_le_lp_power hU ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp) hf)
    simpa only [M, one_div, hpq.one_sub_inv] using hh
  have hpower : (∫ t in (z : ℝ)..u, t ^ (δ + s - 1)) ≤ U ^ (δ + s) / (δ + s) := by
    rw [integral_rpow (Or.inl (by linarith only [hδ, hs])), sub_add_cancel]
    apply div_le_div_of_nonneg_right _ (add_pos hδ hs).le
    exact (sub_le_self _ (Real.rpow_nonneg z.property.1 _)).trans
      (Real.rpow_le_rpow u.property.1 u.property.2 (add_pos hδ hs).le)
  let P := fun t : ℝ => L * C * (w t * |f t|) +
    L * G * U ^ δ * ((z : ℝ) ^ σ * t ^ (s - σ - 1)) + J * C * |f t| + J * G * t ^ (δ + s - 1)
  have hi1 := hwfi.const_mul (L * C)
  have hi2 := hki.const_mul (L * G * U ^ δ)
  have hi3 := hfzu.const_mul (J * C)
  have hi4 := (hpi (δ + s - 1)).const_mul (J * G)
  have hPi : IntervalIntegrable P volume (z : ℝ) u := ((hi1.add hi2).add hi3).add hi4
  let F := fun t => -x.2.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1
  have hsource : ∀ᵐ t ∂volume, t ∈ Ioc (z : ℝ) u → ‖F t‖ ≤ P t := by
    apply (ae_restrict_iff' measurableSet_Ioc).1
    filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Icc_self.trans hsub) le_rfl) hψ,
      ae_restrict_mem measurableSet_Ioc] with t ht htm
    have htm' := Ioc_subset_Icc_self htm
    have ht0 := hz.trans htm.1
    have htU := htm.2.trans u.property.2
    have hwp : w t * t ^ (δ + s - 1) ≤ U ^ δ * ((z : ℝ) ^ σ * t ^ (s - σ - 1)) := by
      have he : w t * t ^ (δ + s - 1) = t ^ δ * ((z : ℝ) ^ σ * t ^ (s - σ - 1)) := by
        dsimp only [w]
        rw [mul_assoc, ← Real.rpow_add ht0, mul_left_comm, ← Real.rpow_add ht0]
        congr 2
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht0.le htU hδ.le) (by positivity)
    have hh := mul_le_mul (hlam t htm') (ht htm') (abs_nonneg _)
      (show 0 ≤ L * w t + J by dsimp only [w]; positivity)
    have hk := mul_le_mul_of_nonneg_left hwp (show 0 ≤ L * G by positivity)
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    apply hh.trans
    dsimp only [P]
    nlinarith only [hk]
  have hI := intervalIntegral.norm_integral_le_of_norm_le (show (z : ℝ) ≤ u from hzu) hsource hPi
  rw [Real.norm_eq_abs] at hI
  dsimp only [P] at hI
  rw [intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
    intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul (L * C), intervalIntegral.integral_const_mul (L * G * U ^ δ),
    intervalIntegral.integral_const_mul (J * C), intervalIntegral.integral_const_mul (J * G)] at hI
  have hIb := hI.trans (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hweighted (show 0 ≤ L * C by positivity))
    (mul_le_mul_of_nonneg_left hkernel (show 0 ≤ L * G * U ^ δ by positivity)))
    (mul_le_mul_of_nonneg_left hplain (show 0 ≤ J * C by positivity)))
    (mul_le_mul_of_nonneg_left hpower (show 0 ≤ J * G by positivity)))
  let eval : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (1 : Fin 3)).comp (ContinuousMap.evalCLM ℝ b)
  have hψi : IntervalIntegrable (fun t => x.2.2 t b 1) volume 0 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      ((eval.comp_memLp' (Lp.memLp x.2.2)).integrable (by norm_num))
  have hFi : IntervalIntegrable F volume 0 U := hψi.continuousOn_mul (by fun_prop)
  have h0z : uIcc (0 : ℝ) z ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le z.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl z.property.2
  have hθseg : x.1 u b 0 * x.2.1 u b 1 = x.1 z b 0 * x.2.1 z b 1 + ∫ t in (z : ℝ)..u, F t := by
    rw [hx.theta_integral (c := ![R₀, φ₀, Real.log 4]) rfl u b,
      hx.theta_integral (c := ![R₀, φ₀, Real.log 4]) rfl z b,
      ← intervalIntegral.integral_add_adjacent_intervals (hFi.mono_set h0z) (hFi.mono_set hsub')]
    ring
  have ht := (abs_add_le _ _).trans (add_le_add hentry hIb)
  rw [← hθseg, abs_mul, abs_of_pos (hρ.trans_le hr)] at ht
  have hb := (mul_le_mul_of_nonneg_right hr (abs_nonneg (x.2.1 u b 1))).trans ht
  exact ((le_div_iff₀ hρ).2 (by simpa only [mul_comm ρ] using hb)).trans_eq (by dsimp only [M]; ring)

end CauchyHorizon
