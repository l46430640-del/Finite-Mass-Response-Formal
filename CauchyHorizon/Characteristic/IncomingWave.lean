import CauchyHorizon.Characteristic.Incoming
import CauchyHorizon.Reduced.IntegralRegularity
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! The rough incoming data in the actual vector-valued characteristic space. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

noncomputable def incomingVelocity (R : ℝ) (f : ℝ → ℝ) (t : ℝ) : WaveVector :=
  ![-1, f t, -(R - t) * f t ^ 2]

theorem incomingVelocity_memLp {R U : ℝ} (hUR : U < R) {p : ℝ≥0∞} (hp : 4 ≤ p)
    {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    MemLp (incomingVelocity R f) 2 (volume.restrict (Icc 0 U)) := by
  obtain ⟨hf4, hs⟩ := incoming_memLp_sources hUR hp hf
  apply memLp_pi_iff.2
  intro i
  fin_cases i
  · exact memLp_const (-1)
  · exact hf4.mono_exponent (by norm_num)
  · exact hs

noncomputable def incomingWaveVelocity {R U : ℝ} (hUR : U < R) {p : ℝ≥0∞} (hp : 4 ≤ p)
    {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    Lp WaveVector 2 (volume.restrict (Icc 0 U)) :=
  (incomingVelocity_memLp hUR hp hf).toLp (incomingVelocity R f)

theorem incomingWaveVelocity_ae {R U : ℝ} (hUR : U < R) {p : ℝ≥0∞} (hp : 4 ≤ p)
    {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    incomingWaveVelocity hUR hp hf =ᵐ[volume.restrict (Icc 0 U)] incomingVelocity R f :=
  (incomingVelocity_memLp hUR hp hf).coeFn_toLp

noncomputable def incomingWaveCurve {R U : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (φ₀ : ℝ) : C(Icc 0 U, WaveVector) :=
  ContinuousMap.const _ ![R, φ₀, Real.log 4] + horizontalPrimitive hU (incomingWaveVelocity hUR hp hf)

theorem incomingWaveCurve_apply {R U : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (φ₀ : ℝ) (t : Icc 0 U) : incomingWaveCurve hU hUR hp hf φ₀ t =
      ![incomingRadius R t, incomingPhi φ₀ f t, incomingLogOmega R f t] := by
  have hsub : Ioc 0 (t : ℝ) ⊆ Icc 0 U := fun w hw => ⟨hw.1.le, hw.2.trans t.property.2⟩
  have he : (∫ w in (0 : ℝ)..t, incomingWaveVelocity hUR hp hf w) = ∫ w in (0 : ℝ)..t, incomingVelocity R f w := by
    simp only [intervalIntegral.integral_of_le t.property.1]
    exact integral_congr_ae (ae_mono (Measure.restrict_mono hsub le_rfl) (incomingWaveVelocity_ae hUR hp hf))
  have hi : IntervalIntegrable (incomingVelocity R f) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).2
    exact ((incomingVelocity_memLp hUR hp hf).integrable (by norm_num)).mono_measure
      (Measure.restrict_mono (Icc_subset_Icc le_rfl t.property.2) le_rfl)
  change ![R, φ₀, Real.log 4] + (∫ w in (0 : ℝ)..t, incomingWaveVelocity hUR hp hf w) = _
  rw [he]
  ext i
  have hproj := (ContinuousLinearMap.proj i : WaveVector →L[ℝ] ℝ).intervalIntegral_comp_comm hi
  change (∫ w in (0 : ℝ)..t, incomingVelocity R f w i) = (∫ w in (0 : ℝ)..t, incomingVelocity R f w) i at hproj
  change ![R, φ₀, Real.log 4] i + (∫ w in (0 : ℝ)..t, incomingVelocity R f w) i = _
  rw [← hproj]
  fin_cases i <;> dsimp [incomingVelocity, incomingRadius, incomingPhi, incomingLogOmega] <;>
    simp only [neg_mul, intervalIntegral.integral_neg, intervalIntegral.integral_const, sub_zero, smul_eq_mul] <;> ring

theorem incomingWaveCurve_radius {R U : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (φ₀ : ℝ) (t : Icc 0 U) :
    R - U ≤ incomingWaveCurve hU hUR hp hf φ₀ t 0 := by
  rw [incomingWaveCurve_apply]
  change R - U ≤ R - (t : ℝ)
  linarith [t.property.2]

theorem incomingWaveCurve_norm_le {R U : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (φ₀ : ℝ) : ‖incomingWaveCurve hU hUR hp hf φ₀‖ ≤
      ‖(![R, φ₀, Real.log 4] : WaveVector)‖ + Real.sqrt U * ‖incomingWaveVelocity hUR hp hf‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (ContinuousMap.norm_le _ (norm_nonneg (![R, φ₀, Real.log 4] : WaveVector))).2 (fun _ => le_rfl)
  · simpa only [sub_zero] using horizontalPrimitive_norm_le hU (incomingWaveVelocity hUR hp hf)

end CauchyHorizon
