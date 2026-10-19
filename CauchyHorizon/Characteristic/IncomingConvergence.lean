import CauchyHorizon.Characteristic.IncomingEstimates
import CauchyHorizon.Reduced.RegularRadius

/-! Small incoming scalar data give uniform convergence of the compatible metric coefficients. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

def HasConvergentIncomingData {U R : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, MemLp (f n) p (volume.restrict (Icc 0 U))) (φ₀ : ℝ) : Prop :=
  Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 U))).toReal) atTop (𝓝 0) ∧
  Tendsto (fun n => incomingWaveVelocity hUR hp (hf n)) atTop
    (𝓝 (incomingWaveVelocity hUR hp (hf 0))) ∧
  Tendsto (fun n => incomingWaveCurve hU hUR hp (hf n) φ₀) atTop
    (𝓝 (incomingWaveCurve hU hUR hp (hf 0) φ₀)) ∧
  Tendsto (fun n => waveAmplitude (incomingWaveCurve hU hUR hp (hf n) φ₀)) atTop
    (𝓝 (waveAmplitude (incomingWaveCurve hU hUR hp (hf 0) φ₀))) ∧
  Tendsto (fun n => waveRadius (incomingWaveCurve hU hUR hp (hf n) φ₀) ^ 2) atTop
    (𝓝 (waveRadius (incomingWaveCurve hU hUR hp (hf 0) φ₀) ^ 2))

theorem incoming_data_convergence {U R : ℝ} (hU : 0 ≤ U) (hU1 : U ≤ 1) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, MemLp (f n) p (volume.restrict (Icc 0 U))) (hzero : f 0 = 0)
    (hlim : Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 U))).toReal)
      atTop (𝓝 0)) (φ₀ : ℝ) : HasConvergentIncomingData hU hUR hp f hf φ₀ := by
  have h4 : Tendsto (fun n => ((hf n).mono_exponent hp).toLp (f n)) atTop (𝓝 0) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => incomingL4_norm_le_lp hU1 hp (hf n)) hlim
  have heq (n : ℕ) := incomingL4Map_eq_velocity hU hUR hp (hf n)
  have heq0 : incomingL4Map hU R 0 = incomingWaveVelocity hUR hp (hf 0) := by
    simpa only [hzero, MemLp.toLp_zero] using heq 0
  have hv : Tendsto (fun n => incomingWaveVelocity hUR hp (hf n)) atTop
      (𝓝 (incomingWaveVelocity hUR hp (hf 0))) := by
    simpa only [Function.comp_def, heq, heq0] using
      (incomingL4Map_continuous hU R).tendsto 0 |>.comp h4
  have hc : Tendsto (fun n => incomingWaveCurve hU hUR hp (hf n) φ₀) atTop
      (𝓝 (incomingWaveCurve hU hUR hp (hf 0) φ₀)) :=
    tendsto_const_nhds.add ((horizontalPrimitive_lipschitz hU).continuous.tendsto _ |>.comp hv)
  exact ⟨hlim, hv, hc, waveAmplitude.continuous.tendsto _ |>.comp hc,
    (waveRadius.continuous.tendsto _ |>.comp hc).pow 2⟩

end CauchyHorizon
