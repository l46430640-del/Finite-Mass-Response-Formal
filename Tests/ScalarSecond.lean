import CauchyHorizon.Reduced.ScalarSecond
import CauchyHorizon.Characteristic.ConstraintWave

open Set MeasureTheory

namespace CauchyHorizon.Tests

-- Critical L4 data need only be continuous away from zero for the first derivatives.
example {U V R e Λ φ₀ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    (hfc : ContinuousOn f (Ioi 0)) (vOut : C(Icc 0 V, WaveVector)) (x : WaveState U V)
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) :
    ∃ D S : ℝ → C(Icc 0 V, WaveVector), ContinuousOn D (Ioi 0) ∧ ContinuousOn S (Ioi 0) ∧
      ∀ u ∈ Ioc 0 U,
        HasDerivWithinAt (intervalExtension hU x.1) (D u) (Icc 0 U) u ∧
        HasDerivWithinAt (intervalExtension hU x.2.1) (S u) (Icc 0 U) u := by
  have hF : ContinuousOn (incomingVelocity R f) (Ioi 0) := by
    unfold incomingVelocity
    fun_prop
  obtain ⟨D, S, hD, hS, _hDae, _hSae, hd⟩ := hx.exists_continuous_horizontal_derivatives rfl
    (incomingWave_constraint_data hU hUR le_rfl hf φ₀).1 hF (incomingWaveVelocity_ae hUR le_rfl hf)
  exact ⟨D, S, hD, hS, hd⟩

-- The C1 section is the actual r times scalar derivative, including the right-hand trace.
example {U V R e Λ φ₀ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    (hfc : ContDiffOn ℝ 1 f (Ioi 0)) (vOut : C(Icc 0 V, WaveVector)) (x : WaveState U V)
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) :
    let zIn := incomingWaveCurve hU hUR le_rfl hf φ₀
    let ν := radialNuField hV e Λ zIn x.1 hx.choose
    let C := scalarTransportCorrection hV ν x.2.1
    let ζ := fun u => ContinuousMap.const (Icc 0 V) (zIn (projIcc 0 U hU u) 0 * f u) +
      intervalExtension hU C u
    ContDiffOn ℝ 1 ζ (Ioo 0 U) ∧ ContinuousOn (deriv ζ) (Ioo 0 U) ∧
      ∀ (u : ℝ) (hu : u ∈ Ioc 0 U), ∀ v : Icc 0 V,
        ζ u v = x.1 ⟨u, hu.1.le, hu.2⟩ v 0 *
          derivWithin (fun w => intervalExtension hU x.1 w v 1) (Icc 0 U) u := by
  intro zIn ν C ζ
  have hF : ContinuousOn (incomingVelocity R f) (Ioi 0) := by
    have hc := hfc.continuousOn
    unfold incomingVelocity
    fun_prop
  have hscalar : ContDiffOn ℝ 1 (fun u => incomingVelocity R f u 1) (Ioi 0) := hfc
  have hn := (incomingWave_constraint_data hU hUR le_rfl hf φ₀).1
  have hh := hx.scalar_transverse_contDiff rfl hn hF (incomingWaveVelocity_ae hUR le_rfl hf) hscalar
  have hζ : ContDiffOn ℝ 1 ζ (Ioo 0 U) := hh.2.2.2
  refine ⟨hζ, hζ.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl, ?_⟩
  have hif : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR le_rfl hf u 1 = f u := by
    filter_upwards [incomingWaveVelocity_ae hUR le_rfl hf] with u hu
    rw [hu]
    rfl
  intro u hu v
  have hd := hx.scalar_hasDerivWithinAt_of_continuous rfl hn hfc.continuousOn hif hu v
  rw [hd.derivWithin ((uniqueDiffOn_Icc (hu.1.trans_le hu.2)) u ⟨hu.1.le, hu.2⟩)]
  simp only [ζ, ContinuousMap.add_apply, ContinuousMap.const_apply, intervalExtension_apply,
    projIcc_of_mem hU (show u ∈ Icc 0 U from ⟨hu.1.le, hu.2⟩)]
  field_simp [hx.choose ⟨u, hu.1.le, hu.2⟩ v]
  dsimp only [zIn, C, ν]
  ring

end CauchyHorizon.Tests
