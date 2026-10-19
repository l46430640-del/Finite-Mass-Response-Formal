import CauchyHorizon.Reduced.ContinuousWave
import CauchyHorizon.Characteristic.OpticalIdentities
import CauchyHorizon.Analysis.ContinuousFluxDerivative

/-! The wave system and both radial constraints on the same physical fields. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

def HasContinuousWaveSystem {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (x : WaveState U V) : Prop :=
  ∃ hr : ∀ u v, x.1 u v 0 ≠ 0, ∃ D : ℝ → C(Icc 0 V, WaveVector),
    let N := radialNuField hV e Λ zIn x.1 hr
    ContinuousOn D (Ioi 0) ∧ x.2.2 =ᵐ[volume.restrict (Icc 0 U)] D ∧
      (∀ u v, HasDerivWithinAt (intervalExtension hV (x.1 u)) (x.2.1 u v) (Icc 0 V) v ∧
        HasDerivWithinAt (fun t => intervalExtension hV (x.2.1 u) t 0)
          (x.2.1 u v 2 * x.2.1 u v 0 - x.1 u v 0 * x.2.1 u v 1 ^ 2) (Icc 0 V) v) ∧
      ∀ u ∈ Ioc 0 U,
        HasDerivWithinAt (intervalExtension hU x.1) (D u) (Icc 0 U) u ∧
        ∀ v : Icc 0 V,
          D u v 0 = intervalExtension hU N u v ∧
          HasDerivWithinAt (intervalExtension hV (D u))
            (waveSource e Λ (intervalExtension hU x.1 u v) (D u v)
              (intervalExtension hU x.2.1 u v)) (Icc 0 V) v ∧
          HasDerivWithinAt (fun t => intervalExtension hU x.2.1 t v)
            (waveSource e Λ (intervalExtension hU x.1 u v) (D u v)
              (intervalExtension hU x.2.1 u v)) (Icc 0 U) u ∧
          HasDerivWithinAt (fun t => intervalExtension hU N t v)
            (D u v 2 * intervalExtension hU N u v -
              intervalExtension hU x.1 u v 0 * D u v 1 ^ 2) (Icc 0 U) u

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.continuous_wave_system (B : Background) {s l U V : ℝ}
    (A : AdmissibleOutgoingData B s l) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < A.radius 0)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hfc : ContinuousOn f (Ioi 0)) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi A.tail A.radius 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V A.tail_continuous
        (horizon_mass_integrable A.rate_pos A.upper_nonneg A.tail_continuous A.tail_bound)
        A.radius_continuous (fun v => ((sub_pos.2 A.deviation_lt).trans_le (A.radius_lower v)).ne'))
      (incomingWaveVelocity hUR hp hf) x) :
    HasContinuousWaveSystem hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi A.tail A.radius 0)) x := by
  have hF : ContinuousOn (incomingVelocity (A.radius 0) f) (Ioi 0) := by
    unfold incomingVelocity
    fun_prop
  obtain ⟨hinu, hinell⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi A.tail A.radius 0)
  obtain ⟨D, hDc, hDae, hder⟩ := hx.exists_continuous_wave_derivatives rfl hinu hF
    (incomingWaveVelocity_ae hUR hp hf)
  let N := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi A.tail A.radius 0)) x.1 hx.choose
  have hφ := horizonPhi_integrable A.rate_pos A.upper_nonneg (sub_pos.2 A.deviation_lt)
    A.tail_continuous A.radius_continuous A.tail_bound A.radius_lower
  refine ⟨hx.choose, D, hDc, hDae, ?_, fun u hu => ⟨(hder u hu).1, fun v => ?_⟩⟩
  · intro u v
    exact ⟨hx.longitudinal_derivative u v.property,
      hx.outgoing_radial_constraint hU hV hUR A.tail_continuous
        (horizon_mass_integrable A.rate_pos A.upper_nonneg A.tail_continuous A.tail_bound)
        A.radius_continuous (fun t => ((sub_pos.2 A.deviation_lt).trans_le (A.radius_lower t)).ne')
        hφ A.radius_derivative hp hf u v.property⟩
  · have humem : u ∈ Icc 0 U := ⟨hu.1.le, hu.2⟩
    let P (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v)
    have hz (i : Fin 3) := (P i).hasFDerivAt.comp_hasDerivWithinAt u (hder u hu).1
    have hN := hx.radial_hasDerivWithinAt hx.choose rfl hinu v humem
    have hNval : D u v 0 = intervalExtension hU N u v := by
      have hd := ((hz 0).derivWithin (uniqueDiffOn_Icc (hu.1.trans_le hu.2) u humem)).symm.trans
        (hN.derivWithin (uniqueDiffOn_Icc (hu.1.trans_le hu.2) u humem))
      change D u v 0 = N ⟨u, humem⟩ v at hd
      simpa only [intervalExtension_apply, projIcc_of_mem hU humem] using hd
    refine ⟨hNval, (hder u hu).2 v |>.1, (hder u hu).2 v |>.2, ?_⟩
    let W := fun t => intervalExtension hU N t v * Real.exp (-intervalExtension hU x.1 t v 2)
    let G := fun t => -intervalExtension hU x.1 t v 0 *
      Real.exp (-intervalExtension hU x.1 t v 2) * D t v 1 ^ 2
    have hD1 : ContinuousOn (fun t => D t v 1) (Ioi 0) :=
      (P 1).continuous.comp_continuousOn hDc
    have hGc : ContinuousOn G (Ioi 0) := by dsimp only [G]; fun_prop
    have hGae : ∀ᵐ t ∂volume.restrict (Icc 0 U), HasDerivWithinAt W (G t) (Icc 0 U) t := by
      filter_upwards [hx.transverse_constraint hx.choose rfl hinu hinell,
        hx.horizontal_derivative rfl, hDae] with t ht hz htD
      have hd := (ht v).mul (((P 2).hasFDerivAt.comp_hasDerivWithinAt t hz).neg.exp)
      apply hd.congr_deriv
      simp only [P, G, Function.comp_apply, Pi.neg_apply, ContinuousLinearMap.proj_apply,
        ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply, intervalExtension_apply, htD]
      ring
    have hW := absolutelyContinuous_hasDerivWithinAt_of_continuous hU
      (hx.weightedNu_absolutelyContinuous hx.choose rfl v) hGc hGae hu
    have he (t : ℝ) : W t * Real.exp (intervalExtension hU x.1 t v 2) = intervalExtension hU N t v := by
      dsimp only [W]
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    have hd := hW.mul ((hz 2).exp)
    apply (hd.congr_of_mem (fun t _ => (he t).symm) humem).congr_deriv
    simp only [Function.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply,
      ContinuousMap.evalCLM_apply, P, G, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring

end CauchyHorizon
