import CauchyHorizon.Characteristic.FirstOrder
import CauchyHorizon.Reduced.ScalarResidual
import CauchyHorizon.Analysis.ContinuousFluxDerivative

/-! Continuous incoming profiles give the physical first-order system at every positive u. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

def HasContinuousFirstOrderEquations {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (x : WaveState U V) : Prop :=
  HasFirstOrderEquations hU hV e Λ zIn x ∧
  ∃ hr : ∀ u v, x.1 u v 0 ≠ 0,
    let N := radialNuField hV e Λ zIn x.1 hr
    let m := massField e Λ x.1 x.2.1 N hr
    let κ := fun u (v : Icc 0 V) => -Real.exp (intervalExtension hU x.1 u v 2) /
      (4 * intervalExtension hU N u v)
    let θ := fun u (v : Icc 0 V) => intervalExtension hU x.1 u v 0 *
      intervalExtension hU x.2.1 u v 1
    ∃ ζ : ℝ → C(Icc 0 V, ℝ), ContinuousOn ζ (Ioi 0) ∧
      (∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        intervalExtension hU x.1 u v 0 * x.2.2 u v 1 = ζ u v) ∧
      ∀ u ∈ Ioc 0 U, ∀ v : Icc 0 V,
        HasDerivWithinAt (fun t => intervalExtension hU x.1 t v 1)
          (ζ u v / intervalExtension hU x.1 u v 0) (Icc 0 U) u ∧
        HasDerivWithinAt (fun t => θ t v)
          (-intervalExtension hU x.2.1 u v 0 * ζ u v / intervalExtension hU x.1 u v 0) (Icc 0 U) u ∧
        HasDerivWithinAt (intervalExtension hV (ζ u))
          (-intervalExtension hU N u v * θ u v / intervalExtension hU x.1 u v 0) (Icc 0 V) v ∧
        HasDerivWithinAt (fun t => intervalExtension hU m t v)
          (horizonFunction (intervalExtension hU x.1 u v 0) (intervalExtension hU m u v) e Λ *
            ζ u v ^ 2 / (2 * intervalExtension hU N u v)) (Icc 0 U) u ∧
        HasDerivWithinAt (fun t => κ t v)
          (κ u v * ζ u v ^ 2 / (intervalExtension hU x.1 u v 0 * intervalExtension hU N u v))
          (Icc 0 U) u

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.continuous_first_order_equations (B : Background) {s l U V : ℝ}
    (D : AdmissibleOutgoingData B s l) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < D.radius 0)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hfc : ContinuousOn f (Ioi 0)) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi D.tail D.radius 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V D.tail_continuous
        (horizon_mass_integrable D.rate_pos D.upper_nonneg D.tail_continuous D.tail_bound)
        D.radius_continuous (fun v => ((sub_pos.2 D.deviation_lt).trans_le (D.radius_lower v)).ne'))
      (incomingWaveVelocity hUR hp hf) x) :
    HasContinuousFirstOrderEquations hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi D.tail D.radius 0)) x := by
  have hold := hx.first_order_equations B D hU hV hUR hp hf
  refine ⟨hold, hx.choose, ?_⟩
  obtain ⟨_hr, hpoint, hae, hκ⟩ := hold
  let zIn := incomingWaveCurve hU hUR hp hf (horizonPhi D.tail D.radius 0)
  let N := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 N hx.choose
  let κ := fun u (v : Icc 0 V) => -Real.exp (intervalExtension hU x.1 u v 2) /
    (4 * intervalExtension hU N u v)
  let C := scalarTransportCorrection hV N x.2.1
  let ζ := fun u => ContinuousMap.const (Icc 0 V) (zIn (projIcc 0 U hU u) 0 * f u) +
    C (projIcc 0 U hU u)
  have hζc : ContinuousOn ζ (Ioi 0) := by dsimp only [ζ]; fun_prop
  obtain ⟨hinu, _hinell⟩ := incomingWave_constraint_data hU hUR hp hf (horizonPhi D.tail D.radius 0)
  have hif : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 1 = f u := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    exact congrArg (fun z : WaveVector => z 1) hu
  have hζae : ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      intervalExtension hU x.1 u v 0 * x.2.2 u v 1 = ζ u v := by
    filter_upwards [hx.zeta_transport hx.choose hinu, hif] with u hu hf
    intro v
    simpa only [ζ, C, N, zIn, ContinuousMap.add_apply, ContinuousMap.const_apply,
      intervalExtension_apply, hf] using hu v
  have hN (u : ℝ) (v : Icc 0 V) : intervalExtension hU N u v ≠ 0 :=
    (hpoint (projIcc 0 U hU u) v).2.1.ne
  have hκc (v : Icc 0 V) : Continuous (fun u => κ u v) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    exact fun u => mul_ne_zero (by norm_num) (hN u v)
  have hFc (v : Icc 0 V) : Continuous (fun u =>
      horizonFunction (intervalExtension hU x.1 u v 0) (intervalExtension hU m u v)
        B.charge B.cosmological) := by
    have hr : Continuous (fun u => intervalExtension hU x.1 u v 0) := by fun_prop
    have hm : Continuous (fun u => intervalExtension hU m u v) := by fun_prop
    exact ((continuous_const.sub ((continuous_const.mul hm).div hr (fun _ => hx.choose _ _))).add
      (continuous_const.div (hr.pow 2) (fun _ => pow_ne_zero 2 (hx.choose _ _)))).sub
      ((continuous_const.mul (hr.pow 2)).div_const 3)
  refine ⟨ζ, hζc, hζae, ?_⟩
  intro u hu v
  have humem : u ∈ Icc 0 U := ⟨hu.1.le, hu.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ζ, C, N, zIn, ContinuousMap.add_apply, ContinuousMap.const_apply,
      intervalExtension_apply, projIcc_of_mem hU humem] using
      hx.scalar_hasDerivWithinAt_of_continuous rfl hinu hfc hif hu v
  · have hd := hx.theta_hasDerivWithinAt_of_continuous rfl hinu hfc hif hu v
    apply hd.congr_deriv
    simp only [ζ, C, N, zIn, ContinuousMap.add_apply, ContinuousMap.const_apply,
      intervalExtension_apply, projIcc_of_mem hU humem, mul_div_assoc]
  · have hd := (continuousPrimitive_hasDerivWithinAt hV (scalarTransportSource N x.2.1
      (projIcc 0 U hU u)) v.property).const_add (zIn (projIcc 0 U hU u) 0 * f u)
    change HasDerivWithinAt (intervalExtension hV (ζ u))
      (-N (projIcc 0 U hU u) v * x.2.1 (projIcc 0 U hU u) v 1) (Icc 0 V) v at hd
    apply hd.congr_deriv
    simp only [intervalExtension_apply]
    field_simp [hx.choose (projIcc 0 U hU u) v]
    dsimp only [N, zIn]
    ring
  · apply absolutelyContinuous_hasDerivWithinAt_of_continuous hU
      (hx.mass_horizontal_absolutelyContinuous hx.choose rfl v) ?_ ?_ hu
    · apply ContinuousOn.div
      · exact (hFc v).continuousOn.mul ((ContinuousMap.evalCLM ℝ v).continuous.comp_continuousOn hζc |>.pow 2)
      · fun_prop
      · exact fun t _ => mul_ne_zero (by norm_num) (hN t v)
    · filter_upwards [hae, hζae] with t ht hζt
      simpa only [hζt v] using (ht.2 v).2.2
  · apply absolutelyContinuous_hasDerivWithinAt_of_continuous hU (hκ v).1 ?_ ?_ hu
    · apply ContinuousOn.div
      · exact (hκc v).continuousOn.mul ((ContinuousMap.evalCLM ℝ v).continuous.comp_continuousOn hζc |>.pow 2)
      · fun_prop
      · exact fun t _ => mul_ne_zero (hx.choose (projIcc 0 U hU t) v) (hN t v)
    · filter_upwards [(hκ v).2, hζae] with t ht hζt
      simpa only [hζt v] using ht

end CauchyHorizon
