import CauchyHorizon.Reduced.ScalarTransport
import CauchyHorizon.Analysis.PrimitiveProduct

/-! The horizontal scalar transport law in integral form at the rough data regularity. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.theta_integral {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.1 u v 0 * x.2.1 u v 1 = x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1 +
      ∫ s in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU s) v 0 * x.2.2 s v 1 := by
  let μ := volume.restrict (Icc 0 U)
  let T (i : Fin 3) : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v)
  let F := rectangleSource hU e Λ x hx.choose
  let f := (T 0).compLpL 2 μ x.2.2
  let g := (T 1).compLpL 2 μ F
  let a := c 0 + continuousPrimitive hV vOut v 0
  let b := vOut v 1
  have hrid (w : Icc 0 U) : x.1 w v 0 = a + horizontalPrimitive hU f w := by
    have hp := congrArg (fun q : C(Icc 0 U, ℝ) => q w) (horizontalPrimitive_compLp hU (T 0) x.2.2)
    change horizontalPrimitive hU f w = horizontalPrimitive hU x.2.2 w v 0 at hp
    have hz := congrArg (fun q : WaveRectangle U V => q w v 0) (hx.horizontal_identity hzin)
    change x.1 w v 0 = a + horizontalPrimitive hU x.2.2 w v 0 at hz
    rwa [← hp] at hz
  have hsid (w : Icc 0 U) : x.2.1 w v 1 = b + horizontalPrimitive hU g w := by
    have hp := congrArg (fun q : C(Icc 0 U, ℝ) => q w) (horizontalPrimitive_compLp hU (T 1) F)
    change horizontalPrimitive hU g w = horizontalPrimitive hU F w v 1 at hp
    have hv : ContinuousMap.const _ vOut + horizontalPrimitive hU F = x.2.1 :=
      congrArg (fun y : WaveState U V => y.2.1) hx.choose_spec
    have hz := congrArg (fun q : WaveRectangle U V => q w v 1) hv.symm
    change x.2.1 w v 1 = b + horizontalPrimitive hU F w v 1 at hz
    rwa [← hp] at hz
  have he : (fun s => f s * (b + ∫ w in 0..s, g w) + (a + ∫ w in 0..s, f w) * g s) =ᵐ[μ]
      fun s => -x.2.1 (projIcc 0 U hU s) v 0 * x.2.2 s v 1 := by
    filter_upwards [(T 0).coeFn_compLpL x.2.2, (T 1).coeFn_compLpL F,
      rectangleSource_ae hU e Λ x hx.choose, ae_restrict_mem measurableSet_Icc] with s hf hg hs hm
    change f s = x.2.2 s v 0 at hf
    change g s = F s v 1 at hg
    have hrw := hrid ⟨s, hm⟩
    have hsw := hsid ⟨s, hm⟩
    change x.1 ⟨s, hm⟩ v 0 = a + ∫ w in 0..s, f w at hrw
    change x.2.1 ⟨s, hm⟩ v 1 = b + ∫ w in 0..s, g w at hsw
    rw [hf, hg, ← hrw, ← hsw, hs v, projIcc_of_mem hU hm]
    change _ * _ + x.1 ⟨s, hm⟩ v 0 *
      (-(x.2.2 s v 0 * x.2.1 ⟨s, hm⟩ v 1 + x.2.1 ⟨s, hm⟩ v 0 * x.2.2 s v 1) / x.1 ⟨s, hm⟩ v 0) = _
    field_simp [hx.choose ⟨s, hm⟩ v]
    ring
  have hp := l2_primitive_product hU f g a b u
  have hs : Ioc (0 : ℝ) u ⊆ Icc (0 : ℝ) U := fun _ hs => ⟨hs.1.le, hs.2.trans u.property.2⟩
  rw [intervalIntegral.integral_of_le u.property.1,
    integral_congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) he)] at hp
  have hzero := hrid ⟨0, le_rfl, hU⟩
  change x.1 ⟨0, le_rfl, hU⟩ v 0 = a + (∫ w in (0 : ℝ)..0, f w) at hzero
  simp only [intervalIntegral.integral_same, add_zero] at hzero
  rw [hrid u, hsid u, hzero, intervalIntegral.integral_of_le u.property.1]
  exact hp

end CauchyHorizon
