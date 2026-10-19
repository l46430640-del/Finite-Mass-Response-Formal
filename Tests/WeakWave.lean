import CauchyHorizon.Reduced.WeakWave
import CauchyHorizon.Reduced.RegularCrossing
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open scoped Distributions

namespace CauchyHorizon.Tests

-- The test need not factor into a function of each coordinate.
private def polynomialWaveTest : WaveTest 1 1 where
  val u v := u * (1 - u) * v * (1 - v) * (u + v)
  du u v := ((1 - 2 * u) * (u + v) + u * (1 - u)) * v * (1 - v)
  duv u v := (1 - 2 * u) * v * (1 - v) +
    ((1 - 2 * u) * (u + v) + u * (1 - u)) * (1 - 2 * v)
  continuous_val := by fun_prop
  continuous_du := by fun_prop
  continuous_duv := by fun_prop
  smooth_u := by intro v; fun_prop
  deriv_u := by
    intro u v
    convert ((((hasDerivAt_id u).mul ((hasDerivAt_const u (1 : ℝ)).sub
      (hasDerivAt_id u))).mul_const v).mul_const (1 - v)).mul
        ((hasDerivAt_id u).add_const v) using 1 <;> first | rfl | (dsimp; ring)
  deriv_du_v := by
    intro u v
    convert ((((hasDerivAt_const v (1 - 2 * u)).mul
      ((hasDerivAt_const v u).add (hasDerivAt_id v))).add_const (u * (1 - u))).mul
        (hasDerivAt_id v)).mul ((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)) using 1 <;>
      first | rfl | (dsimp; ring)
  boundary_u := by intro v; constructor <;> ring
  boundary_du_v := by intro u; constructor <;> ring

-- No condition forces a test to vanish at an interior joining hypersurface.
example : polynomialWaveTest.val (1 / 2) (1 / 2) = 1 / 16 := by
  norm_num [polynomialWaveTest]

example {f f' g g' : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f 0 0)
    (hfd : ∀ᵐ t ∂volume.restrict (Icc 0 0), HasDerivWithinAt f (f' t) (Icc 0 0) t)
    (hg : ContDiff ℝ 1 g) (hgd : ∀ t ∈ Icc 0 0, HasDerivWithinAt g (g' t) (Icc 0 0) t)
    (hg0 : g 0 = 0) :
    (∫ t in (0 : ℝ)..0, f' t * g t) = -(∫ t in (0 : ℝ)..0, f t * g' t) :=
  (integral_weak_derivative le_rfl hf hfd hg hgd hg0 hg0).2

-- The scalar source retains its minus sign and both stored velocity components.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (ψ : WaveTest U V) :
    let z := fun u v => x.1 (projIcc 0 U hU u) (projIcc 0 V hV v)
    let p := fun u v => x.2.1 (projIcc 0 U hU u) (projIcc 0 V hV v)
    let q := fun u v => x.2.2 u (projIcc 0 V hV v)
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      (-(q u v 0 * p u v 1 + p u v 0 * q u v 1) / z u v 0) * ψ.val u v) =
      ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, z u v 1 * ψ.duv u v :=
  (hx.weak_wave_equation ψ 1).2

-- Compatible incoming data identify the rough velocity with the actual field derivative.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    HasWeakWaveEquation hU hV e Λ x ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U),
        HasDerivWithinAt (intervalExtension hU x.1) (x.2.2 u) (Icc 0 U) u :=
  ⟨hx.weak_wave_equation, hx.horizontal_derivative hzin⟩

-- All three equations are tested on the same rectangle that crosses V=0.
example {U ε e Λ T₀ u₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀) :
    ∃ L T b : ℝ,
      let V := regularTime (anchoringLapse (hε.trans hεU) X)
      ∃ hL : 0 ≤ L, ∃ hV : 0 ≤ b - V T, ∃ y : WaveState (b - V T) L,
        V T < 0 ∧ 0 < b ∧ (∀ t s, 0 < y.1 t s 0) ∧ HasWeakWaveEquation hV hL e Λ y ∧
          HasDistributionalWaveEquation hV hL e Λ y ∧ HasL2WaveDerivatives hV hL y ∧
            HasL2MetricCoefficients hV hL y ∧ HasL2CoordinateMetric hV hL y ∧
              HasL2CoordinateConnection hV hL y ∧ HasCoordinateRicci hV hL y ∧
                HasNullRicciSources hV hL y ∧ HasMixedRicciSources hV hL e Λ y ∧
                  HasAngularRicciSources hV hL e Λ y ∧ HasOffDiagonalRicciSources hV hL y ∧
                    HasCoordinateMaxwell hV hL e y ∧ HasCoordinateEinsteinEquation hV hL e Λ y ∧
                    HasCoordinateScalarEquation hV hL y := by
  obtain ⟨_ua, L, T, b, _hea, _ham, _hmr, _hrU, _hT₀, _hT, hn, hb,
    hL, hV, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, _hfuture, _hout, _hxin, _hbottom,
    hr, _hmatch, _hvelocity, _hc, _hi, hweak, hdistribution, hL2, hmetric, hcoord, hconnection,
    hRicci, hsource, hmixed, hangular, hoffdiag, hmaxwell, heinstein, hscalar, _hradial⟩ := hcross
  exact ⟨L, T, b, hL, hV, y, hn, hb, hr, hweak, hdistribution, hL2, hmetric, hcoord, hconnection,
    hRicci, hsource, hmixed, hangular, hoffdiag, hmaxwell, heinstein, hscalar⟩

-- The standard test space contains a test nonzero at every interior point, including the horizon.
example {U V : ℝ} {w : ℝ × ℝ} (hw : w ∈ openRectangle U V) :
    ∃ ψ : 𝓓(openRectangle U V, ℝ), (WaveTest.ofTestFunction ψ).val w.1 w.2 = 1 := by
  obtain ⟨f, hs, hc, hd, _hrange, hf⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((openRectangle U V).isOpen.mem_nhds hw)
  exact ⟨⟨f, hd, hc, hs⟩, hf⟩

-- The test's mixed derivative has the order required by two distributional derivatives.
example {U V : ℝ} (ψ : 𝓓(openRectangle U V, ℝ)) (u v : ℝ) :
    HasDerivAt (fun t => (WaveTest.ofTestFunction ψ).du u t)
      ((TestFunction.lineDerivCLM ℝ (0, 1)
        (TestFunction.lineDerivCLM ℝ (1, 0) ψ : 𝓓(openRectangle U V, ℝ)) :
          𝓓(openRectangle U V, ℝ)) (u, v)) v :=
  (WaveTest.ofTestFunction ψ).deriv_du_v u v

-- Pairing uses ordinary two-dimensional Lebesgue measure, with integrability proved.
example {U V : ℝ} {f : ℝ × ℝ → ℝ} (hf : IntegrableOn f (Icc 0 U ×ˢ Icc 0 V))
    (ψ : 𝓓(openRectangle U V, ℝ)) :
    Integrable (fun w => f w * ψ w) ∧
      rectangleDistribution U V f ψ = ∫ w, f w * ψ w :=
  rectangleDistribution_pairing hf ψ

-- The radius equation keeps its potential and quadratic null-derivative term.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) :
    let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
    let p := fun w : ℝ × ℝ => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
    let q := fun w : ℝ × ℝ => x.2.2 w.1 (projIcc 0 V hV w.2)
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1, 0)
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, 1)
        (rectangleDistribution U V (fun w => z w 0))) =
      rectangleDistribution U V (fun w =>
        Real.exp (z w 2) * radialPotential (z w 0) e Λ - q w 0 * p w 0 / z w 0) :=
  (hx.distributional_wave_equation 0).2

-- The mixed-space representative gives a genuine two-dimensional L2 function.
example {U V : ℝ} (hV : 0 ≤ V) (F : Lp C(Icc 0 V, ℝ) 2 (volume.restrict (Icc 0 U))) :
    MemLp (fun w : ℝ × ℝ => F w.1 (projIcc 0 V hV w.2)) 2
      (volume.restrict (Icc 0 U ×ˢ Icc 0 V)) :=
  memLp_rectangle_evaluation hV F

-- The scalar's rough derivative has integrable square, without pointwise boundedness.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    IntegrableOn (fun w : ℝ × ℝ => (x.2.2 w.1 (projIcc 0 V hV w.2) 1) ^ 2)
      (Icc 0 U ×ˢ Icc 0 V) := by
  have hq := (hx.weak_first_derivatives hzin 1).2.2.1
  exact (memLp_two_iff_integrable_sq hq.1).1 hq

-- Both weak conformal derivatives coincide with the stored components on the same field.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    let ℓ := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) 2
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1, 0) (rectangleDistribution U V ℓ) =
        rectangleDistribution U V (fun w => x.2.2 w.1 (projIcc 0 V hV w.2) 2) ∧
      Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, 1) (rectangleDistribution U V ℓ) =
        rectangleDistribution U V (fun w => x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) 2) :=
  (hx.weak_first_derivatives hzin 2).2.2.2

-- The conformal coefficient itself, not just its logarithm, has the stated weak derivatives.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    let H := fun w : ℝ × ℝ => Real.exp (x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) 2)
    Continuous H ∧ (∀ w, 0 < H w) ∧ HasL2FirstDerivatives U V H
      (fun w => H w * x.2.2 w.1 (projIcc 0 V hV w.2) 2)
      (fun w => H w * x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) 2) := by
  have hh := hx.metric_coefficients hzin
  exact ⟨hh.1, fun w => (hh.2.2.1 w).1, hh.2.2.2.1⟩

-- The sphere coefficient keeps the factor 2 and both actual radial velocities.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    let r := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) 0
    HasL2FirstDerivatives U V (fun w => (r w) ^ 2)
      (fun w => 2 * r w * x.2.2 w.1 (projIcc 0 V hV w.2) 0)
      (fun w => 2 * r w * x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2) 0) :=
  (hx.metric_coefficients hzin).2.2.2.2

-- Local smoothness on the actual image suffices, even for inverse radius.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn) :
    let z := fun w : ℝ × ℝ => x.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2)
    let G := fun z : WaveVector => (z 0)⁻¹
    HasL2FirstDerivatives U V (fun w => G (z w))
      (fun w => fderiv ℝ G (z w) (x.2.2 w.1 (projIcc 0 V hV w.2)))
      (fun w => fderiv ℝ G (z w) (x.2.1 (projIcc 0 U hU w.1) (projIcc 0 V hV w.2))) :=
  hx.weak_composition hzin _ (fun u v =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff.contDiffAt.inv
      (hx.choose u v))

end CauchyHorizon.Tests
