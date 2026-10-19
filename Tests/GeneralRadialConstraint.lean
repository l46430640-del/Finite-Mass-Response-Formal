import CauchyHorizon.Reduced.GeneralRadialConstraint
import CauchyHorizon.Reduced.LongitudinalConstraint

open Set MeasureTheory

namespace CauchyHorizon.Tests

-- The generalized representative recovers the existing normalized one exactly.
example {U V : ℝ} (hV : 0 ≤ V) (e Λ : ℝ) (zIn : C(Icc 0 U, WaveVector))
    (z : WaveRectangle U V) (hr : ∀ u v, z u v 0 ≠ 0) :
    radialVelocityField hV e Λ (ContinuousMap.const _ (-1)) zIn z hr =
      radialNuField hV e Λ zIn z hr := by
  apply ContinuousMap.ext
  intro u
  apply ContinuousMap.ext
  intro v
  change (zIn u 0 * (-1) + continuousPrimitive hV (radialFluxField e Λ z hr u) v) / z u v 0 = _
  rw [mul_neg_one]
  rfl

-- A different affine radial slope propagates without imposing the old -1 normalization.
example {U V e Λ α : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hin : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u = ![α, 0, 0]) :
    let N := radialVelocityField hV e Λ (ContinuousMap.const _ α) zIn x.1 hx.choose
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      HasDerivWithinAt (fun t => intervalExtension hU N t v)
        (x.2.2 u v 2 * N (projIcc 0 U hU u) v -
          x.1 (projIcc 0 U hU u) v 0 * (x.2.2 u v 1) ^ 2) (Icc 0 U) u := by
  apply (hx.general_radial_constraint hx.choose hzin (ContinuousMap.const _ α) ?_ ?_).2.2
  · filter_upwards [hin] with u hu
    rw [hu]
    rfl
  · filter_upwards [hin] with u hu
    rw [hu]
    change HasDerivWithinAt (fun _ : ℝ => α)
      (0 * α - zIn (projIcc 0 U hU u) 0 * 0 ^ 2) (Icc 0 U) u
    norm_num only [zero_mul, zero_pow, mul_zero, sub_zero]
    exact hasDerivWithinAt_const u (Icc 0 U) α

-- The quadratic initial term is alpha squared, even when it is not one.
example {U V e Λ α : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (hin : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u = ![α, 0, 0]) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      radialFluxVariation (x.1 (projIcc 0 U hU u) v) (x.2.2 u v) = α ^ 2 +
        continuousPrimitive hV (radialFluxDifferential e Λ
          (x.1 (projIcc 0 U hU u)) (x.2.2 u) (hx.choose (projIcc 0 U hU u))) v := by
  filter_upwards [hx.radialFluxVariation_transverse_integral hx.choose, hin] with u hu hin
  intro v
  simpa [radialFluxVariation, hin] using hu v

-- The continuous-direction constraint accepts an arbitrary L2 incoming velocity.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hout : ∀ t (ht : t ∈ Icc 0 V), HasDerivWithinAt (fun s => intervalExtension hV vOut s 0)
      (vOut ⟨t, ht⟩ 2 * vOut ⟨t, ht⟩ 0 -
        x.1 ⟨0, le_rfl, hU⟩ ⟨t, ht⟩ 0 * (vOut ⟨t, ht⟩ 1) ^ 2) (Icc 0 V) t)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.2.1 u v 0 * Real.exp (-x.1 u v 2) =
      x.2.1 u ⟨0, le_rfl, hV⟩ 0 * Real.exp (-x.1 u ⟨0, le_rfl, hV⟩ 2) -
        ∫ t in (0 : ℝ)..v, intervalExtension hV (x.1 u) t 0 *
          Real.exp (-intervalExtension hV (x.1 u) t 2) * (intervalExtension hV (x.2.1 u) t 1) ^ 2 :=
  hx.longitudinal_constraint_integral hx.choose hzin hout u v

-- Positive radius gives the correct sign of the weighted constraint for general incoming data.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, 0 < x.1 u v 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (n : C(Icc 0 U, ℝ))
    (hn : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = n (projIcc 0 U hU u))
    (hnAC : AbsolutelyContinuousOnInterval (intervalExtension hU n) 0 U)
    (hnd : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (intervalExtension hU n)
        (uIn u 2 * n (projIcc 0 U hU u) - zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2) (Icc 0 U) u)
    (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialVelocityField hV e Λ n zIn x.1 (fun u v => (hr u v).ne')
    N u v * Real.exp (-x.1 u v 2) ≤
      N ⟨0, le_rfl, hU⟩ v * Real.exp (-x.1 ⟨0, le_rfl, hU⟩ v 2) := by
  dsimp only
  have he := hx.general_radial_constraint_integral (fun u v => (hr u v).ne') hzin n hn hnAC hnd v
  rw [he.2.2 u]
  apply sub_le_self
  apply intervalIntegral.integral_nonneg_of_forall u.property.1
  intro t
  exact mul_nonneg (mul_nonneg (hr (projIcc 0 U hU t) v).le (Real.exp_pos _).le) (sq_nonneg _)

end CauchyHorizon.Tests
