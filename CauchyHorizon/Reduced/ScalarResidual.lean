import CauchyHorizon.Reduced.ScalarRegularity
import CauchyHorizon.Reduced.ScalarIntegral
import CauchyHorizon.Radial.ModeDerivative

/-! The actual scalar transport residual against a slowly varying radial mode. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.theta_hasDerivWithinAt_of_continuous
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
    {u : ℝ} (hu : u ∈ Ioc 0 U) (v : Icc 0 V) :
    HasDerivWithinAt (fun t => intervalExtension hU x.1 t v 0 * intervalExtension hU x.2.1 t v 1)
      (-x.2.1 ⟨u, hu.1.le, hu.2⟩ v 0 *
        ((zIn ⟨u, hu.1.le, hu.2⟩ 0 * f u +
          scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hx.choose)
            x.2.1 ⟨u, hu.1.le, hu.2⟩ v) / x.1 ⟨u, hu.1.le, hu.2⟩ v 0)) (Icc 0 U) u := by
  let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (1 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  let X := T.compLpL 2 (volume.restrict (Icc 0 U)) x.2.2
  let C := scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hx.choose) x.2.1
  let L := fun t => -x.2.1 (projIcc 0 U hU t) v 0
  let F := fun t => L t * ((zIn (projIcc 0 U hU t) 0 * f t +
    C (projIcc 0 U hU t) v) / x.1 (projIcc 0 U hU t) v 0)
  have hae : (fun t => L t * X t) =ᵐ[volume.restrict (Icc 0 U)] F := by
    filter_upwards [T.coeFn_compLpL x.2.2, hx.zeta_transport hx.choose hinu, hif] with t ht hz hf
    change X t = x.2.2 t v 1 at ht
    rw [ht]
    apply congrArg (L t * ·)
    apply (eq_div_iff (hx.choose _ _)).2
    have hh := hz v
    rw [hf] at hh
    simpa only [mul_comm] using hh
  have hLc : Continuous L := by fun_prop
  have hLi : MemLp L ∞ (volume.restrict (Icc 0 U)) :=
    (intervalExtension hU (⟨fun t => -x.2.1 t v 0, by fun_prop⟩ : C(Icc 0 U, ℝ))).memLp_top
  have hprod : MemLp (fun t => L t * X t) 2 (volume.restrict (Icc 0 U)) := (Lp.memLp X).mul hLi
  have hi : IntervalIntegrable F volume 0 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      ((hprod.integrable (by norm_num)).congr hae)
  have hFc : ContinuousOn F (Ioi 0) := by
    apply ContinuousOn.mul hLc.continuousOn
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t _
      exact hx.choose _ _
  have hiu := hi.mono_set (show uIcc (0 : ℝ) u ⊆ uIcc 0 U by
    rw [uIcc_of_le hu.1.le, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl hu.2)
  have hd := intervalIntegral.integral_hasDerivAt_right hiu
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hFc u hu.1)
    (hFc.continuousAt (isOpen_Ioi.mem_nhds hu.1))
  have he (t : ℝ) (ht : t ∈ Icc 0 U) :
      intervalExtension hU x.1 t v 0 * intervalExtension hU x.2.1 t v 1 =
        x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1 + ∫ w in (0 : ℝ)..t, F w := by
    have hint : (∫ w in (0 : ℝ)..t, -x.2.1 (projIcc 0 U hU w) v 0 * x.2.2 w v 1) =
        ∫ w in (0 : ℝ)..t, F w := by
      simp only [intervalIntegral.integral_of_le ht.1]
      apply integral_congr_ae
      apply ae_mono (Measure.restrict_mono
        (show Ioc (0 : ℝ) t ⊆ Icc 0 U from fun _ hw => ⟨hw.1.le, hw.2.trans ht.2⟩) le_rfl)
      filter_upwards [hae, T.coeFn_compLpL x.2.2] with w hw he
      change X w = x.2.2 w v 1 at he
      simpa only [L, he] using hw
    simp only [intervalExtension_apply, projIcc_of_mem hU ht]
    rw [hx.theta_integral hzin ⟨t, ht⟩ v, hint]
  have hh := (hd.const_add (x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1)).hasDerivWithinAt
    (s := Icc 0 U)
  simpa only [F, L, projIcc_of_mem hU (show u ∈ Icc 0 U from ⟨hu.1.le, hu.2⟩)] using
    hh.congr_of_mem he (show u ∈ Icc 0 U from ⟨hu.1.le, hu.2⟩)

set_option maxHeartbeats 800000 in
theorem IsWaveIntegral.radial_mode_residual
    (B : Background) (hb : B.criticalExponent < 1)
    {U V : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
    (u : Icc 0 U) (v : Icc 0 V) (hu : 0 < (u : ℝ))
    (hr : x.1 u v 0 ∈ Ioo B.inner B.event)
    {H : ℝ → ℝ} {H' : ℝ} (hH : HasDerivWithinAt H H' (Icc 0 V) v) :
    let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
    let C := scalarTransportCorrection hV ν x.2.1
    let r := fun w t => x.1 (projIcc 0 U hU w) (projIcc 0 V hV t) 0
    let ζ := fun w t => zIn (projIcc 0 U hU w) 0 * f w + C (projIcc 0 U hU w) (projIcc 0 V hV t)
    let Θ := fun w t => Real.exp (B.innerRate * t) *
      (r w t * x.2.1 (projIcc 0 U hU w) (projIcc 0 V hV t) 1)
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).1 (B.event - y)
    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).2 (B.event - y)
    let P := fun w t => Θ w t - X (r w t) * H t
    let Q := fun w t => Real.exp (B.innerRate * t) * w * ζ w t / B.criticalWeight (r w t) - W (r w t) * H t
    let r₀ := x.1 u v 0
    let q₀ := B.criticalWeight r₀
    let A := x.2.1 u v 0 / (r₀ * (u : ℝ) * ν u v)
    let Bc := (u : ℝ) * ν u v / (r₀ * x.2.1 u v 0)
    let c₀ := -1 / B.F r₀
    let c := -1 / x.2.1 u v 0
    let S₁ := (A - B.outerRate / r₀) * q₀ * W r₀ * H v
    let S₂ := ((Bc - 1 / (B.outerRate * r₀)) / q₀ * X r₀ +
      B.innerRate * (c - c₀) * W r₀) * H v - c * W r₀ * H'
    ν u v ≠ 0 → x.2.1 u v 0 ≠ 0 →
      ζ u v = r₀ * derivWithin (fun w => intervalExtension hU x.1 w v 1) (Icc 0 U) u ∧
      HasDerivWithinAt (fun w => P w v) (-ν u v * (A * q₀ * Q u v + S₁)) (Icc 0 U) u ∧
      HasDerivWithinAt (fun t => Q u t)
        (-x.2.1 u v 0 * (Bc / q₀ * P u v + B.innerRate * (c - c₀) * Q u v + S₂)) (Icc 0 V) v := by
  intro ν C r ζ Θ X W P Q r₀ q₀ A Bc c₀ c S₁ S₂ hnu hlam
  have hr0 : r₀ ≠ 0 := hx.choose u v
  have hq0 : q₀ ≠ 0 := (B.criticalWeight_pos hr).ne'
  have hF0 := (B.F_neg hr).ne
  have ha0 := B.outerRate_pos.ne'
  have hmode := B.radialMode_radius_hasDerivAt hb hr
  have hmodeU := hmode.1
  have hmodeV := hmode.2
  have hweight := B.criticalWeight_hasDerivAt hr
  have hru : intervalExtension hU x.1 (u : ℝ) v 0 = x.1 u v 0 := by
    simp only [intervalExtension_apply, projIcc_of_mem hU u.property]
  have hrv : intervalExtension hV (x.1 u) (v : ℝ) 0 = x.1 u v 0 := by
    simp only [intervalExtension_apply, projIcc_of_mem hV v.property]
  rw [← hru] at hmodeU
  rw [← hrv] at hmodeV hweight
  have hradU := hx.radial_hasDerivWithinAt hx.choose hzin hinu v u.property
  have hradV := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
    (v : ℝ) (hx.longitudinal_derivative u v.property)
  change HasDerivWithinAt (fun t => intervalExtension hV (x.1 u) t 0)
    (x.2.1 u v 0) (Icc 0 V) v at hradV
  have hζ := hx.scalar_hasDerivWithinAt_of_continuous hzin hinu hc hif
    (show (u : ℝ) ∈ Ioc 0 U from ⟨hu, u.property.2⟩) v
  have hζd := hζ.derivWithin ((uniqueDiffOn_Icc (hu.trans_le u.property.2)) u u.property)
  refine ⟨?_, ?_, ?_⟩
  · rw [hζd]
    dsimp only [ζ, r₀]
    rw [projIcc_of_mem hU u.property, projIcc_of_mem hV v.property, mul_div_cancel₀ _ (hx.choose u v)]
  · have hd := ((hx.theta_hasDerivWithinAt_of_continuous hzin hinu hc hif
        (show (u : ℝ) ∈ Ioc 0 U from ⟨hu, u.property.2⟩) v).const_mul
        (Real.exp (B.innerRate * v))).sub
      ((hmodeU.comp_hasDerivWithinAt (u : ℝ) hradU).mul_const (H v))
    have hd' : HasDerivWithinAt (fun w => P w v)
        (Real.exp (B.innerRate * v) * (-x.2.1 u v 0 * (ζ u v / r₀)) -
          (-(B.outerRate * q₀ / r₀ * W r₀) * ν u v) * H v) (Icc 0 U) u := by
      simpa only [P, Θ, r, ζ, X, W, r₀, q₀, intervalExtension_apply,
        projIcc_of_mem hU u.property, projIcc_of_mem hV v.property, Function.comp_def, Pi.sub_def] using hd
    apply hd'.congr_deriv
    dsimp only [A, S₁, Q, r]
    rw [projIcc_of_mem hU u.property, projIcc_of_mem hV v.property]
    change _ = -ν u v * (_ * q₀ * (Real.exp (B.innerRate * v) * (u : ℝ) * ζ u v / q₀ - W r₀ * H v) + _)
    field_simp [hr0, hq0, hnu, hu.ne']
    ring
  · have hz := (continuousPrimitive_hasDerivWithinAt hV (scalarTransportSource ν x.2.1 u)
      v.property).const_add (zIn u 0 * f u)
    have hz' : HasDerivWithinAt (fun t => ζ u t) (-ν u v * x.2.1 u v 1) (Icc 0 V) v := by
      change HasDerivWithinAt (fun t => zIn u 0 * f u + C u (projIcc 0 V hV t))
        (-ν u v * x.2.1 u v 1) (Icc 0 V) v at hz
      simpa only [ζ, projIcc_of_mem hU u.property] using hz
    have he := ((hasDerivWithinAt_id (v : ℝ) (Icc 0 V)).const_mul B.innerRate).exp
    have hweight := hweight.comp_hasDerivWithinAt (v : ℝ) hradV
    have hqv : B.criticalWeight (intervalExtension hV (x.1 u) (v : ℝ) 0) ≠ 0 := by
      simpa only [intervalExtension_apply, projIcc_of_mem hV v.property] using hq0
    have hd := ((((he.mul_const (u : ℝ)).mul hz').div hweight hqv).sub
      ((hmodeV.comp_hasDerivWithinAt (v : ℝ) hradV).mul hH))
    have hd' : HasDerivWithinAt (fun t => Q u t)
        ((((Real.exp (B.innerRate * v) * B.innerRate) * (u : ℝ) * ζ u v +
          Real.exp (B.innerRate * v) * (u : ℝ) * (-ν u v * x.2.1 u v 1)) * q₀ -
          Real.exp (B.innerRate * v) * (u : ℝ) * ζ u v *
            ((B.innerRate / B.F r₀ * q₀) * x.2.1 u v 0)) / q₀ ^ 2 -
          ((-(X r₀ / (B.outerRate * r₀ * q₀)) * x.2.1 u v 0) * H v + W r₀ * H')) (Icc 0 V) v := by
      simpa only [Q, r, X, W, r₀, q₀, intervalExtension_apply, projIcc_of_mem hU u.property,
        projIcc_of_mem hV v.property, Function.comp_def, mul_one, id_eq,
        Pi.sub_def, Pi.mul_def, Pi.div_def] using hd
    apply hd'.congr_deriv
    dsimp only [Bc, c, c₀, S₂, P, Q, Θ, r]
    rw [projIcc_of_mem hU u.property, projIcc_of_mem hV v.property]
    change _ = -x.2.1 u v 0 *
      ((u : ℝ) * ν u v / (r₀ * x.2.1 u v 0) / q₀ *
          (Real.exp (B.innerRate * v) * (r₀ * x.2.1 u v 1) - X r₀ * H v) +
        B.innerRate * (-1 / x.2.1 u v 0 - -1 / B.F r₀) *
          (Real.exp (B.innerRate * v) * (u : ℝ) * ζ u v / q₀ - W r₀ * H v) + _)
    field_simp [hr0, hq0, hlam, hF0, ha0]
    ring

end CauchyHorizon
