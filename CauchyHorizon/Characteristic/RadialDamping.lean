import CauchyHorizon.Analysis.DampedScalar
import CauchyHorizon.Radial.Restoring
import CauchyHorizon.Characteristic.MassFlux
import CauchyHorizon.Reduced.MassRadialRate

/-! The actual radial equation has signed damping across the inner radius. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem Background.exists_inner_radius_damping (B : Background) {κ₀ : ℝ} (hk : 0 < κ₀) :
    ∃ q : ℝ, 0 < q ∧ ∀ {U V : ℝ} {h r : ℝ → ℝ}
      (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
      (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
      (_hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
      (_hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
        (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
      {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
      {x : WaveState U V}
      (hx : IsWaveIntegral hU hV B.charge B.cosmological
        (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR hp hf) x)
      (u : Icc 0 U) (a b : Icc 0 V), a ≤ b →
      (∀ v ∈ Icc a b, x.1 u v 0 ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2)) →
      let ν := radialNuField hV B.charge B.cosmological
        (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
      let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
      ∀ G : ℝ → ℝ, ContinuousOn G (Icc (a : ℝ) b) →
      (∀ v ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
      (∀ v ∈ Icc a b, |m u v - B.mass| ≤ G v) →
        (∀ v ∈ Icc a b, |x.1 u v 0 - B.inner| ≤ Real.exp (-q * ((v : ℝ) - a)) *
          (|x.1 u a 0 - B.inner| + ∫ t in (a : ℝ)..v,
            Real.exp (q * (t - a)) * ((4 / B.inner) * G t))) ∧
        (∫ t in (a : ℝ)..b, |intervalExtension hV (x.1 u) t 0 - B.inner|) ≤
          (|x.1 u a 0 - B.inner| + (4 / B.inner) * ∫ t in (a : ℝ)..b, G t) / q := by
  obtain ⟨d, d₀, hd₀, hdc, _hdi, hdf⟩ := B.exists_inner_restoring_factor
  refine ⟨κ₀ * d₀, mul_pos hk hd₀, ?_⟩
  intro U V h r hU hV hUR hc hi hrc hr0 hφ hrd p hp f hf x hx u a b hab hrad
  dsimp only
  intro G hG hkappa hmass
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
  let R := fun t => intervalExtension hV (x.1 u) t 0
  let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) /
    (4 * intervalExtension hV (ν u) t)
  let M := fun t => intervalExtension hV (m u) t - B.mass
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hn (w v) : ν w v < 0 := (hg w v).2.2.1
  have hnn (t : ℝ) : intervalExtension hV (ν u) t ≠ 0 := (hn u (projIcc 0 V hV t)).ne
  have hκc : Continuous κ := by unfold κ; fun_prop (disch := aesop)
  have hRc : Continuous R := by fun_prop
  have hsub : Icc (a : ℝ) b ⊆ Icc 0 V :=
    fun _ ht => ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
  have hRrange (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) :
      R t ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2) := by
    simpa only [R, intervalExtension_apply, projIcc_of_mem hV (hsub ht)] using
      hrad ⟨t, hsub ht⟩ ht
  have hκrange (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) : κ₀ ≤ κ t ∧ κ t ≤ 1 := by
    simpa only [κ, intervalExtension_apply, projIcc_of_mem hV (hsub ht)] using
      And.intro (hkappa ⟨t, hsub ht⟩ ht) (hg u ⟨t, hsub ht⟩).2.2.2.2
  have hmass' (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) : |M t| ≤ G t := by
    simpa only [M, intervalExtension_apply, projIcc_of_mem hV (hsub ht)] using
      hmass ⟨t, hsub ht⟩ ht
  have hdamping (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) :
      HasDerivAt (fun s => R s - B.inner)
        (-(κ t * d (R t)) * (R t - B.inner) + (-2 * κ t * M t / R t)) t := by
    have htV := hsub (Ioo_subset_Icc_self ht)
    have hh := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      t (hx.longitudinal_derivative u htV)
    have hdr : HasDerivAt R (x.2.1 u ⟨t, htV⟩ 0) t :=
      hh.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2))
    apply (hdr.sub_const B.inner).congr_deriv
    have hid := massField_lambda_eq_kappa (e := B.charge) (Λ := B.cosmological)
      x.1 x.2.1 ν hx.choose (fun w v => (hn w v).ne) u ⟨t, htV⟩
    rw [hid, horizonFunction_mass_difference _ _ B.mass]
    have hfac := (hdf (R t) (hRrange t (Ioo_subset_Icc_self ht))).2
    simp only [R, intervalExtension_apply, projIcc_of_mem hV htV] at hfac
    change horizonFunction _ B.mass B.charge B.cosmological = _ at hfac
    rw [hfac]
    simp only [κ, R, M, intervalExtension_apply, projIcc_of_mem hV htV]
    ring
  have hforcing (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) :
      |-2 * κ t * M t / R t| ≤ (4 / B.inner) * G t := by
    have hρ : 0 < B.inner / 2 := half_pos B.inner_pos
    have hRt := hRrange t ht
    have hκt := hκrange t ht
    have hκ0 := hk.le.trans hκt.1
    have hm := hmass' t ht
    have hG0 := (abs_nonneg _).trans hm
    calc
      _ = (2 * κ t) * |M t| / R t := by
        rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_pos (hρ.trans_le hRt.1)]
        norm_num
      _ ≤ (2 * 1) * G t / R t := div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hκt.2 (by norm_num)) hm (abs_nonneg _) (by norm_num))
        (hρ.trans_le hRt.1).le
      _ ≤ (2 * 1) * G t / (B.inner / 2) :=
        div_le_div_of_nonneg_left (by positivity) hρ hRt.1
      _ = _ := by ring
  have hb := damped_scalar_bound (show (a : ℝ) ≤ b from hab) (mul_pos hk hd₀)
    (hRc.continuousOn.sub continuousOn_const)
    (hκc.continuousOn.mul (hdc.comp hRc.continuousOn hRrange))
    (hG.const_mul (4 / B.inner)) hdamping
    (fun t ht => mul_le_mul (hκrange t ht).1 (hdf (R t) (hRrange t ht)).1
      hd₀.le (hk.le.trans (hκrange t ht).1)) hforcing
  constructor
  · intro v hv
    simpa only [Pi.sub_apply, R, intervalExtension_apply, projIcc_of_mem hV v.property,
      projIcc_of_mem hV a.property] using hb.1 v hv
  · simpa only [Pi.sub_apply, R, intervalIntegral.integral_const_mul, intervalExtension_apply,
      projIcc_of_mem hV a.property] using hb.2

end CauchyHorizon
