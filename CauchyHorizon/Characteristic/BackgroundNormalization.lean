import CauchyHorizon.Characteristic.MassFlux
import CauchyHorizon.Reduced.MassRadialRate
import CauchyHorizon.Radial.Coordinate

/-! Transport of the actual radial Jacobian and phase relative to RN-dS. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon

theorem Background.F_hasDerivAt (B : Background) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt B.F (2 * horizonK r B.mass B.charge B.cosmological) r := by
  change HasDerivAt (fun w => horizonFunction w B.mass B.charge B.cosmological) _ _
  simpa only [id_eq, mul_one, mul_zero, zero_div, sub_zero] using
    horizonFunction_hasDerivAt (hasDerivAt_id r) (hasDerivAt_const r B.mass) hr B.charge B.cosmological

theorem IsWaveIntegral.background_normalization_derivative (B : Background)
    {U V : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological zIn vOut uIn x)
    (hr : ∀ u v, x.1 u v 0 ≠ 0) (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 V)
    (hν : radialNuField hV B.charge B.cosmological zIn x.1 hr u v ≠ 0)
    (hband : x.1 u v 0 ∈ Ioo B.inner B.event) :
    let ν := radialNuField hV B.charge B.cosmological zIn x.1 hr
    let m := massField B.charge B.cosmological x.1 x.2.1 ν hr
    let R := fun t => intervalExtension hV (x.1 u) t 0
    let N := intervalExtension hV (ν u)
    let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
    HasDerivWithinAt (fun t => Real.log ((u : ℝ) * N t / B.F (R t)))
      (2 * κ * (m u v - B.mass) *
        (1 / (x.1 u v 0) ^ 2 + deriv B.F (x.1 u v 0) / (x.1 u v 0 * B.F (x.1 u v 0))))
      (Icc 0 V) v ∧
    HasDerivWithinAt (fun t => Real.log (B.z (R t)) - B.outerRate * t)
      (B.outerRate * (κ - 1) -
        2 * B.outerRate * κ * (m u v - B.mass) / (x.1 u v 0 * B.F (x.1 u v 0)))
      (Icc 0 V) v := by
  let ν := radialNuField hV B.charge B.cosmological zIn x.1 hr
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hr
  let R := fun t => intervalExtension hV (x.1 u) t 0
  let N := intervalExtension hV (ν u)
  let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
  have hn : ν u v ≠ 0 := hν
  have hR : HasDerivWithinAt R (x.2.1 u v 0) (Icc 0 V) v :=
    (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      (v : ℝ) (hx.longitudinal_derivative u v.property)
  have hfo := renormalizedMass_first_order (hr u v) hν (x.2.1 u v 0) (x.1 u v 2)
    B.charge B.cosmological
  change x.2.1 u v 0 = κ * horizonFunction (x.1 u v 0) (m u v) B.charge B.cosmological ∧
    Real.exp (x.1 u v 2) * radialPotential (x.1 u v 0) B.charge B.cosmological / ν u v -
      x.2.1 u v 0 / x.1 u v 0 = 2 * κ * horizonK (x.1 u v 0) (m u v) B.charge B.cosmological at hfo
  have hN : HasDerivWithinAt N
      (2 * κ * horizonK (x.1 u v 0) (m u v) B.charge B.cosmological * ν u v) (Icc 0 V) v := by
    apply (hx.radialNu_hasDerivWithinAt hr u v).congr_deriv
    rw [radialSourceField_apply]
    change Real.exp (x.1 u v 2) * radialPotential (x.1 u v 0) B.charge B.cosmological -
      ν u v * x.2.1 u v 0 / x.1 u v 0 = _
    calc
      _ = (Real.exp (x.1 u v 2) * radialPotential (x.1 u v 0) B.charge B.cosmological / ν u v -
          x.2.1 u v 0 / x.1 u v 0) * ν u v := by field_simp [hn]
      _ = _ := by rw [hfo.2]
  have hF := B.F_hasDerivAt (hr u v)
  have hF0 := (B.F_neg hband).ne
  have hRv : R v = x.1 u v 0 := by simp only [R, intervalExtension_apply, projIcc_of_mem hV v.property]
  have hNv : N v = ν u v := by simp only [N, intervalExtension_apply, projIcc_of_mem hV v.property]
  have hFcomp : HasDerivWithinAt (fun t => B.F (R t))
      (2 * horizonK (x.1 u v 0) B.mass B.charge B.cosmological * x.2.1 u v 0) (Icc 0 V) v :=
    (hF.comp_hasDerivWithinAt_of_eq (v : ℝ) hR hRv.symm)
  have hK : horizonK (x.1 u v 0) (m u v) B.charge B.cosmological =
      horizonK (x.1 u v 0) B.mass B.charge B.cosmological + (m u v - B.mass) / (x.1 u v 0) ^ 2 := by
    unfold horizonK
    ring
  have hmass := horizonFunction_mass_difference (x.1 u v 0) (m u v) B.mass B.charge B.cosmological
  change horizonFunction _ _ _ _ = B.F (x.1 u v 0) - 2 * (m u v - B.mass) / x.1 u v 0 at hmass
  constructor
  · have hh := ((hN.const_mul (u : ℝ)).div hFcomp (by rwa [hRv])).log
      (by change (u : ℝ) * N v / B.F (R v) ≠ 0
          rw [hNv, hRv]; exact div_ne_zero (mul_ne_zero hu.ne' hn) hF0)
    apply hh.congr_deriv
    change _ = 2 * κ * (m u v - B.mass) *
      (1 / (x.1 u v 0) ^ 2 + deriv B.F (x.1 u v 0) / (x.1 u v 0 * B.F (x.1 u v 0)))
    simp only [Pi.div_apply]
    rw [hNv, hRv, hfo.1, hmass, hF.deriv, hK]
    field_simp [hu.ne', hn, hF0, hr u v]
    ring
  · have hz := (B.z_hasDerivAt hband).comp_hasDerivWithinAt_of_eq (v : ℝ) hR hRv.symm
    have hh := (hz.log (by
      change B.z (R v) ≠ 0
      rw [hRv]
      exact (B.z_pos hband).ne')).sub
      ((hasDerivWithinAt_id (v : ℝ) (Icc 0 V)).const_mul B.outerRate)
    apply hh.congr_deriv
    change _ = B.outerRate * (κ - 1) -
      2 * B.outerRate * κ * (m u v - B.mass) / (x.1 u v 0 * B.F (x.1 u v 0))
    simp only [Function.comp_apply]
    rw [hRv, hfo.1, hmass]
    have hz0 := (B.z_pos hband).ne'
    field_simp [hF0, hz0, hr u v]
    ring

theorem Background.exists_band_normalization_control (B : Background) {Y Z : ℝ}
    (hY : B.inner < Y) (hZ : Z < B.event) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U V : ℝ} {h r : ℝ → ℝ}
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
      (u : Icc 0 U), 0 < (u : ℝ) → ∀ a b : Icc 0 V, a ≤ b →
      (∀ v ∈ Icc a b, x.1 u v 0 ∈ Icc Y Z) →
      let ν := radialNuField hV B.charge B.cosmological
        (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
      let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
      let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) /
        (4 * intervalExtension hV (ν u) t)
      |Real.log ((u : ℝ) * ν u b / B.F (x.1 u b 0)) -
        Real.log ((u : ℝ) * ν u a / B.F (x.1 u a 0))| +
      |Real.log (B.z (x.1 u b 0)) - Real.log (B.z (x.1 u a 0)) - B.outerRate * ((b : ℝ) - a)| ≤
        C * ∫ t in (a : ℝ)..b, |intervalExtension hV (m u) t - B.mass| + |κ t - 1| := by
  let A : ℝ → ℝ := fun s => 2 * (1 / s ^ 2 +
    (2 * horizonK s B.mass B.charge B.cosmological) / (s * B.F s))
  let H : ℝ → ℝ := fun s => 2 * B.outerRate / (s * B.F s)
  have hs0 (s : ℝ) (hs : s ∈ Icc Y Z) : s ≠ 0 :=
    (B.inner_pos.trans (hY.trans_le hs.1)).ne'
  have hsF (s : ℝ) (hs : s ∈ Icc Y Z) : B.F s ≠ 0 :=
    (B.F_neg ⟨hY.trans_le hs.1, hs.2.trans_lt hZ⟩).ne
  have hFc : ContinuousOn B.F (Icc Y Z) :=
    fun s hs => (B.F_hasDerivAt (hs0 s hs)).continuousAt.continuousWithinAt
  have hKc : ContinuousOn (fun s => horizonK s B.mass B.charge B.cosmological) (Icc Y Z) := by
    unfold horizonK
    fun_prop (disch := aesop)
  have hAc : ContinuousOn A (Icc Y Z) := by
    dsimp [A]
    fun_prop (disch := aesop)
  have hHc : ContinuousOn H (Icc Y Z) := by
    dsimp [H]
    fun_prop (disch := aesop)
  obtain ⟨A₀, hAb⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  obtain ⟨H₀, hHb⟩ := isCompact_Icc.exists_bound_of_continuousOn hHc
  let K := max 0 A₀ + max 0 H₀ + B.outerRate
  have hK0 : 0 ≤ K := add_nonneg (add_nonneg (le_max_left _ _) (le_max_left _ _)) B.outerRate_pos.le
  refine ⟨2 * K, by positivity, ?_⟩
  intro U V h r hU hV hUR hc hi hrc hr0 hφ hrd p hp f hf x hx u hu a b hab hband
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
  let R := fun t => intervalExtension hV (x.1 u) t 0
  let N := intervalExtension hV (ν u)
  let M := fun t => intervalExtension hV (m u) t - B.mass
  let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) / (4 * N t)
  let Q := fun t => Real.log ((u : ℝ) * N t / B.F (R t))
  let P := fun t => Real.log (B.z (R t)) - B.outerRate * t
  let G := fun t => κ t * M t * A (R t)
  let S := fun t => B.outerRate * (κ t - 1) - κ t * M t * H (R t)
  let E := fun t => |M t| + |κ t - 1|
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hn (w v) : ν w v < 0 := (hg w v).2.2.1
  have hnn (t : ℝ) : N t ≠ 0 := (hn u (projIcc 0 V hV t)).ne
  have hκc : Continuous κ := by dsimp [κ]; fun_prop (disch := aesop)
  have hMc : Continuous M := by dsimp [M]; fun_prop
  have hRc : Continuous R := by dsimp [R]; fun_prop
  have hEc : Continuous E := hMc.abs.add ((hκc.sub continuous_const).abs)
  have hsub : Icc (a : ℝ) b ⊆ Icc 0 V :=
    fun _ ht => ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
  have hrad (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) : R t ∈ Icc Y Z := by
    simpa only [R, intervalExtension_apply, projIcc_of_mem hV (hsub ht)] using hband ⟨t, hsub ht⟩ ht
  have hGc : ContinuousOn G (Icc (a : ℝ) b) :=
    (hκc.mul hMc).continuousOn.mul (hAc.comp hRc.continuousOn hrad)
  have hSc : ContinuousOn S (Icc (a : ℝ) b) :=
    (continuousOn_const.mul (hκc.continuousOn.sub continuousOn_const)).sub
      ((hκc.mul hMc).continuousOn.mul (hHc.comp hRc.continuousOn hrad))
  have hder (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) :
      HasDerivWithinAt Q (G t) (Icc 0 V) t ∧ HasDerivWithinAt P (S t) (Icc 0 V) t := by
    let v : Icc 0 V := ⟨t, hsub ht⟩
    have hrv := hband v ht
    have hh := hx.background_normalization_derivative B hx.choose u hu v (hn u v).ne
      ⟨hY.trans_le hrv.1, hrv.2.trans_lt hZ⟩
    dsimp only at hh
    have hFder := (B.F_hasDerivAt (hx.choose u v)).deriv
    constructor
    · apply hh.1.congr_deriv
      simp only [G, κ, M, R, N, intervalExtension_apply, projIcc_of_mem hV (hsub ht)]
      rw [hFder]
      dsimp [A, v]
      ring
    · apply hh.2.congr_deriv
      simp only [S, κ, M, R, N, intervalExtension_apply, projIcc_of_mem hV (hsub ht)]
      dsimp [H, v]
      ring
  have hQ : ContinuousOn Q (Icc (a : ℝ) b) :=
    fun t ht => ((hder t ht).1.continuousWithinAt).mono hsub
  have hP : ContinuousOn P (Icc (a : ℝ) b) :=
    fun t ht => ((hder t ht).2.continuousWithinAt).mono hsub
  have hQI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (a : ℝ) ≤ b from hab) hQ
    (fun t ht => ((hder t (Ioo_subset_Icc_self ht)).1).hasDerivAt
      (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2)))
    (hGc.intervalIntegrable_of_Icc (show (a : ℝ) ≤ b from hab))
  have hPI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (a : ℝ) ≤ b from hab) hP
    (fun t ht => ((hder t (Ioo_subset_Icc_self ht)).2).hasDerivAt
      (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2)))
    (hSc.intervalIntegrable_of_Icc (show (a : ℝ) ≤ b from hab))
  have hbounds (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) : |G t| ≤ K * E t ∧ |S t| ≤ K * E t := by
    have hk : 0 ≤ κ t ∧ κ t ≤ 1 := by
      simpa only [κ, N, intervalExtension_apply, projIcc_of_mem hV (hsub ht)] using
        And.intro (hg u ⟨t, hsub ht⟩).2.2.2.1.le (hg u ⟨t, hsub ht⟩).2.2.2.2
    have hma : |κ t * M t * A (R t)| ≤ max 0 A₀ * |M t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hk.1]
      calc
        _ ≤ (1 * |M t|) * max 0 A₀ := mul_le_mul
          (mul_le_mul_of_nonneg_right hk.2 (abs_nonneg _))
          ((hAb _ (hrad t ht)).trans (le_max_right _ _)) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hmh : |κ t * M t * H (R t)| ≤ max 0 H₀ * |M t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hk.1]
      calc
        _ ≤ (1 * |M t|) * max 0 H₀ := mul_le_mul
          (mul_le_mul_of_nonneg_right hk.2 (abs_nonneg _))
          ((hHb _ (hrad t ht)).trans (le_max_right _ _)) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hmx : |M t| ≤ E t := le_add_of_nonneg_right (abs_nonneg _)
    have hkx : |κ t - 1| ≤ E t := le_add_of_nonneg_left (abs_nonneg _)
    have hE0 : 0 ≤ E t := (abs_nonneg _).trans hmx
    constructor
    · exact hma.trans ((mul_le_mul_of_nonneg_left hmx (le_max_left _ _)).trans
        (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith [le_max_left 0 H₀, B.outerRate_pos]) hE0))
    · have hs : |S t| ≤ B.outerRate * |κ t - 1| + max 0 H₀ * |M t| := by
        calc
          _ ≤ |B.outerRate * (κ t - 1)| + |κ t * M t * H (R t)| := by
            simpa only [S, sub_eq_add_neg, abs_neg] using
              abs_add_le (B.outerRate * (κ t - 1)) (-(κ t * M t * H (R t)))
          _ ≤ _ := by
            rw [abs_mul, abs_of_pos B.outerRate_pos]
            exact add_le_add le_rfl hmh
      apply hs.trans
      have hsum := add_le_add (mul_le_mul_of_nonneg_left hkx B.outerRate_pos.le)
        (mul_le_mul_of_nonneg_left hmx (le_max_left 0 H₀))
      have hmax : B.outerRate + max 0 H₀ ≤ K := by dsimp [K]; linarith [le_max_left 0 A₀]
      nlinarith only [hsum, mul_le_mul_of_nonneg_right hmax hE0]
  have hGb : |Q b - Q a| ≤ K * ∫ t in (a : ℝ)..b, E t := by
    rw [← hQI, ← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le (f := G) (show (a : ℝ) ≤ b from hab) _
      ((hEc.intervalIntegrable _ _).const_mul K)
    apply ae_of_all
    intro t ht
    exact (hbounds t ⟨ht.1.le, ht.2⟩).1
  have hSb : |P b - P a| ≤ K * ∫ t in (a : ℝ)..b, E t := by
    rw [← hPI, ← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le (f := S) (show (a : ℝ) ≤ b from hab) _
      ((hEc.intervalIntegrable _ _).const_mul K)
    apply ae_of_all
    intro t ht
    exact (hbounds t ⟨ht.1.le, ht.2⟩).2
  have hsum := add_le_add hGb hSb
  have hphase : P b - P a = Real.log (B.z (x.1 u b 0)) - Real.log (B.z (x.1 u a 0)) -
      B.outerRate * ((b : ℝ) - a) := by
    simp only [P, R, intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property]
    ring
  rw [hphase] at hsum
  simpa only [Q, R, N, M, κ, E, intervalExtension_apply,
    projIcc_of_mem hV a.property, projIcc_of_mem hV b.property, two_mul, add_mul] using hsum

end CauchyHorizon
