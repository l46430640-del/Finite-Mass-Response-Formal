import CauchyHorizon.Characteristic.ConstraintWave
import CauchyHorizon.Characteristic.InnerPotential
import CauchyHorizon.Reduced.FiniteRadialFlux
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Positive radial potential controls the late transverse velocity and radius loss. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem radialNuField_flux_nonincrease {U V e Λ : ℝ} (hV : 0 ≤ V)
    (zIn : C(Icc 0 U, WaveVector)) (x : WaveRectangle U V)
    (hr : ∀ u v, x u v 0 ≠ 0) (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b)
    (hpos : ∀ t ∈ Icc a b, 0 ≤ x u t 0)
    (hP : ∀ t ∈ Icc a b, 0 ≤ radialPotential (x u t 0) e Λ) :
    x u b 0 * (-radialNuField hV e Λ zIn x hr u b) ≤
      x u a 0 * (-radialNuField hV e Λ zIn x hr u a) := by
  let F := intervalExtension hV (radialFluxField e Λ x hr u)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (F.continuous.intervalIntegrable (0 : ℝ) a) (F.continuous.intervalIntegrable (a : ℝ) b)
  have hn : 0 ≤ ∫ t in (a : ℝ)..b, F t := by
    apply intervalIntegral.integral_nonneg (show (a : ℝ) ≤ b from hab)
    intro t ht
    have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
    simp only [F, intervalExtension_apply, projIcc_of_mem hV htV, radialFluxField_apply]
    exact mul_nonneg (hpos ⟨t, htV⟩ ht) (mul_nonneg (Real.exp_pos _).le (hP ⟨t, htV⟩ ht))
  have hp : continuousPrimitive hV (radialFluxField e Λ x hr u) a ≤
      continuousPrimitive hV (radialFluxField e Λ x hr u) b := by
    change (∫ t in (0 : ℝ)..a, F t) ≤ ∫ t in (0 : ℝ)..b, F t
    linarith only [hi, hn]
  simp only [radialNuField_apply, mul_neg, mul_div_cancel₀ _ (hr u a),
    mul_div_cancel₀ _ (hr u b)]
  linarith only [hp]

theorem IsWaveIntegral.late_radius_bound (B : Background) {U V R φ₀ Δ N d : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf φ₀) vOut (incomingWaveVelocity hUR hp hf) x)
    (hΔ : 0 < Δ) (hΔr : Δ ≤ B.inner / 4) (hN : 0 ≤ N) (hd : 0 < d)
    (hpot : ∀ r ∈ Icc (B.inner - Δ) (B.inner + Δ),
      B.innerRate / 4 ≤ radialPotential r B.charge B.cosmological)
    (z u : Icc 0 U) (v : Icc 0 V) (hz : 0 < (z : ℝ)) (hzu : z ≤ u)
    (hleft : |x.1 z v 0 - B.inner| ≤ Δ / 2)
    (hentry : ∀ w ∈ Icc z u, ∃ a : Icc 0 V, a ≤ v ∧
      |x.1 w a 0 - B.inner| ≤ Δ / 2 ∧
      -radialNuField hV B.charge B.cosmological (incomingWaveCurve hU hUR hp hf φ₀)
        x.1 hx.choose w a ≤ N * (w : ℝ) ^ (-1 + d) ∧
      ∀ t ∈ Icc a v, x.1 w t 0 ∈ Icc (B.inner - Δ) (B.inner + Δ)) :
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
    (∀ w ∈ Icc z u, -ν w v ≤ 2 * N * (w : ℝ) ^ (-1 + d)) ∧
      x.1 z v 0 - x.1 u v 0 ≤ 2 * N * (u : ℝ) ^ d / d ∧
      (2 * N * (u : ℝ) ^ d / d < Δ / 2 → B.inner - Δ < x.1 u v 0) := by
  dsimp only
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
  have hρ : 0 < B.inner - Δ := by linarith only [hΔr, B.inner_pos]
  have hn (w : Icc 0 U) (hw : w ∈ Icc z u) : -ν w v ≤ 2 * N * (w : ℝ) ^ (-1 + d) := by
    obtain ⟨a, hav, hra, hna, hstrip⟩ := hentry w hw
    have hflux := radialNuField_flux_nonincrease hV
      (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose w a v hav
      (fun t ht => hρ.le.trans (hstrip t ht).1)
      (fun t ht => (by positivity [B.innerRate_pos] : (0 : ℝ) ≤ B.innerRate / 4).trans
        (hpot _ (hstrip t ht)))
    have hrp := hx.incoming_radius_pos hU hV hUR hp hf w a
    have hrlo := (hstrip v (right_mem_Icc.2 hav)).1
    have hrhi := (abs_le.1 hra).2
    have hpow := Real.rpow_nonneg (hz.le.trans hw.1) (-1 + d)
    have hnonneg : 0 ≤ N * (w : ℝ) ^ (-1 + d) := mul_nonneg hN hpow
    have hrcomp : x.1 w a 0 ≤ 2 * x.1 w v 0 := by linarith only [hrhi, hrlo, hΔr, hΔ]
    have hm := mul_le_mul_of_nonneg_left hna hrp.le
    have hc := mul_le_mul_of_nonneg_right hrcomp hnonneg
    have hrv : 0 < x.1 w v 0 := hρ.trans_le hrlo
    apply (mul_le_mul_iff_right₀ hrv).1
    change x.1 w v 0 * (-ν w v) ≤ x.1 w a 0 * (-ν w a) at hflux
    nlinarith only [hflux, hm, hc]
  have hsub : Icc (z : ℝ) u ⊆ Icc 0 U :=
    fun _ ht => ⟨z.property.1.trans ht.1, ht.2.trans u.property.2⟩
  have hnc : Continuous (fun t => intervalExtension hU ν t v) := by fun_prop
  have hrc : Continuous (fun t => intervalExtension hU x.1 t v 0) := by fun_prop
  have hi := (incomingWave_constraint_data hU hUR hp hf φ₀).1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (z : ℝ) ≤ u from hzu) hrc.continuousOn
    (fun t ht => by
      have htU := hsub (Ioo_subset_Icc_self ht)
      simpa only [intervalExtension_apply, projIcc_of_mem hU htU] using
        (hx.radial_hasDerivWithinAt hx.choose rfl hi v htU).hasDerivAt
          (Icc_mem_nhds (z.property.1.trans_lt ht.1) (ht.2.trans_le u.property.2)))
    (hnc.intervalIntegrable (z : ℝ) u)
  simp only [intervalExtension_apply, projIcc_of_mem hU z.property,
    projIcc_of_mem hU u.property] at hFTC
  change (∫ t in (z : ℝ)..u, intervalExtension hU ν t v) = x.1 u v 0 - x.1 z v 0 at hFTC
  have hgap : x.1 z v 0 - x.1 u v 0 = ∫ t in (z : ℝ)..u, -intervalExtension hU ν t v := by
    rw [intervalIntegral.integral_neg]
    linarith only [hFTC]
  have hpowI : IntervalIntegrable (fun t : ℝ => t ^ (-1 + d)) volume (z : ℝ) u :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith only [hd])
  have hbound : x.1 z v 0 - x.1 u v 0 ≤ 2 * N * (u : ℝ) ^ d / d := by
    rw [hgap]
    calc
      _ ≤ ∫ t in (z : ℝ)..u, (2 * N) * t ^ (-1 + d) := by
        apply intervalIntegral.integral_mono_on (show (z : ℝ) ≤ u from hzu)
          (hnc.neg.intervalIntegrable _ _) (hpowI.const_mul (2 * N))
        intro t ht
        change -intervalExtension hU ν t v ≤ 2 * N * t ^ (-1 + d)
        simpa only [intervalExtension_apply, projIcc_of_mem hU (hsub ht)] using hn ⟨t, hsub ht⟩ ht
      _ = (2 * N) * (((u : ℝ) ^ d - (z : ℝ) ^ d) / d) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith only [hd])),
          show -1 + d + 1 = d by ring]
      _ ≤ 2 * N * (u : ℝ) ^ d / d := by
        rw [← mul_div_assoc, mul_sub, sub_div]
        exact sub_le_self _ (div_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hz.le d)) hd.le)
  refine ⟨hn, hbound, ?_⟩
  intro hsmall
  have hl := (abs_le.1 hleft).1
  linarith only [hl, hbound, hsmall]

end CauchyHorizon
