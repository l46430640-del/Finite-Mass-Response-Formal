import CauchyHorizon.Characteristic.LateHorizontal
import CauchyHorizon.Analysis.ArrivalPower

/-! Fix the late scalar amplitude before shrinking the common incoming width. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

set_option maxHeartbeats 800000 in
theorem exists_late_scalar_improvement {ρ N C K L Q D A d c s δ σ q Umax : ℝ}
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hpq : p.toReal.HolderConjugate q)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hC : 0 ≤ C) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hc : 0 < c) (hs : 0 < s)
    (hds : d * s = c) (hδ : 0 < δ) (hsq : s < 1 / q) (hσ : 1 / q < σ)
    (hUmax : 0 < Umax) :
    ∃ H W : ℝ, 0 < H ∧ N < H / 2 ∧ 0 < W ∧ W ≤ Umax ∧
      ∀ (U V R φ₀ e Λ : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < R)
        (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (vOut : C(Icc 0 V, WaveVector)) (x : WaveState U V),
        IsWaveIntegral hU.le hV e Λ (incomingWaveCurve hU.le hUR hp hf φ₀)
          vOut (incomingWaveVelocity hUR hp hf) x → U ≤ W →
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        ∀ γ : ℝ → ℝ, ContinuousOn γ (Ioc 0 U) → StrictAntiOn γ (Ioc 0 U) →
          Tendsto γ (𝓝[>] (0 : ℝ)) atTop →
          (∀ z ∈ Ioc 0 U, z * Real.exp (d * γ z) ≤ D) →
          (∀ u v, ρ ≤ x.1 u v 0) →
          (∀ z : Icc 0 U, 0 < (z : ℝ) → ∀ v : Icc 0 V, γ z = v →
            |x.1 z v 0 * x.2.1 z v 1| ≤ ρ * N * Real.exp (-c * v)) →
          (∀ z u : Icc 0 U, 0 < (z : ℝ) → z ≤ u → ∀ v : Icc 0 V, γ z = v →
            |x.2.1 u v 0| ≤ L * ((z : ℝ) ^ σ * (u : ℝ) ^ (-σ)) +
              Q * H ^ 2 * Real.exp (-(2 * c) * v)) →
          (∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, 0 < t → γ t ≤ v →
            |x.2.2 t v 1| ≤ C * |f t| + (C + K * H) * t ^ (δ + s - 1)) →
          ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V, γ u ≤ v →
            |x.2.1 u v 1| ≤ H / 2 * Real.exp (-c * v) := by
  let H := 4 * (N + 1)
  let G := C + K * H
  let F := fun w : ℝ => L / ρ *
    (C * A * (D ^ s * w ^ (1 / q - s)) / (σ * q - 1) ^ (1 / q) +
      G * w ^ δ * D ^ s / (σ - s)) +
    (Q * H ^ 2 / ρ) * (C * A * w ^ (1 / q) + G * w ^ (δ + s) / (δ + s))
  have hH : 0 < H := by dsimp only [H]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hb : 0 < 1 / q := hs.trans hsq
  have hbs : 0 < 1 / q - s := sub_pos.2 hsq
  have hsum : 0 < δ + s := add_pos hδ hs
  have hsσ : s < σ := hsq.trans hσ
  have hden : 0 < σ * q - 1 := by
    have hh := (div_lt_iff₀ hpq.symm.pos).1 hσ
    linarith only [hh]
  have hFc : Continuous F := by
    unfold F
    fun_prop (disch := positivity)
  have hF0 : F 0 = 0 := by
    simp only [F, Real.zero_rpow hbs.ne', Real.zero_rpow hδ.ne',
      Real.zero_rpow hb.ne', Real.zero_rpow hsum.ne', mul_zero, zero_mul, zero_div, add_zero]
  have hsmall : ∀ᶠ w : ℝ in 𝓝 0, F w < H / 4 :=
    hFc.continuousAt.tendsto.eventually_lt_const (by rw [hF0]; positivity)
  obtain ⟨W, hW, hWmax, hFW⟩ := ((eventually_lt_nhds hUmax).and hsmall).exists_gt
  refine ⟨H, W, hH, ?_, hW, hWmax.le, ?_⟩
  · dsimp only [H]
    linarith only [hN]
  intro U V R φ₀ e Λ hU hV hUR f hf vOut x hx hUW hfn γ hγc hγa hγl hscale hr hentry hlam hψ u hu v huv
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (u : ℝ) :=
    (show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and
      ((eventually_lt_nhds hu).filter_mono nhdsWithin_le_nhds)
  obtain ⟨z₀, hz₀, hzV⟩ := (hnear.and (hγl.eventually (eventually_gt_atTop (v : ℝ)))).exists
  have hsub : Icc z₀ (u : ℝ) ⊆ Ioc 0 U :=
    fun _ ht => ⟨hz₀.1.trans_le ht.1, ht.2.trans u.property.2⟩
  obtain ⟨z, hz, hzt⟩ := intermediate_value_Icc' hz₀.2.le (hγc.mono hsub) ⟨huv, hzV.le⟩
  let z' : Icc 0 U := ⟨z, (hsub hz).1.le, (hsub hz).2⟩
  have hz0 := (hsub hz).1
  have hzW : z ≤ W := (hsub hz).2.trans hUW
  have hzscale : z * Real.exp (d * (v : ℝ)) ≤ D := by
    simpa only [hzt] using hscale z (hsub hz)
  have hzb : z ^ (1 / q) ≤ D ^ s * W ^ (1 / q - s) * Real.exp (-c * v) := by
    simpa only [hds] using arrival_power_upper hz0 hzW hs.le hsq.le hzscale
  have hzs : z ^ s ≤ D ^ s * Real.exp (-c * v) := by
    simpa only [hds, sub_self, Real.rpow_zero, mul_one] using
      arrival_power_upper hz0 hzW hs.le le_rfl hzscale
  have hJ : 0 ≤ Q * H ^ 2 * Real.exp (-(2 * c) * v) := by positivity
  have hbound := hx.late_horizontal_bound (C := C) (G := G) (L := L)
    (J := Q * H ^ 2 * Real.exp (-(2 * c) * v)) (H := ρ * N * Real.exp (-c * v))
    hU.le hV hUR hpq hp hf hρ hσ hs hsσ hδ hC hG hL hJ z' u hz0 hz.2 v (hr u v)
    (hentry z' hz0 v hzt) (by
      intro t ht
      have htU : t ∈ Icc 0 U := ⟨hz0.le.trans ht.1, ht.2.trans u.property.2⟩
      simpa only [projIcc_of_mem hU.le htU] using hlam z' ⟨t, htU⟩ hz0 ht.1 v hzt) (by
      filter_upwards [hψ] with t ht
      intro htm
      exact ht v (hz0.trans_le htm.1)
        ((hγa.antitoneOn (hsub hz) ⟨hz0.trans_le htm.1, htm.2.trans u.property.2⟩ htm.1).trans_eq hzt))
  dsimp only at hbound
  have hCM : C * (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ C * A :=
    mul_le_mul_of_nonneg_left hfn hC
  have hDens : 0 ≤ (σ * q - 1) ^ (1 / q) := Real.rpow_nonneg hden.le _
  have hfirst : C * (eLpNorm f p (volume.restrict (Icc 0 U))).toReal * z ^ (1 / q) /
      (σ * q - 1) ^ (1 / q) ≤
      C * A * (D ^ s * W ^ (1 / q - s) * Real.exp (-c * v)) / (σ * q - 1) ^ (1 / q) :=
    div_le_div_of_nonneg_right (mul_le_mul hCM hzb (by positivity) (by positivity)) hDens
  have hsecond : G * U ^ δ * z ^ s / (σ - s) ≤
      G * W ^ δ * (D ^ s * Real.exp (-c * v)) / (σ - s) :=
    div_le_div_of_nonneg_right (mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hU.le hUW hδ.le) hG) hzs
      (by positivity) (by positivity)) (sub_pos.2 hsσ).le
  have hplain : C * (eLpNorm f p (volume.restrict (Icc 0 U))).toReal * U ^ (1 / q) +
      G * U ^ (δ + s) / (δ + s) ≤ C * A * W ^ (1 / q) + G * W ^ (δ + s) / (δ + s) :=
    add_le_add (mul_le_mul hCM (Real.rpow_le_rpow hU.le hUW hb.le) (by positivity) (by positivity))
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hU.le hUW hsum.le) hG) hsum.le)
  have hdec : Real.exp (-(2 * c) * (v : ℝ)) ≤ Real.exp (-c * v) :=
    Real.exp_le_exp.2 (by nlinarith only [mul_nonneg hc.le v.property.1])
  have hlast := mul_le_mul
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdec (by positivity : 0 ≤ Q * H ^ 2)) hρ.le)
    hplain (by positivity : 0 ≤ C * (eLpNorm f p (volume.restrict (Icc 0 U))).toReal * U ^ (1 / q) +
      G * U ^ (δ + s) / (δ + s)) (by positivity)
  have htotal : |x.2.1 u v 1| ≤ (N + F W) * Real.exp (-c * v) :=
    (hbound.trans (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (div_nonneg hL hρ.le))) hlast)).trans_eq (by
        dsimp only [F, z']
        field_simp
        ring)
  apply htotal.trans (mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le)
  have hNH : N ≤ H / 4 := by dsimp only [H]; linarith
  linarith only [hNH, hFW]

end CauchyHorizon
