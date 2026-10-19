import CauchyHorizon.Characteristic.EarlyScalar
import CauchyHorizon.Characteristic.FiniteKappa
import CauchyHorizon.Characteristic.OuterBootstrap
import CauchyHorizon.Analysis.PowerEnergy

/-! Horizontal constraint energy on the actual early trapped region. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.early_inverse_nu_bound {M e Λ U V k ε κ₀ β n : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k) (hβ : 0 ≤ β) (hn : 0 < n)
    (u : Icc 0 U) (T b : Icc 0 V) (hTb : T ≤ b) (hwindow : (b : ℝ) ≤ (1 + β) * T)
    (htrap : x.2.1 u T 0 < 0) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 ν hx.choose
    let K := fun v => horizonK (x.1 u v 0) (m u v) e Λ
    n ≤ (u : ℝ) * (-ν u T) →
    (∀ v ∈ Icc T b, κ₀ ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
    (∀ v ∈ Icc T b, |K v + k| ≤ ε) →
      1 / (-ν u b) ≤ ((u : ℝ) / n) * Real.exp ((2 * (k + ε) * β / (1 + β)) * b) := by
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField e Λ x.1 x.2.1 ν hx.choose
  let γ := 2 * (k + ε) * β / (1 + β)
  dsimp only
  intro hentry hk hK
  have hν (v) : ν u v < 0 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1
  have hrcont : Continuous (fun v : Icc 0 V => x.1 u v 0) := (continuous_apply 0).comp (x.1 u).continuous
  have hKcont : Continuous (fun v => horizonK (x.1 u v 0) (m u v) e Λ) :=
    (((m u).continuous.div (hrcont.pow 2) (fun v => pow_ne_zero 2 (hx.choose u v))).sub
      (continuous_const.div (hrcont.pow 3) (fun v => pow_ne_zero 3 (hx.choose u v)))).sub
        ((continuous_const.mul hrcont).div_const 3)
  let E : C(Icc 0 V, ℝ) := ⟨fun v => x.2.1 u v 2 - 2 * horizonK (x.1 u v 0) (m u v) e Λ,
    ((continuous_apply 2).comp (x.2.1 u).continuous).sub (hKcont.const_mul 2)⟩
  have hlow := (hx.inner_segment_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf hκ₀ hε hεk
    (d := ‖E‖) u T b hTb htrap hk hK (fun v _ => by
      change |E v| ≤ ‖E‖
      simpa only [Real.norm_eq_abs] using E.norm_coe_le_norm v)).1.1
  have hα : 0 < 1 + β := by linarith only [hβ]
  have hΔ : (b : ℝ) - T ≤ β / (1 + β) * b := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hα).2
    nlinarith only [hwindow]
  have hg : 0 ≤ 2 * (k + ε) := by linarith only [hε, hεk]
  have hexp : Real.exp (-γ * b) ≤ Real.exp (-(2 * (k + ε)) * ((b : ℝ) - T)) := by
    apply Real.exp_le_exp.2
    have hh := mul_le_mul_of_nonneg_left hΔ hg
    dsimp only [γ]
    calc
      _ = -(2 * (k + ε) * (β / (1 + β) * (b : ℝ))) := by ring
      _ ≤ -(2 * (k + ε) * ((b : ℝ) - T)) := neg_le_neg hh
      _ = _ := by ring
  have hprod : n * Real.exp (-γ * b) ≤ (u : ℝ) * (-ν u b) := by
    calc
      _ ≤ ((u : ℝ) * (-ν u T)) * Real.exp (-(2 * (k + ε)) * ((b : ℝ) - T)) :=
        mul_le_mul hentry hexp (Real.exp_pos _).le (mul_nonneg u.property.1 (neg_pos.2 (hν T)).le)
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlow u.property.1
  have hh := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (γ * b)).le
  rw [mul_assoc n, ← Real.exp_add, show -γ * (b : ℝ) + γ * b = 0 by ring,
    Real.exp_zero, mul_one] at hh
  apply (div_le_iff₀ (neg_pos.2 (hν b))).2
  calc
    1 ≤ ((u : ℝ) * (-ν u b) * Real.exp (γ * b)) / n := (le_div_iff₀ hn).2 (by simpa using hh)
    _ = _ := by dsimp only [γ]; ring

theorem IsWaveIntegral.early_constraint_bound
    {M e Λ U V a c k ε κ₀ β ρ R n N H D A : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hc0 : 0 < c) (hac : c < a) (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k)
    (hβ : 0 ≤ β) (hρ : 0 < ρ) (hR : 0 ≤ R) (hn : 0 < n)
    (hN : 0 ≤ N) (hH : 0 ≤ H) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hpoint : ∀ᵐ t ∂volume.restrict (Icc 0 U), |f t| ≤ A * t ^ (-1 / p.toReal))
    (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (hrow : ∀ w ∈ Icc z u, ρ ≤ x.1 w b 0 ∧ x.1 w b 0 ≤ R)
    (hwidth : (u : ℝ) * Real.exp ((a / (1 + β)) * b) ≤ D) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 ν hx.choose
    let K := fun w v => horizonK (x.1 w v 0) (m w v) e Λ
    let ω := a / (1 + β)
    let γ := 2 * (k + ε) * β / (1 + β)
    let s := 1 - 1 / p.toReal
    let t := c / a
    let F := r 0 * A / ρ
    let G := (N * H / ρ) * (1 / (a - c) + 1 / (2 * κ₀ * (k - ε) + c)) * D ^ (1 - c / a)
    (∀ y ∈ Ioc (z : ℝ) u,
      let w := projIcc 0 U hU y
      ∃ T : Icc 0 V, T ≤ b ∧ (b : ℝ) ≤ (1 + β) * T ∧ x.2.1 w T 0 < 0 ∧
        n ≤ y * (-ν w T) ∧ y * Real.exp (a * T) ≤ D ∧
        (∀ v ≤ T, |ν w v| ≤ N * Real.exp (a * v)) ∧
        (∀ v ≤ b, |x.2.1 w v 1| ≤ H * Real.exp (-c * v)) ∧
        (∀ v ∈ Icc T b, κ₀ ≤ -Real.exp (x.1 w v 2) / (4 * ν w v)) ∧
        (∀ v ∈ Icc T b, |K w v + k| ≤ ε)) →
      (∫ y in (z : ℝ)..u, intervalExtension hU x.1 y b 0 * (x.2.2 y b 1) ^ 2 /
        (-intervalExtension hU ν y b)) ≤
      (R / n) * (F ^ 2 * D ^ (2 * s) / s * Real.exp (-(2 * ω * s - γ) * b) +
        G ^ 2 * D ^ (2 * t) / t * Real.exp (-(2 * ω * t - γ) * b)) := by
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let ω := a / (1 + β)
  let γ := 2 * (k + ε) * β / (1 + β)
  let s := 1 - 1 / p.toReal
  let t := c / a
  let F := r 0 * A / ρ
  let G := (N * H / ρ) * (1 / (a - c) + 1 / (2 * κ₀ * (k - ε) + c)) * D ^ (1 - c / a)
  let W := fun y => intervalExtension hU x.1 y b 0 / (-intervalExtension hU ν y b)
  dsimp only
  intro hmatch
  have ha : 0 < a := hc0.trans hac
  have hs : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (incoming_exponent_bounds hp).1
  have ht : 0 < t := div_pos hc0 ha
  have hF : 0 ≤ F := div_nonneg (mul_nonneg (hU.trans hUR.le) hA) hρ.le
  have hG : 0 ≤ G := by
    have hq : 0 < 2 * κ₀ * (k - ε) := mul_pos (mul_pos (by norm_num) hκ₀) (sub_pos.2 hεk)
    dsimp only [G]
    positivity
  have hsub : Ioc (z : ℝ) u ⊆ Icc 0 U := fun _ hy => ⟨z.property.1.trans hy.1.le, hy.2.trans u.property.2⟩
  have hwmem (y : ℝ) (hy : y ∈ Ioc (z : ℝ) u) : projIcc 0 U hU y ∈ Icc z u := by
    rw [projIcc_of_mem hU (hsub hy)]
    exact ⟨hy.1.le, hy.2⟩
  have hWi : IntervalIntegrable (fun y => W y * (x.2.2 y b 1) ^ 2) volume z u := by
    have hh := (hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd hp hf b).1
    have hsub' : uIcc (z : ℝ) u ⊆ uIcc (0 : ℝ) U := by
      rw [uIcc_of_le (show (z : ℝ) ≤ u from hzu), uIcc_of_le hU]
      exact Icc_subset_Icc z.property.1 u.property.2
    simpa only [W, div_mul_eq_mul_div] using hh.mono_set hsub'
  have hweight : ∀ᵐ y ∂volume.restrict (Ioc (z : ℝ) u), W y ≤ (R / n) * Real.exp (γ * b) * y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    obtain ⟨T, hTb, hwin, htrap, hentry, _hscale, _hpre, _hscalar, hk, hK⟩ := hmatch y hy
    let w := projIcc 0 U hU y
    have hwval : (w : ℝ) = y := by simp only [w, projIcc_of_mem hU (hsub hy)]
    have hnu := hx.early_inverse_nu_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf hκ₀ hε hεk hβ hn
      w T b hTb hwin htrap (by simpa only [hwval] using hentry) hk hK
    rw [hwval] at hnu
    have hn0 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf w b).2.2.1
    calc
      W y = x.1 w b 0 * (1 / (-ν w b)) := by dsimp only [W, intervalExtension_apply, w]; ring
      _ ≤ R * ((y / n) * Real.exp (γ * b)) :=
        mul_le_mul (hrow w (hwmem y hy)).2 hnu (one_div_nonneg.2 (neg_pos.2 hn0).le) hR
      _ = _ := by ring
  have hhist := hx.early_scalar_incoming_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf
    hc0.le hac hκ₀ hε hεk hρ hN hH hD hpoint
  have hscalar : ∀ᵐ y ∂volume.restrict (Ioc (z : ℝ) u),
      |x.2.2 y b 1| ≤ F * y ^ (s - 1) + G * y ^ (t - 1) := by
    filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hhist,
      ae_restrict_mem measurableSet_Ioc] with y hy hym
    obtain ⟨T, hTb, _hwin, htrap, _hentry, hscale, hpre, hscalar, hk, hK⟩ := hmatch y hym
    have hh := hy T b (z.property.1.trans_lt hym.1) hTb hscale htrap
      (hrow _ (hwmem y hym)).1 hpre hscalar hk hK
    have he1 : s - 1 = -1 / p.toReal := by dsimp only [s]; ring
    have he2 : t - 1 = -1 + c / a := by dsimp only [t]; ring
    rw [he1, he2]
    exact hh
  have hb := linear_weight_power_energy z.property.1 (show (z : ℝ) ≤ u from hzu) hs ht
    (div_nonneg hR hn.le) hF hG hWi hweight hscalar hwidth
  simpa only [W, F, G, s, t, γ, ν, div_mul_eq_mul_div] using hb

end CauchyHorizon
