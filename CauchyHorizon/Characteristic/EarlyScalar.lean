import CauchyHorizon.Characteristic.InnerTransport
import CauchyHorizon.Characteristic.ScalarWave
import CauchyHorizon.Reduced.ScalarHistory

/-! Actual transverse scalar history through the early trapped region. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.early_scalar_history {M e Λ U V a c k ε κ₀ ρ N H : ℝ} {h r : ℝ → ℝ}
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
    (hc0 : 0 ≤ c) (hac : c < a) (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hH : 0 ≤ H) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ (T b : Icc 0 V), T ≤ b →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
      let m := massField e Λ x.1 x.2.1 ν hx.choose
      let K := fun v => horizonK (x.1 u v 0) (m u v) e Λ
      x.2.1 u T 0 < 0 → ρ ≤ x.1 u b 0 →
      (∀ v ≤ T, |ν u v| ≤ N * Real.exp (a * v)) →
      (∀ v ≤ b, |x.2.1 u v 1| ≤ H * Real.exp (-c * v)) →
      (∀ v ∈ Icc T b, κ₀ ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
      (∀ v ∈ Icc T b, |K v + k| ≤ ε) →
        |x.2.2 t b 1| ≤ (r 0 / ρ) * |f t| +
          (N * H / ρ) * (1 / (a - c) + 1 / (2 * κ₀ * (k - ε) + c)) *
            Real.exp ((a - c) * T) := by
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let q := 2 * κ₀ * (k - ε)
  have hq : 0 < q := mul_pos (mul_pos (by norm_num) hκ₀) (sub_pos.2 hεk)
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  filter_upwards [hx.incoming_zeta_transport hU hV hUR hp hf,
    ae_restrict_mem measurableSet_Icc] with t ht htm
  intro T b hTb
  dsimp only
  intro htrap hrb hpre hscalar hk hK
  let u := projIcc 0 U hU t
  have hn (v) : ν u v < 0 := (hg u v).2.2.1
  let m := massField e Λ x.1 x.2.1 ν hx.choose
  have hrn (v) : x.1 u v 0 ≠ 0 := hx.choose u v
  have hrcont : Continuous (fun v : Icc 0 V => x.1 u v 0) := (continuous_apply 0).comp (x.1 u).continuous
  have hKcont : Continuous (fun v => horizonK (x.1 u v 0) (m u v) e Λ) :=
    (((m u).continuous.div (hrcont.pow 2) (fun v => pow_ne_zero 2 (hrn v))).sub
      (continuous_const.div (hrcont.pow 3) (fun v => pow_ne_zero 3 (hrn v)))).sub
        ((continuous_const.mul hrcont).div_const 3)
  -- Only the nu component is used; its bound is independent of the conformal error.
  let E : C(Icc 0 V, ℝ) := ⟨fun v => x.2.1 u v 2 - 2 * horizonK (x.1 u v 0) (m u v) e Λ,
    ((continuous_apply 2).comp (x.2.1 u).continuous).sub (hKcont.const_mul 2)⟩
  have hpost (v : Icc 0 V) (hv : v ∈ Icc T b) :
      |ν u v| ≤ N * Real.exp (a * T) * Real.exp (-q * ((v : ℝ) - T)) := by
    have hb := (hx.inner_segment_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf hκ₀ hε hεk
      (d := ‖E‖) u T v hv.1 htrap
      (fun w hw => hk w ⟨hw.1, hw.2.trans hv.2⟩)
      (fun w hw => hK w ⟨hw.1, hw.2.trans hv.2⟩)
      (fun w _ => by
        change |E w| ≤ ‖E‖
        simpa only [Real.norm_eq_abs] using E.norm_coe_le_norm w)).1.2
    rw [abs_of_neg (hn v)]
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hh : |ν u T| ≤ N * Real.exp (a * T) := hpre T le_rfl
    rwa [abs_of_neg (hn T)] at hh
  have hb := scalarTransportCorrection_split_bound (hV := hV) hac (add_pos_of_pos_of_nonneg hq hc0)
    hN hH ν x.2.1 u T b hTb hpre hpost hscalar
  have hrpos : 0 < x.1 u b 0 := hρ.trans_le hrb
  have hrt : 0 < r 0 - t := sub_pos.2 (htm.2.trans_lt hUR)
  have hbound : ρ * |x.2.2 t b 1| ≤ r 0 * |f t| +
      N * H * (1 / (a - c) + 1 / (q + c)) * Real.exp ((a - c) * T) := by
    calc
      _ ≤ x.1 u b 0 * |x.2.2 t b 1| := mul_le_mul_of_nonneg_right hrb (abs_nonneg _)
      _ = |x.1 u b 0 * x.2.2 t b 1| := by rw [abs_mul, abs_of_pos hrpos]
      _ ≤ _ := by
        rw [ht b]
        apply (abs_add_le _ _).trans (add_le_add _ hb)
        rw [abs_mul, abs_of_pos hrt]
        exact mul_le_mul_of_nonneg_right (by linarith only [htm.1]) (abs_nonneg _)
  refine ((le_div_iff₀ hρ).2 (by simpa only [mul_comm ρ] using hbound)).trans_eq ?_
  dsimp only [q]
  ring

theorem IsWaveIntegral.early_scalar_history_power
    {M e Λ U V a c k ε κ₀ ρ N H D : ℝ} {h r : ℝ → ℝ}
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
    (hc0 : 0 ≤ c) (hac : c < a) (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hH : 0 ≤ H) (hD : 0 ≤ D) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ (T b : Icc 0 V), 0 < t → T ≤ b →
      t * Real.exp (a * T) ≤ D →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
      let m := massField e Λ x.1 x.2.1 ν hx.choose
      let K := fun v => horizonK (x.1 u v 0) (m u v) e Λ
      x.2.1 u T 0 < 0 → ρ ≤ x.1 u b 0 →
      (∀ v ≤ T, |ν u v| ≤ N * Real.exp (a * v)) →
      (∀ v ≤ b, |x.2.1 u v 1| ≤ H * Real.exp (-c * v)) →
      (∀ v ∈ Icc T b, κ₀ ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
      (∀ v ∈ Icc T b, |K v + k| ≤ ε) →
        |x.2.2 t b 1| ≤ (r 0 / ρ) * |f t| +
          (N * H / ρ) * (1 / (a - c) + 1 / (2 * κ₀ * (k - ε) + c)) *
            D ^ (1 - c / a) * t ^ (-1 + c / a) := by
  have ha : 0 < a := hc0.trans_lt hac
  have hq : 0 < 2 * κ₀ * (k - ε) := mul_pos (mul_pos (by norm_num) hκ₀) (sub_pos.2 hεk)
  have hcoef : 0 ≤ (N * H / ρ) * (1 / (a - c) + 1 / (2 * κ₀ * (k - ε) + c)) := by
    positivity
  filter_upwards [hx.early_scalar_history hU hV hUR hc hi hrc hr0 hφ hrd hp hf
    hc0 hac hκ₀ hε hεk hρ hN hH] with t ht
  intro T b ht0 hTb hwidth
  dsimp only
  intro htrap hrb hpre hscalar hk hK
  have hscale : Real.exp ((a - c) * T) ≤ D ^ (1 - c / a) * t ^ (-1 + c / a) := by
    have he : Real.exp (a * T) ≤ D / t :=
      (le_div_iff₀ ht0).2 (by simpa only [mul_comm t] using hwidth)
    have hh := Real.rpow_le_rpow (Real.exp_pos (a * T)).le he
      (sub_nonneg.2 ((div_le_one ha).2 hac.le))
    rw [← Real.exp_mul, Real.div_rpow hD ht0.le] at hh
    have hex : a * (T : ℝ) * (1 - c / a) = (a - c) * T := by field_simp
    rw [hex] at hh
    apply hh.trans_eq
    rw [show -1 + c / a = -(1 - c / a) by ring, Real.rpow_neg ht0.le]
    rfl
  have hhist := mul_le_mul_of_nonneg_left hscale hcoef
  exact ((ht T b hTb htrap hrb hpre hscalar hk hK).trans
    (add_le_add le_rfl hhist)).trans_eq (by ring)

theorem IsWaveIntegral.early_scalar_incoming_bound
    {M e Λ U V a c k ε κ₀ ρ N H D A : ℝ} {h r : ℝ → ℝ}
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
    (hc0 : 0 ≤ c) (hac : c < a) (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hpoint : ∀ᵐ t ∂volume.restrict (Icc 0 U), |f t| ≤ A * t ^ (-1 / p.toReal)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ (T b : Icc 0 V), 0 < t → T ≤ b →
      t * Real.exp (a * T) ≤ D →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
      let m := massField e Λ x.1 x.2.1 ν hx.choose
      let K := fun v => horizonK (x.1 u v 0) (m u v) e Λ
      x.2.1 u T 0 < 0 → ρ ≤ x.1 u b 0 →
      (∀ v ≤ T, |ν u v| ≤ N * Real.exp (a * v)) →
      (∀ v ≤ b, |x.2.1 u v 1| ≤ H * Real.exp (-c * v)) →
      (∀ v ∈ Icc T b, κ₀ ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
      (∀ v ∈ Icc T b, |K v + k| ≤ ε) →
        |x.2.2 t b 1| ≤ (r 0 * A / ρ) * t ^ (-1 / p.toReal) +
          (N * H / ρ) * (1 / (a - c) + 1 / (2 * κ₀ * (k - ε) + c)) *
            D ^ (1 - c / a) * t ^ (-1 + c / a) := by
  filter_upwards [hx.early_scalar_history_power hU hV hUR hc hi hrc hr0 hφ hrd hp hf
    hc0 hac hκ₀ hε hεk hρ hN hH hD, hpoint] with t ht hft
  intro T b ht0 hTb hwidth
  dsimp only
  intro htrap hrb hpre hscalar hk hK
  have hin := mul_le_mul_of_nonneg_left hft (div_nonneg (hU.trans hUR.le) hρ.le)
  exact ((ht T b ht0 hTb hwidth htrap hrb hpre hscalar hk hK).trans
    (add_le_add hin le_rfl)).trans_eq (by ring)

end CauchyHorizon
