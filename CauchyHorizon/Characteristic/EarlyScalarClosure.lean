import CauchyHorizon.Characteristic.ArrivalScalar
import CauchyHorizon.Characteristic.EarlyInnerFeedback
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A uniform strict scalar improvement under the remaining geometric bootstrap. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

set_option maxHeartbeats 800000 in
theorem exists_early_scalar_improvement {M e Λ a c k ε d κ₀ ρ R n N E D A H L l β : ℝ}
    {h r : ℝ → ℝ} (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) (hrinit : 0 < r 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p)
    (hc0 : 0 ≤ c) (hac : c < a) (hca : c ≤ a * (1 - 1 / p.toReal))
    (hk : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k)
    (hρ : 0 < ρ) (hn : 0 < n) (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hH : 0 ≤ H) (hL : 0 ≤ L) (hl : 0 < l)
    (hℓ : c < 2 * (k - ε) - d)
    (hη : 0 < 2 * c - max 0 (2 * (k + ε) + d - 2 * c) * β)
    (hsmall : Real.exp 1 * L ^ 2 /
      (ρ ^ 2 * (2 * (k - ε) - d - c) * (2 * κ₀ * (k - ε) + c)) ≤ 1 / 4) :
    ∃ He T₀ : ℝ, 0 < He ∧ E < He ∧ 0 ≤ T₀ ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ᵐ t ∂volume.restrict (Icc 0 U), |f t| ≤ A * t ^ (-1 / p.toReal)) →
        ∀ (z u : Icc 0 U) (_hz : 0 < (z : ℝ)) (hzu : z ≤ u) (b : Icc 0 V)
          (T : C(Icc (z : ℝ) u, Icc 0 V)),
          let τ := fun t => T (projIcc (z : ℝ) u hzu t)
          let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let K := fun w v => horizonK (x.1 w v 0) (massField e Λ x.1 x.2.1 ν hx.choose w v) e Λ
          τ z = b →
          (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
            (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) →
          (∀ w ∈ Icc z u, ρ ≤ x.1 w b 0) →
          (∀ t ∈ Icc (z : ℝ) u,
            let w := projIcc 0 U hU t
            T₀ ≤ τ t ∧ τ t ≤ b ∧ (b : ℝ) ≤ (1 + β) * τ t ∧
              l ≤ -x.2.1 w (τ t) 0 ∧ -x.2.1 w (τ t) 0 ≤ L ∧ x.1 w (τ t) 0 ≤ R ∧
              n ≤ t * (-ν w (τ t)) ∧ t * Real.exp (a * τ t) ≤ D ∧
              (∀ v ≤ τ t, |ν w v| ≤ N * Real.exp (a * v)) ∧
              (∀ v ≤ τ t, |x.2.1 w v 1| ≤ E * Real.exp (-c * v)) ∧
              (∀ v ∈ Icc (τ t) b, |x.2.1 w v 1| ≤ He * Real.exp (-c * v)) ∧
              (∀ v ∈ Icc (τ t) b, κ₀ ≤ -Real.exp (x.1 w v 2) / (4 * ν w v)) ∧
              (∀ v ∈ Icc (τ t) b, |K w v + k| ≤ ε) ∧
              (∀ v ∈ Icc (τ t) b, |x.2.1 w v 2 - 2 * K w v| ≤ d)) →
          Real.exp (c * b) * |x.1 z b 0 * x.2.1 z b 1| ≤ H →
            Real.exp (c * b) * |x.2.1 u b 1| ≤ He / 2 := by
  let q := 2 * κ₀ * (k - ε)
  let ℓ := 2 * (k - ε) - d
  let η := 2 * c - max 0 (2 * (k + ε) + d - 2 * c) * β
  have hq : 0 < q := mul_pos (mul_pos (by norm_num) hk) (sub_pos.2 hεk)
  have hqc : 0 < q + c := add_pos_of_pos_of_nonneg hq hc0
  have hs : 0 < ℓ - c := sub_pos.2 hℓ
  let J := (r 0 * A * D ^ (1 - 1 / p.toReal) + N * E * D / (a - c)) / n
  let C := Real.exp 1 * L ^ 2 / (ρ ^ 2 * (ℓ - c))
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let He := 4 * (E + H / ρ + C * J + 1)
  have hHe : 0 < He := by dsimp only [He]; positivity
  have hEHe : E < He := by dsimp only [He]; nlinarith only [hE, div_nonneg hH hρ.le, mul_nonneg hC hJ]
  have hforce : H / ρ + C * J ≤ He / 4 := by dsimp only [He]; linarith only [hE]
  have hsmall' : C / (q + c) ≤ 1 / 4 := by
    convert hsmall using 1
    dsimp only [C, ℓ, q]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  -- Select the amplitude before the time that makes the actual inner flux small.
  have hlim : Tendsto (fun t : ℝ => (R * He ^ 2 / l) * β * t * Real.exp (-η * t)) atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => ((R * He ^ 2 / l) * β) * (t * Real.exp (-η * t))) atTop (𝓝 0) := by
      simpa only [Real.rpow_one, mul_zero] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 η hη).const_mul ((R * He ^ 2 / l) * β)
    convert hh using 1
    funext t
    ring
  obtain ⟨T₀, hlate⟩ := eventually_atTop.1 (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨He, max 0 T₀, hHe, hEHe, le_max_left _ _, ?_⟩
  intro U V hU hV hUR f hf x hx hpoint z u hz hzu b T
  dsimp only
  intro hτz hder hr hhist hθ
  let τ := fun t => T (projIcc (z : ℝ) u hzu t)
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hν (w v) : ν w v < 0 := (hg w v).2.2.1
  have hentry (t) (ht : t ∈ Icc (z : ℝ) u) :
      -L ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧ x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0 := by
    have hb := hhist t ht
    constructor <;> linarith only [hb.2.2.2.1, hb.2.2.2.2.1, hl]
  have htransport (t) (ht : t ∈ Icc (z : ℝ) u) :
      (∀ v ∈ Icc (τ t) b, |ν (projIcc 0 U hU t) v| ≤
        (-ν (projIcc 0 U hU t) (τ t)) * Real.exp (-q * ((v : ℝ) - τ t))) ∧
      |x.2.1 (projIcc 0 U hU t) b 0| ≤
        (Real.exp 1 * L) * Real.exp (-ℓ * ((b : ℝ) - τ t)) := by
    obtain ⟨hTlate, hTb, hwindow, hlower, hupper, hRentry, _hn, _hwidth, _hpre, _hwpre,
      hscalar, hkappa, hK, herr⟩ := hhist t ht
    let w := projIcc 0 U hU t
    have ha : x.2.1 w (τ t) 0 < 0 := (hentry t ht).2
    have hJb := (hx.early_inner_flux_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf
      hk hε hεk hHe.le hl w (τ t) b hTb hlower hRentry hwindow hscalar hkappa hK herr).2
    have hJsmall : (∫ v in (τ t : ℝ)..b, intervalExtension hV (x.1 w) v 0 *
        (intervalExtension hV (x.2.1 w) v 1) ^ 2 / (-intervalExtension hV (x.2.1 w) v 0)) ≤ 1 :=
      hJb.trans (hlate (τ t) ((le_max_right _ _).trans hTlate)).le
    refine ⟨?_, ?_⟩
    · intro v hv
      have hsub : Icc (τ t) v ⊆ Icc (τ t) b := Icc_subset_Icc le_rfl hv.2
      have hb := (hx.inner_segment_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf
        hk hε hεk w (τ t) v hv.1 ha (fun y hy => hkappa y (hsub hy))
        (fun y hy => hK y (hsub hy)) (fun y hy => herr y (hsub hy))).1.2
      rw [abs_of_neg (hν _ _)]
      exact hb
    · have hb := (hx.inner_segment_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf
        hk hε hεk w (τ t) b hTb ha hkappa hK herr).2.2.2
      have hlb := (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf w (τ t) b hTb ha).1
      rw [abs_of_neg hlb]
      calc
        _ ≤ _ := hb
        _ ≤ L * Real.exp (-ℓ * ((b : ℝ) - τ t) + 1) :=
          mul_le_mul hupper (Real.exp_le_exp.2 (add_le_add le_rfl hJsmall)) (Real.exp_pos _).le hL
        _ = _ := by rw [Real.exp_add]; ring
  have hζ : ∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1| ≤
        (-ν (projIcc 0 U hU t) (τ t)) * Real.exp (-c * τ t) * (J + He / (q + c)) := by
    filter_upwards [hx.entry_normalized_zeta hU hV hUR hp hf hc0 hac hqc hn hN hE hHe.le hA hca hpoint] with t ht
    intro htm
    obtain ⟨_hTlate, hTb, _hwindow, _hlower, _hupper, _hRentry, hnT, hwidth, hpre, hwpre,
      hscalar, _hkappa, _hK, _herr⟩ := hhist t htm
    exact ht (τ t) b (hz.trans_le htm.1) hTb hwidth hnT hpre (htransport t htm).1 hwpre hscalar
  have hb := hx.arrival_scalar_feedback hU hV hUR hp hf hℓ hρ
    (mul_nonneg (Real.exp_pos 1).le hL) hL (add_nonneg hJ (div_nonneg hHe.le hqc.le))
    z u hzu b T hτz (fun t _ => hν _ _) hentry hder hr (fun t ht => (htransport t ht).2) hζ hθ
  have hcoefficient := mul_le_mul_of_nonneg_right hsmall' hHe.le
  apply hb.trans
  calc
    _ = H / ρ + C * J + (C / (q + c)) * He := by
      dsimp only [C]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ He / 2 := by linarith only [hforce, hcoefficient]

end CauchyHorizon
