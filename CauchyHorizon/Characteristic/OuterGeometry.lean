import CauchyHorizon.Characteristic.MassConstraint
import CauchyHorizon.Characteristic.OuterScalar

/-! Quadratic lapse and mass feedback on the outer region. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem weighted_quadratic_integral_le_lp {U A α C K : ℝ} (hU : 0 ≤ U)
    {p : ℝ≥0∞} (hp : 2 ≤ p) {f q ψ : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hA : 0 ≤ A) (hfn : (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A)
    (hα : 0 ≤ α) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hi : IntervalIntegrable (fun t => q t * ψ t ^ 2) volume 0 U)
    (hq : ∀ᵐ t ∂volume.restrict (Icc 0 U), q t ≤ K)
    (hψ : ∀ᵐ t ∂volume.restrict (Icc 0 U), |ψ t| ≤ α * |f t| + C)
    (u : Icc 0 U) :
    (∫ t in (0 : ℝ)..u, q t * ψ t ^ 2) ≤
      K * (2 * α ^ 2 * A ^ 2 * (u : ℝ) ^ (1 - 2 / p.toReal) + 2 * C ^ 2 * u) := by
  have hf2 := hf.mono_exponent hp
  have hfi : IntervalIntegrable (fun t => f t ^ 2) volume 0 U := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    change Integrable (fun t => f t ^ 2) (volume.restrict (Icc 0 U))
    simpa only [pow_two] using (hf2.mul' hf2 (r := 1)).integrable le_rfl
  have hsub : uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le u.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl u.property.2
  have hb : ∀ᵐ t ∂volume.restrict (Icc 0 U),
      q t * ψ t ^ 2 ≤ K * (2 * α ^ 2 * f t ^ 2 + 2 * C ^ 2) := by
    filter_upwards [hq, hψ] with t hqt hψt
    have hs := (sq_le_sq₀ (abs_nonneg (ψ t)) (by positivity)).2 hψt
    rw [sq_abs] at hs
    have ht : ψ t ^ 2 ≤ 2 * α ^ 2 * f t ^ 2 + 2 * C ^ 2 := by
      nlinarith only [hs, sq_nonneg (α * |f t| - C), sq_abs (f t)]
    exact (mul_le_mul_of_nonneg_right hqt (sq_nonneg _)).trans (mul_le_mul_of_nonneg_left ht hK)
  have hb' := ae_mono (Measure.restrict_mono (Icc_subset_Icc (le_rfl : (0 : ℝ) ≤ 0) u.property.2) le_rfl) hb
  have hh := intervalIntegral.integral_mono_ae_restrict u.property.1 (hi.mono_set hsub)
    ((((hfi.mono_set hsub).const_mul (2 * α ^ 2)).add intervalIntegrable_const).const_mul K) hb'
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hfi.mono_set hsub).const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hh
  have hj := (incoming_integral_sq_le_lp_power hp hf u).trans
    (mul_le_mul_of_nonneg_right ((sq_le_sq₀ ENNReal.toReal_nonneg hA).2 hfn) (Real.rpow_nonneg u.property.1 _))
  have hk := mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ 2 * α ^ 2)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hK
  nlinarith only [hk]

theorem IsWaveIntegral.horizon_outer_feedback {M e Λ U V a c ρ R n N L H A δ : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hA : 0 ≤ A) (hfn : (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A)
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hc0 : 0 ≤ c) (hac : c < a) (hcb : c ≤ a * (1 - 1 / p.toReal))
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hn : 0 < n) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hrhi : ∀ u v, x.1 u v 0 ≤ R)
    (hνlo : ∀ (u : Icc 0 U) (v : Icc 0 V), n * Real.exp (a * v) ≤
      -radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v)
    (hνhi : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hout : ∀ v : Icc 0 V, Real.exp (c * v) * |h v| ≤ H)
    (hwidth : U * Real.exp (a * V) ≤ δ) (hsmall : L * N * δ / (ρ ^ 2 * (a - c)) ≤ 1 / 2)
    (u : Icc 0 U) (v : Icc 0 V) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let E := 2 * (H + L * (r 0 / ρ) * (A * δ ^ (1 - 1 / p.toReal))) / ρ
    let B := (2 * R / n) * ((r 0 / ρ) ^ 2 * A ^ 2 * Real.exp (-a * v) * (u : ℝ) ^ (1 - 2 / p.toReal) +
      (N / (ρ * (a - c)) * E) ^ 2 * u * Real.exp ((a - 2 * c) * v))
    (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU ν t v)) ≤ B ∧
    Real.exp (-B) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧
    |massField e Λ x.1 x.2.1 ν hx.choose u v - horizonMass M h v| ≤ (R * L / 2) * (Real.exp B - 1) := by
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let E := 2 * (H + L * (r 0 / ρ) * (A * δ ^ (1 - 1 / p.toReal))) / ρ
  let β := N / (ρ * (a - c)) * E
  let B := (2 * R / n) * ((r 0 / ρ) ^ 2 * A ^ 2 * Real.exp (-a * v) * (u : ℝ) ^ (1 - 2 / p.toReal) +
    β ^ 2 * u * Real.exp ((a - 2 * c) * v))
  have hrp : 0 ≤ r 0 := hU.trans hUR.le
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hβ : 0 ≤ β := mul_nonneg (div_nonneg hN (mul_nonneg hρ.le (sub_pos.2 hac).le)) hE
  have hs := hx.horizon_outer_scalar hU hV hUR hc hi hrc hr0 hφ hrd hp hf hA hfn
    hc0 hac hcb hρ hN hL hH hδ hlo hνhi hlam hout hwidth hsmall
  let q := fun t => intervalExtension hU x.1 t v 0 / (-intervalExtension hU ν t v)
  have hq (t : ℝ) : q t ≤ R / n * Real.exp (-a * v) := by
    let b := projIcc 0 U hU t
    have hnp : 0 < n * Real.exp (a * v) := mul_pos hn (Real.exp_pos _)
    calc
      _ ≤ R / (n * Real.exp (a * v)) :=
        div_le_div₀ hR (hrhi b v) hnp (hνlo b v)
      _ = R / n * Real.exp (-a * v) := by
        rw [div_mul_eq_div_div, div_eq_mul_inv, ← Real.exp_neg, neg_mul]
  have hk := hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
  have hqi : IntervalIntegrable (fun t => q t * (x.2.2 t v 1) ^ 2) volume 0 U := by
    simpa only [q, div_mul_eq_mul_div] using hk.1
  have hψ : ∀ᵐ t ∂volume.restrict (Icc 0 U), |x.2.2 t v 1| ≤ (r 0 / ρ) * |f t| + β * Real.exp ((a - c) * v) := by
    filter_upwards [hs.2] with t ht
    exact ht v
  have he := weighted_quadratic_integral_le_lp hU ((by norm_num : (2 : ℝ≥0∞) ≤ 4).trans hp) hf hA hfn
    (div_nonneg hrp hρ.le) (mul_nonneg hβ (Real.exp_pos _).le)
    (mul_nonneg (div_nonneg hR hn.le) (Real.exp_pos _).le) hqi (Filter.Eventually.of_forall hq) hψ u
  have hexp : Real.exp (-a * v) * Real.exp ((a - c) * v) ^ 2 = Real.exp ((a - 2 * c) * v) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have henergy : (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU ν t v)) ≤ B := by
    simp only [q, div_mul_eq_mul_div] at he
    apply he.trans_eq
    dsimp only [B]
    calc
      _ = (2 * R / n) * ((r 0 / ρ) ^ 2 * A ^ 2 * Real.exp (-a * v) * (u : ℝ) ^ (1 - 2 / p.toReal) +
        β ^ 2 * u * (Real.exp (-a * v) * Real.exp ((a - c) * v) ^ 2)) := by ring
      _ = _ := by rw [hexp]
  exact ⟨henergy, hx.mass_constraint_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf hR hL hrhi hlam u v henergy⟩

end CauchyHorizon
