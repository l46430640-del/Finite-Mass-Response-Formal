import CauchyHorizon.Reduced.WeightedScalar
import CauchyHorizon.Characteristic.OuterBootstrap

/-! Time-uniform scalar and late quadratic feedback for bounded exponential width. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_weighted_scalar {M e Λ U V a c ρ N L H A δ : ℝ} {h r : ℝ → ℝ}
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
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hδ : 0 ≤ δ)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0)
    (hν : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hout : ∀ v : Icc 0 V, Real.exp (c * v) * |h v| ≤ H)
    (hwidth : U * Real.exp (a * V) ≤ δ) :
    let E := ((H + L * (r 0 / ρ) * (A * max 1 δ)) / ρ) * Real.exp (L * N * δ / (ρ ^ 2 * (a - c)))
    (∀ u v, |x.2.1 u v 1| ≤ E * Real.exp (-c * v)) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        |x.2.2 u v 1| ≤ (r 0 / ρ) * |f u| + (N / (ρ * (a - c))) * E * Real.exp ((a - c) * v) := by
  have hin (u : Icc 0 U) : |incomingWaveCurve hU hUR hp hf (horizonPhi h r 0) u 0| ≤ r 0 := by
    rw [incomingWaveCurve_apply]
    change |r 0 - (u : ℝ)| ≤ r 0
    rw [abs_of_pos (sub_pos.2 (u.property.2.trans_lt hUR))]
    linarith only [u.property.1]
  have hhor (v : Icc 0 V) : Real.exp (c * v) *
      |x.1 ⟨0, le_rfl, hU⟩ v 0 * horizonWaveVelocity M e Λ V hc hi hrc hr0 v 1| ≤ H := by
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
    change Real.exp (c * v) * |r v * (h v / r v)| ≤ H
    have he : r v * (h v / r v) = h v := by field_simp [hr0 v]
    rw [he]
    exact hout v
  have hpow : δ ^ (1 - 1 / p.toReal) ≤ max 1 δ := by
    by_cases hd : δ ≤ 1
    · exact (Real.rpow_le_one hδ hd (by linarith only [(incoming_exponent_bounds hp).1])).trans (le_max_left _ _)
    · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hd)
        (sub_le_self _ (by positivity))).trans (le_max_right _ _)
  have hinput : Real.exp (c * V) * (∫ t in (0 : ℝ)..U, |incomingWaveVelocity hUR hp hf t 1|) ≤ A * max 1 δ := by
    have heq : (∫ t in (0 : ℝ)..U, |incomingWaveVelocity hUR hp hf t 1|) = ∫ t in (0 : ℝ)..U, |f t| := by
      simp only [intervalIntegral.integral_of_le hU]
      apply integral_congr_ae
      filter_upwards [ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
        (incomingWaveVelocity_ae hUR hp hf)] with t ht
      rw [ht]
      rfl
    rw [heq]
    exact (incoming_weighted_integral_le_lp hU hV ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp) hf hcb hwidth).trans
      (mul_le_mul hfn hpow (Real.rpow_nonneg hδ _) hA)
  have hs := hx.weighted_scalar_bound hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 hc0 hac hρ (hU.trans hUR.le)
    hN hL hH (mul_nonneg hA (zero_le_one.trans (le_max_left _ _))) hlo hin hν hlam hhor hinput hwidth
  refine ⟨hs.1, ?_⟩
  filter_upwards [hs.2, incomingWaveVelocity_ae hUR hp hf] with u hu hfEq
  intro v
  have ht := hu v
  rw [hfEq] at ht
  exact ht

set_option maxHeartbeats 800000 in
theorem exists_weighted_feedback_envelope {M e Λ a c ρ R n N L H A δ : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (hc0 : 0 < c) (hac : c < a) (hρ : 0 < ρ) (hR : 0 ≤ R) (hn : 0 < n)
    (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
      (x : WaveState U V)
      (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → c ≤ a * (1 - 1 / p.toReal) →
      (∀ u v, ρ ≤ x.1 u v 0) → (∀ u v, x.1 u v 0 ≤ R) →
      (∀ u (v : Icc 0 V), n * Real.exp (a * v) ≤ -radialNuField hV e Λ
        (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v) →
      (∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        x.1 hx.choose u v| ≤ N * Real.exp (a * v)) →
      (∀ u v, |x.2.1 u v 0| ≤ L) → (∀ v : Icc 0 V, Real.exp (c * v) * |h v| ≤ H) →
      U * Real.exp (a * V) ≤ δ → ∀ u : Icc 0 U,
        let Q := C * Real.exp (-a * V) + D * Real.exp (-(2 * c) * V)
        let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
        let v : Icc 0 V := ⟨V, hV, le_rfl⟩
        (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
          (-intervalExtension hU ν t v)) ≤ Q ∧
        Real.exp (-Q) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧
        |massField e Λ x.1 x.2.1 ν hx.choose u v - horizonMass M h V| ≤ (R * L / 2) * (Real.exp Q - 1) := by
  let α := r 0 / ρ
  let E := ((H + L * α * (A * max 1 δ)) / ρ) * Real.exp (L * N * δ / (ρ ^ 2 * (a - c)))
  let β := (N / (ρ * (a - c))) * E
  let C := (2 * R / n) * α ^ 2 * A ^ 2 * max 1 δ
  let D := (2 * R / n) * β ^ 2 * δ
  let Q : ℝ → ℝ := fun v => C * Real.exp (-a * v) + D * Real.exp (-(2 * c) * v)
  have ha : 0 < a := hc0.trans hac
  refine ⟨C, D, by dsimp only [C]; positivity, by dsimp only [D]; positivity, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb hlo hrhi hnlo hnhi hlam hout hwidth u
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
  have hα : 0 ≤ α := div_nonneg (hU.trans hUR.le) hρ.le
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hs := hx.horizon_weighted_scalar hU hV hUR hc hi hrc hr0 hφ hrd hp hf hA hfn hc0.le hac hcb
    hρ hN hL hH hδ hlo hnhi hlam hout hwidth
  let q : ℝ → ℝ := fun t => intervalExtension hU x.1 t v 0 / (-intervalExtension hU ν t v)
  have hq (t : ℝ) : q t ≤ R / n * Real.exp (-a * V) := by
    let b := projIcc 0 U hU t
    calc
      _ ≤ R / (n * Real.exp (a * V)) := div_le_div₀ hR (hrhi b v) (mul_pos hn (Real.exp_pos _)) (hnlo b v)
      _ = R / n * Real.exp (-a * V) := by
        rw [div_mul_eq_div_div, div_eq_mul_inv, ← Real.exp_neg, neg_mul]
  have hk := hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
  have hqi : IntervalIntegrable (fun t => q t * (x.2.2 t v 1) ^ 2) volume 0 U := by
    simpa only [q, div_mul_eq_mul_div] using hk.1
  have hψ : ∀ᵐ t ∂volume.restrict (Icc 0 U), |x.2.2 t v 1| ≤ α * |f t| + β * Real.exp ((a - c) * V) := by
    filter_upwards [hs.2] with t ht
    exact ht v
  have he := weighted_quadratic_integral_le_lp hU ((by norm_num : (2 : ℝ≥0∞) ≤ 4).trans hp) hf hA hfn
    hα (mul_nonneg hβ (Real.exp_pos _).le) (by positivity : 0 ≤ R / n * Real.exp (-a * V))
    hqi (Filter.Eventually.of_forall hq) hψ u
  have huδ : (u : ℝ) ≤ δ := u.property.2.trans
    ((le_mul_of_one_le_right hU (Real.one_le_exp_iff.2 (mul_nonneg ha.le hV))).trans hwidth)
  have hpow : (u : ℝ) ^ (1 - 2 / p.toReal) ≤ max 1 δ := by
    have hb0 : 0 ≤ 1 - 2 / p.toReal := by linarith only [(incoming_exponent_bounds hp).2]
    apply (Real.rpow_le_rpow u.property.1 huδ hb0).trans
    by_cases hd : δ ≤ 1
    · exact (Real.rpow_le_one hδ hd hb0).trans (le_max_left _ _)
    · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hd)
        (sub_le_self _ (by positivity))).trans (le_max_right _ _)
  have hw : (u : ℝ) * Real.exp (a * V) ≤ δ :=
    (mul_le_mul_of_nonneg_right u.property.2 (Real.exp_pos _).le).trans hwidth
  have hexp : Real.exp (-a * V) * Real.exp ((a - c) * V) ^ 2 = Real.exp ((a - 2 * c) * V) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have htime : (u : ℝ) * Real.exp ((a - 2 * c) * V) ≤ δ * Real.exp (-(2 * c) * V) := by
    have hh := mul_le_mul_of_nonneg_right hw (Real.exp_pos (-(2 * c) * V)).le
    rw [mul_assoc, ← Real.exp_add] at hh
    have he : (a - 2 * c) * V = a * V + -(2 * c) * V := by ring
    simpa only [he] using hh
  have henergy : (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU ν t v)) ≤ Q V := by
    simp only [q, div_mul_eq_mul_div] at he
    have he' : (R * Real.exp (-a * V)) *
        (2 * α ^ 2 * A ^ 2 * (u : ℝ) ^ (1 - 2 / p.toReal) + 2 * (β * Real.exp ((a - c) * V)) ^ 2 * u) / n =
        (2 * R / n) * (α ^ 2 * A ^ 2 * Real.exp (-a * V) * (u : ℝ) ^ (1 - 2 / p.toReal) +
          β ^ 2 * ((u : ℝ) * Real.exp ((a - 2 * c) * V))) := by
      calc
        _ = (2 * R / n) * (α ^ 2 * A ^ 2 * Real.exp (-a * V) * (u : ℝ) ^ (1 - 2 / p.toReal) +
          β ^ 2 * u * (Real.exp (-a * V) * Real.exp ((a - c) * V) ^ 2)) := by ring
        _ = _ := by rw [hexp]; ring
    rw [he'] at he
    apply he.trans
    have hh := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ α ^ 2 * A ^ 2 * Real.exp (-a * V)))
      (mul_le_mul_of_nonneg_left htime (sq_nonneg β))) (by positivity : 0 ≤ 2 * R / n)
    apply hh.trans_eq
    dsimp only [Q, C, D]
    ring
  exact ⟨henergy, hx.mass_constraint_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf hR hL hrhi hlam u v henergy⟩

theorem exists_late_weighted_feedback {M e Λ a c ρ R n N L H A δ η : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (hc0 : 0 < c) (hac : c < a) (hρ : 0 < ρ) (hR : 0 ≤ R) (hn : 0 < n)
    (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hη : 0 < η) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
      (x : WaveState U V)
      (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → c ≤ a * (1 - 1 / p.toReal) →
      (∀ u v, ρ ≤ x.1 u v 0) → (∀ u v, x.1 u v 0 ≤ R) →
      (∀ u (v : Icc 0 V), n * Real.exp (a * v) ≤ -radialNuField hV e Λ
        (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v) →
      (∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        x.1 hx.choose u v| ≤ N * Real.exp (a * v)) →
      (∀ u v, |x.2.1 u v 0| ≤ L) → (∀ v : Icc 0 V, Real.exp (c * v) * |h v| ≤ H) →
      U * Real.exp (a * V) ≤ δ → T ≤ V → ∀ u : Icc 0 U,
        let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
        let v : Icc 0 V := ⟨V, hV, le_rfl⟩
        (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
          (-intervalExtension hU ν t v)) ≤ η ∧
        Real.exp (-η) ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧
        |massField e Λ x.1 x.2.1 ν hx.choose u v - horizonMass M h V| ≤ (R * L / 2) * (Real.exp η - 1) := by
  obtain ⟨C, D, _hC, _hD, hbound⟩ := exists_weighted_feedback_envelope hc hi hrc hr0 hφ hrd
    hc0 hac hρ hR hn hN hL hH hA hδ
  let Q : ℝ → ℝ := fun v => C * Real.exp (-a * v) + D * Real.exp (-(2 * c) * v)
  have hlim : Tendsto Q atTop (𝓝 0) := by
    have h1 := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos (hc0.trans hac)))).const_mul C
    have h2 := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (by linarith only [hc0] : -(2 * c) < 0))).const_mul D
    simpa only [Q, Function.comp_def, id_eq, mul_zero, add_zero] using h1.add h2
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hlim.eventually_lt_const hη)
  refine ⟨max 0 T₀, le_max_left _ _, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb hlo hrhi hnlo hnhi hlam hout hwidth hTV u
  obtain ⟨he, hk, hm⟩ := hbound U V hU hV hUR p hp f hf x hx hfn hcb hlo hrhi hnlo hnhi hlam hout hwidth u
  have hQ : Q V ≤ η := (hT₀ V ((le_max_right _ _).trans hTV)).le
  exact ⟨he.trans hQ, (Real.exp_le_exp.2 (neg_le_neg hQ)).trans hk,
    hm.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_le_exp.2 hQ) 1)
      (div_nonneg (mul_nonneg hR hL) (by norm_num)))⟩

end CauchyHorizon
