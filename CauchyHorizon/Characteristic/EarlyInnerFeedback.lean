import CauchyHorizon.Characteristic.InnerTransport

/-! Explicit radiation and mass margins on actual early trapped segments. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {M e Λ U V : ℝ} {h r : ℝ → ℝ}
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

include hφ hrd hx

set_option maxHeartbeats 600000 in
theorem IsWaveIntegral.early_inner_flux_bound {k ε d κ₀ R H c β l : ℝ}
    (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k) (hH : 0 ≤ H) (hl : 0 < l)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (hlam : l ≤ -x.2.1 u a 0)
    (hRa : x.1 u a 0 ≤ R) (hwindow : (b : ℝ) ≤ (1 + β) * a)
    (hscalar : ∀ w ∈ Icc a b, |x.2.1 u w 1| ≤ H * Real.exp (-c * w)) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let K := fun w => horizonK (x.1 u w 0) (massField e Λ x.1 x.2.1 N hx.choose u w) e Λ
    let η := 2 * c - max 0 (2 * (k + ε) + d - 2 * c) * β
    let J := ∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)
    (∀ w ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) →
    (∀ w ∈ Icc a b, |K w + k| ≤ ε) →
    (∀ w ∈ Icc a b, |x.2.1 u w 2 - 2 * K w| ≤ d) →
      0 ≤ J ∧ J ≤ (R * H ^ 2 / l) * β * a * Real.exp (-η * a) := by
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let K := fun w => horizonK (x.1 u w 0) (massField e Λ x.1 x.2.1 N hx.choose u w) e Λ
  let L := 2 * (k + ε) + d
  let η := 2 * c - max 0 (L - 2 * c) * β
  let J := fun t => intervalExtension hV (x.1 u) t 0 *
    (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)
  dsimp only
  intro hk hK herr
  have ha : x.2.1 u a 0 < 0 := by linarith only [hl, hlam]
  have hR : 0 ≤ R := ((hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a).2.1.le).trans hRa
  obtain ⟨hJi, hJ0, _hq, _hqp, _hqm, _hlid⟩ := hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha
  have hvel (w : Icc 0 V) (hw : w ∈ Icc a b) :
      l * Real.exp (-L * ((w : ℝ) - a)) ≤ -x.2.1 u w 0 := by
    have hsub : Icc a w ⊆ Icc a b := Icc_subset_Icc le_rfl hw.2
    have hh := (hx.inner_segment_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf hκ₀ hε hεk
      u a w hw.1 ha (fun z hz => hk z (hsub hz)) (fun z hz => hK z (hsub hz))
      (fun z hz => herr z (hsub hz))).2.2.1
    exact (mul_le_mul_of_nonneg_right hlam (Real.exp_pos _).le).trans hh
  have hb (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) : J t ≤ (R * H ^ 2 / l) * Real.exp (-η * a) := by
    have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
    let w : Icc 0 V := ⟨t, htV⟩
    have hrad : x.1 u w 0 ≤ R :=
      (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a w ht.1 ha).2.trans hRa
    have hsq := (sq_le_sq₀ (abs_nonneg (x.2.1 u w 1)) (mul_nonneg hH (Real.exp_pos _).le)).2 (hscalar w ht)
    rw [sq_abs, mul_pow, pow_two (Real.exp _), ← Real.exp_add,
      show -c * (w : ℝ) + -c * w = -(2 * c) * w by ring] at hsq
    have hnum : x.1 u w 0 * (x.2.1 u w 1) ^ 2 ≤ R * H ^ 2 * Real.exp (-(2 * c) * w) := by
      simpa only [mul_assoc] using mul_le_mul hrad hsq (sq_nonneg _) hR
    have hquot := div_le_div₀ (by positivity : 0 ≤ R * H ^ 2 * Real.exp (-(2 * c) * w))
      hnum (mul_pos hl (Real.exp_pos _)) (hvel w ht)
    have hid : (R * H ^ 2 * Real.exp (-(2 * c) * w)) / (l * Real.exp (-L * ((w : ℝ) - a))) =
        (R * H ^ 2 / l) * Real.exp (-(2 * c) * a + (L - 2 * c) * ((w : ℝ) - a)) := by
      calc
        _ = (R * H ^ 2 / l) * (Real.exp (-(2 * c) * w) / Real.exp (-L * ((w : ℝ) - a))) := by ring
        _ = _ := by rw [← Real.exp_sub]; congr 2; ring
    rw [hid] at hquot
    have htw : (w : ℝ) - a ≤ β * a := by dsimp only [w]; nlinarith only [ht.2, hwindow]
    have hpow : -(2 * c) * a + (L - 2 * c) * ((w : ℝ) - a) ≤ -η * a := by
      have h1 := mul_le_mul_of_nonneg_right (le_max_right (0 : ℝ) (L - 2 * c)) (sub_nonneg.2 ht.1)
      have h2 := mul_le_mul_of_nonneg_left htw (le_max_left (0 : ℝ) (L - 2 * c))
      dsimp only [η]
      nlinarith only [h1, h2]
    have hh := hquot.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hpow) (by positivity))
    simpa only [J, intervalExtension_apply, projIcc_of_mem hV htV, w] using hh
  have hbound := intervalIntegral.integral_mono_on (μ := volume) (show (a : ℝ) ≤ b from hab) hJi
    (g := fun _ => (R * H ^ 2 / l) * Real.exp (-η * a)) intervalIntegrable_const hb
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  have hlength : (b : ℝ) - a ≤ β * a := by nlinarith only [hwindow]
  have hfinal := hbound.trans (mul_le_mul_of_nonneg_right hlength (by positivity))
  exact ⟨hJ0, hfinal.trans_eq (by ring)⟩

theorem IsWaveIntegral.trapped_mass_increment_bound {κ₀ R H c : ℝ}
    (hκ₀ : 0 < κ₀) (hH : 0 ≤ H) (hc0 : 0 ≤ c)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0)
    (hRa : x.1 u a 0 ≤ R)
    (hscalar : ∀ w ∈ Icc a b, |x.2.1 u w 1| ≤ H * Real.exp (-c * w)) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    (∀ w ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) →
      0 ≤ m u b - m u a ∧ m u b - m u a ≤
        (R ^ 2 * H ^ 2 / (2 * κ₀)) * ((b : ℝ) - a) * Real.exp (-(2 * c) * a) := by
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField e Λ x.1 x.2.1 N hx.choose
  let κ := fun t => -Real.exp (intervalExtension hV (x.1 u) t 2) / (4 * intervalExtension hV (N u) t)
  let P := fun t => (intervalExtension hV (x.1 u) t 0 * intervalExtension hV (x.2.1 u) t 1) ^ 2 / (2 * κ t)
  dsimp only
  intro hk
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hR : 0 ≤ R := (hg u a).2.1.le.trans hRa
  have hn (t : ℝ) : intervalExtension hV (N u) t ≠ 0 := (hg u (projIcc 0 V hV t)).2.2.1.ne
  have hkp (t : ℝ) : 0 < κ t := (hg u (projIcc 0 V hV t)).2.2.2.1
  have hPc : Continuous P := by unfold P κ; fun_prop (disch := aesop)
  have hsub : Icc (a : ℝ) b ⊆ Icc 0 V := fun _ ht => ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
  have hd (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) : HasDerivAt (intervalExtension hV (m u)) (P t) t := by
    have htV := hsub (Ioo_subset_Icc_self ht)
    have hh := hx.outgoing_mass_derivative hU hV hUR hc hi hrc hr0 hφ hrd hp hf u ⟨t, htV⟩
    have hh' : HasDerivWithinAt (intervalExtension hV (m u)) (P t) (Icc 0 V) t := by
      simpa only [P, κ, intervalExtension_apply, projIcc_of_mem hV htV] using hh
    exact hh'.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (a : ℝ) ≤ b from hab)
    (intervalExtension hV (m u)).continuous.continuousOn hd (hPc.intervalIntegrable (a : ℝ) b)
  simp only [intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property] at hftc
  have hbound (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) :
      P t ≤ (R ^ 2 * H ^ 2 / (2 * κ₀)) * Real.exp (-(2 * c) * a) := by
    let w : Icc 0 V := ⟨t, hsub ht⟩
    have hrad := (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a w ht.1 ha).2.trans hRa
    have hr2 := (sq_le_sq₀ (hg u w).2.1.le hR).2 hrad
    have hs := (hscalar w ht).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.2 hc0))) hH)
    have hs2 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hH (Real.exp_pos _).le)).2 hs
    rw [sq_abs, mul_pow, pow_two (Real.exp _), ← Real.exp_add,
      show -c * (a : ℝ) + -c * a = -(2 * c) * a by ring] at hs2
    have hnum : (x.1 u w 0 * x.2.1 u w 1) ^ 2 ≤ R ^ 2 * H ^ 2 * Real.exp (-(2 * c) * a) := by
      simpa only [mul_pow, mul_assoc] using mul_le_mul hr2 hs2 (sq_nonneg _) (sq_nonneg R)
    have hquot := div_le_div₀ (by positivity : 0 ≤ R ^ 2 * H ^ 2 * Real.exp (-(2 * c) * a)) hnum
      (mul_pos (by norm_num : (0 : ℝ) < 2) hκ₀) (mul_le_mul_of_nonneg_left (hk w ht) (by norm_num))
    simp only [P, κ, intervalExtension_apply, projIcc_of_mem hV (hsub ht)]
    exact hquot.trans_eq (by ring)
  have hI := intervalIntegral.integral_mono_on (μ := volume) (show (a : ℝ) ≤ b from hab)
    (hPc.intervalIntegrable _ _) (g := fun _ => (R ^ 2 * H ^ 2 / (2 * κ₀)) * Real.exp (-(2 * c) * a))
    intervalIntegrable_const hbound
  rw [hftc, intervalIntegral.integral_const, smul_eq_mul] at hI
  refine ⟨sub_nonneg.2 (hx.mass_monotone hU hV hUR hc hi hrc hr0 hφ hrd hp hf u hab), ?_⟩
  exact hI.trans_eq (by ring)

end CauchyHorizon
