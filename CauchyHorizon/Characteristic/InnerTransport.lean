import CauchyHorizon.Characteristic.TrappedTransport
import CauchyHorizon.Characteristic.MassFlux
import CauchyHorizon.Reduced.MassRadialRate

/-! Actual inner transport bounds under the finite-segment geometric bootstrap. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

set_option maxHeartbeats 600000 in
theorem IsWaveIntegral.inner_segment_transport {M e Λ U V k ε d κ₀ : ℝ} {h r : ℝ → ℝ}
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
    (_hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    let K := fun w => horizonK (x.1 u w 0) (m u w) e Λ
    let Δ := (b : ℝ) - a
    let J := ∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)
    (∀ w ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) →
    (∀ w ∈ Icc a b, |K w + k| ≤ ε) →
    (∀ w ∈ Icc a b, |x.2.1 u w 2 - 2 * K w| ≤ d) →
      ((-N u a) * Real.exp (-(2 * (k + ε)) * Δ) ≤ -N u b ∧
        -N u b ≤ (-N u a) * Real.exp (-(2 * κ₀ * (k - ε)) * Δ)) ∧
      (-(2 * (k + ε) + d) * Δ ≤ x.1 u b 2 - x.1 u a 2 ∧
        x.1 u b 2 - x.1 u a 2 ≤ -(2 * (k - ε) - d) * Δ) ∧
      ((-x.2.1 u a 0) * Real.exp (-(2 * (k + ε) + d) * Δ) ≤ -x.2.1 u b 0 ∧
        -x.2.1 u b 0 ≤ (-x.2.1 u a 0) * Real.exp (-(2 * (k - ε) - d) * Δ + J)) := by
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField e Λ x.1 x.2.1 N hx.choose
  let K := fun w => horizonK (x.1 u w 0) (m u w) e Λ
  let G := fun t => 2 * (-Real.exp (intervalExtension hV (x.1 u) t 2) /
    (4 * intervalExtension hV (N u) t)) *
    horizonK (intervalExtension hV (x.1 u) t 0) (intervalExtension hV (m u) t) e Λ
  let E := fun t => intervalExtension hV (x.1 u) t 2
  let W := fun t => intervalExtension hV (x.2.1 u) t 2
  let Δ := (b : ℝ) - a
  dsimp only
  intro hk hK herr
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hn (w v) : N w v < 0 := (hg w v).2.2.1
  have hrn (t : ℝ) : intervalExtension hV (x.1 u) t 0 ≠ 0 := hx.choose u (projIcc 0 V hV t)
  have hnn (t : ℝ) : intervalExtension hV (N u) t ≠ 0 := (hn u (projIcc 0 V hV t)).ne
  have hGc : Continuous G := by unfold G horizonK; fun_prop (disch := aesop)
  have hEc : Continuous E := by fun_prop
  have hWc : Continuous W := by fun_prop
  have hsub : Icc (a : ℝ) b ⊆ Icc 0 V := fun _ ht => ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
  have hGb (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) :
      -(2 * (k + ε)) ≤ G t ∧ G t ≤ -(2 * κ₀ * (k - ε)) := by
    let w : Icc 0 V := ⟨t, hsub ht⟩
    let κ := -Real.exp (x.1 u w 2) / (4 * N u w)
    have hkw := hk w ht
    have hkw0 : 0 ≤ κ := (hg u w).2.2.2.1.le
    have hkw1 : κ ≤ 1 := (hg u w).2.2.2.2
    have hKl := (abs_le.1 (hK w ht)).1
    have hKh := (abs_le.1 (hK w ht)).2
    have hkl : -(k + ε) ≤ K w := by linarith only [hKl]
    have hkh : K w ≤ -(k - ε) := by linarith only [hKh]
    have hlow := mul_le_mul_of_nonneg_left hkl hkw0
    have hhigh := mul_le_mul_of_nonneg_left hkh hkw0
    have h1 := mul_le_mul_of_nonneg_right hkw1 (show 0 ≤ k + ε by linarith only [hε, hεk])
    have h0 := mul_le_mul_of_nonneg_right hkw (sub_pos.2 hεk).le
    simp only [G, intervalExtension_apply, projIcc_of_mem hV (hsub ht)]
    change -(2 * (k + ε)) ≤ 2 * κ * K w ∧ 2 * κ * K w ≤ -(2 * κ₀ * (k - ε))
    constructor <;> nlinarith only [hlow, hhigh, h1, h0]
  have hGI : -(2 * (k + ε)) * Δ ≤ ∫ t in (a : ℝ)..b, G t ∧
      (∫ t in (a : ℝ)..b, G t) ≤ -(2 * κ₀ * (k - ε)) * Δ := by
    have hl := intervalIntegral.integral_mono_on (μ := volume) (show (a : ℝ) ≤ b from hab)
      (f := fun _ => -(2 * (k + ε))) intervalIntegrable_const (hGc.intervalIntegrable _ _) (fun t ht => (hGb t ht).1)
    have hh := intervalIntegral.integral_mono_on (μ := volume) (show (a : ℝ) ≤ b from hab)
      (hGc.intervalIntegrable _ _) (g := fun _ => -(2 * κ₀ * (k - ε))) intervalIntegrable_const (fun t ht => (hGb t ht).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, Δ] using And.intro hl hh
  have hNe (w : Icc 0 V) : -N u w = Real.exp (∫ t in (0 : ℝ)..w, G t) := by
    simpa only [neg_neg] using congrArg Neg.neg (hx.radialNu_mass_exponential hx.choose hn u w)
  have hNs : -N u b = (-N u a) * Real.exp (∫ t in (a : ℝ)..b, G t) := by
    rw [hNe b, hNe a, ← Real.exp_add,
      intervalIntegral.integral_add_adjacent_intervals (hGc.intervalIntegrable (0 : ℝ) a) (hGc.intervalIntegrable (a : ℝ) b)]
  have hEd (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) : HasDerivAt E (W t) t := by
    have htV := hsub (Ioo_subset_Icc_self ht)
    have hh := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      t (hx.longitudinal_derivative u htV)
    change HasDerivWithinAt E (x.2.1 u ⟨t, htV⟩ 2) (Icc 0 V) t at hh
    have hd : HasDerivWithinAt E (W t) (Icc 0 V) t := by
      simpa only [E, W, intervalExtension_apply, projIcc_of_mem hV htV] using hh
    exact hd.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2))
  have hEI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (a : ℝ) ≤ b from hab)
    hEc.continuousOn hEd (hWc.intervalIntegrable (a : ℝ) b)
  simp only [E, intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property] at hEI
  have hWb (t : ℝ) (ht : t ∈ Icc (a : ℝ) b) :
      -(2 * (k + ε) + d) ≤ W t ∧ W t ≤ -(2 * (k - ε) - d) := by
    have h1 := abs_le.1 (hK ⟨t, hsub ht⟩ ht)
    have h2 := abs_le.1 (herr ⟨t, hsub ht⟩ ht)
    simp only [W, intervalExtension_apply, projIcc_of_mem hV (hsub ht)]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have hEl : -(2 * (k + ε) + d) * Δ ≤ x.1 u b 2 - x.1 u a 2 := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) (show (a : ℝ) ≤ b from hab)
      (f := fun _ => -(2 * (k + ε) + d)) intervalIntegrable_const (hWc.intervalIntegrable _ _) (fun t ht => (hWb t ht).1)
    simpa only [hEI, intervalIntegral.integral_const, smul_eq_mul, mul_comm, Δ] using hh
  have hEh : x.1 u b 2 - x.1 u a 2 ≤ -(2 * (k - ε) - d) * Δ := by
    have hh := intervalIntegral.integral_mono_on (μ := volume) (show (a : ℝ) ≤ b from hab)
      (hWc.intervalIntegrable _ _) (g := fun _ => -(2 * (k - ε) - d)) intervalIntegrable_const (fun t ht => (hWb t ht).2)
    simpa only [hEI, intervalIntegral.integral_const, smul_eq_mul, mul_comm, Δ] using hh
  obtain ⟨_hJi, hJ0, _hq, _hqp, _hqm, hlid⟩ := hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha
  refine ⟨⟨?_, ?_⟩, ⟨hEl, hEh⟩, ?_, ?_⟩
  · rw [hNs]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hGI.1) (neg_pos.2 (hn u a)).le
  · rw [hNs]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hGI.2) (neg_pos.2 (hn u a)).le
  · rw [hlid]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (neg_pos.2 ha).le
    exact hEl.trans (le_add_of_nonneg_right hJ0)
  · rw [hlid]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (add_le_add hEh le_rfl)) (neg_pos.2 ha).le

/-! Bounded conformal and transport remainders retain the exact exponent. -/

theorem IsWaveIntegral.inner_exact_transport_of_remainders {M e Λ U V k R₀ J₀ : ℝ} {h r : ℝ → ℝ}
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
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    (3 / 4 ≤ -Real.exp (x.1 u b 2) / (4 * ν u b)) →
    (x.1 u b 2 - x.1 u a 2 + 2 * k * ((b : ℝ) - a) ≤ R₀) →
    ((∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ J₀) →
      |ν u b| ≤ (2 * Real.exp R₀) * (-ν u a) * Real.exp (-2 * k * ((b : ℝ) - a)) ∧
      |x.2.1 u b 0| ≤ (Real.exp (R₀ + J₀) * (-x.2.1 u a 0)) * Real.exp (-2 * k * ((b : ℝ) - a)) := by
  dsimp only
  intro hκ hR hJ
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hna : ν u a < 0 := (hg u a).2.2.1
  have hnb : ν u b < 0 := (hg u b).2.2.1
  have hEa : Real.exp (x.1 u a 2) ≤ 4 * (-ν u a) := by
    have hh := (div_le_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hna)).1
      (hg u a).2.2.2.2
    linarith only [hh]
  have hEb : 3 * (-ν u b) ≤ Real.exp (x.1 u b 2) := by
    have hh := (le_div_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hnb)).1 hκ
    linarith only [hh]
  have hE : Real.exp (x.1 u b 2) ≤
      (4 * (-ν u a)) * Real.exp R₀ * Real.exp (-2 * k * ((b : ℝ) - a)) := by
    calc
      _ = Real.exp (x.1 u a 2) * Real.exp (x.1 u b 2 - x.1 u a 2) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ (4 * (-ν u a)) * Real.exp (R₀ + (-2 * k * ((b : ℝ) - a))) :=
        mul_le_mul hEa (Real.exp_le_exp.2 (by linarith only [hR]))
          (Real.exp_pos _).le (by linarith only [hna])
      _ = _ := by rw [Real.exp_add]; ring
  have hlb := (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha).1
  obtain ⟨_hJi, _hJ0, _hq, _hqp, _hqm, heq⟩ :=
    hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha
  constructor
  · rw [abs_of_neg hnb]
    have hpos : 0 ≤ (-ν u a) * Real.exp R₀ * Real.exp (-2 * k * ((b : ℝ) - a)) :=
      mul_nonneg (mul_nonneg (neg_pos.2 hna).le (Real.exp_pos R₀).le) (Real.exp_pos _).le
    nlinarith only [hE, hEb, hpos]
  · rw [abs_of_neg hlb, heq]
    calc
      _ ≤ (-x.2.1 u a 0) * Real.exp ((R₀ + J₀) + (-2 * k * ((b : ℝ) - a))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith only [hR, hJ]))
          (neg_pos.2 ha).le
      _ = _ := by rw [Real.exp_add]; ring

theorem IsWaveIntegral.inner_exact_transport {M e Λ U V k : ℝ} {h r : ℝ → ℝ}
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
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    (3 / 4 ≤ -Real.exp (x.1 u b 2) / (4 * ν u b)) →
    (|x.1 u b 2 - x.1 u a 2 + 2 * k * ((b : ℝ) - a)| ≤ 1) →
    ((∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ 1) →
      |ν u b| ≤ (2 * Real.exp 1) * (-ν u a) * Real.exp (-2 * k * ((b : ℝ) - a)) ∧
      |x.2.1 u b 0| ≤ (Real.exp 2 * (-x.2.1 u a 0)) * Real.exp (-2 * k * ((b : ℝ) - a)) := by
  intro ν hκ hR hJ
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    hx.inner_exact_transport_of_remainders hU hV hUR hc hi hrc hr0 hφ hrd hp hf
      u a b hab ha hκ (abs_le.1 hR).2 hJ

theorem IsWaveIntegral.inner_exact_transport_restart {M e Λ U V k R₀ J₀ : ℝ} {h r : ℝ → ℝ}
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
    (u : Icc 0 U) (a₀ a b : Icc 0 V) (h₀a : a₀ ≤ a) (hab : a ≤ b)
    (h₀ : x.2.1 u a₀ 0 < 0) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    (3 / 4 ≤ -Real.exp (x.1 u b 2) / (4 * ν u b)) →
    (|x.1 u a 2 - x.1 u a₀ 2 + 2 * k * ((a : ℝ) - a₀)| ≤ R₀) →
    (|x.1 u b 2 - x.1 u a₀ 2 + 2 * k * ((b : ℝ) - a₀)| ≤ R₀) →
    ((∫ t in (a₀ : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ J₀) →
      |ν u b| ≤ (2 * Real.exp (2 * R₀)) * (-ν u a) * Real.exp (-2 * k * ((b : ℝ) - a)) ∧
      |x.2.1 u b 0| ≤ (Real.exp (2 * R₀ + J₀) * (-x.2.1 u a 0)) *
        Real.exp (-2 * k * ((b : ℝ) - a)) := by
  intro ν hκ hRa hRb hJ
  have ha := (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a₀ a h₀a h₀).1
  have hpre := hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a₀ a h₀a h₀
  have hpost := hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hpre.1 hpost.1
  apply hx.inner_exact_transport_of_remainders hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha hκ
  · linarith only [(abs_le.1 hRa).1, (abs_le.1 hRb).2]
  · linarith only [hJ, hsplit, hpre.2.1]

end CauchyHorizon
