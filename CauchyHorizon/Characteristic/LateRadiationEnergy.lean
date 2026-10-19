import CauchyHorizon.Characteristic.LateGammaRadiation
import CauchyHorizon.Characteristic.OpticalCorner
import CauchyHorizon.Reduced.SpatialRadiation
import CauchyHorizon.Reduced.RadiationEnergy
import CauchyHorizon.Characteristic.TransverseDifference

/-! The actual late supremum is continuous and its feedback is absorbed after first entry. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

noncomputable def lateRadiationDifferenceRows {U V : ℝ} (hU : 0 ≤ U)
    (W : C(Icc 0 V, ℝ)) (k : ℝ) (x : WaveState U V) : C(Icc 0 V, C(Icc 0 U, ℝ)) :=
  transverseRadiationRows k x ⟨fun v => projIcc 0 U hU (W v), by fun_prop⟩
    (ContinuousMap.const _ ⟨U, hU, le_rfl⟩)

noncomputable def lateSpatialRadiationRows {U V : ℝ}
    (W : C(Icc 0 V, ℝ)) (k : ℝ) (x : WaveState U V) : C(Icc 0 V, C(Icc 0 U, ℝ)) :=
  (⟨fun q : Icc 0 V × Icc 0 U =>
    let u : Icc 0 U := ⟨max (q.2 : ℝ) (min U (W q.1)),
      q.2.property.1.trans (le_max_left _ _), max_le q.2.property.2 (min_le_left _ _)⟩
    Real.exp (k * q.1) * (x.1 u q.1 0 * x.2.1 u q.1 1),
    by fun_prop⟩ : C(Icc 0 V × Icc 0 U, ℝ)).curry

noncomputable def lateSpatialRadiationEnvelope {U V : ℝ}
    (W : C(Icc 0 V, ℝ)) (k : ℝ) (x : WaveState U V) : C(Icc 0 V, ℝ) :=
  ⟨fun v => ‖lateSpatialRadiationRows W k x v‖, (lateSpatialRadiationRows W k x).continuous.norm⟩

theorem lateSpatialRadiationEnvelope_le_iff {U V k C : ℝ} (hU : 0 ≤ U)
    (W : C(Icc 0 V, ℝ)) (x : WaveState U V) (v : Icc 0 V) :
    lateSpatialRadiationEnvelope W k x v ≤ C ↔
      ∀ u : Icc 0 U, min U (W v) ≤ (u : ℝ) →
        Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ C := by
  let : Nonempty (Icc 0 U) := ⟨⟨0, le_rfl, hU⟩⟩
  change ‖lateSpatialRadiationRows W k x v‖ ≤ C ↔ _
  rw [ContinuousMap.norm_le_of_nonempty]
  constructor
  · intro hb u hu
    simpa only [lateSpatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
      max_eq_left hu, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using hb u
  · intro hb u
    dsimp only [lateSpatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact hb ⟨max (u : ℝ) (min U (W v)), u.property.1.trans (le_max_left _ _),
      max_le u.property.2 (min_le_left _ _)⟩ (le_max_right _ _)

set_option maxHeartbeats 1200000 in
theorem IsWaveIntegral.late_moving_radiation_energy
    {M₀ e Λ U V a k β j C Cd Co Jmax N T η Y ρ : ℝ} {h r : ℝ → ℝ}
    (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M₀ h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U))) (hfc : ContinuousOn f (Ioi 0))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU.le hV e Λ (incomingWaveCurve hU.le hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M₀ e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (ha : 0 < a) (hk : 0 < k) (hβ : 0 ≤ β) (hβ8 : β < 1 / 8)
    (hj : 0 < j) (hC : 0 < C) (hCd : 0 ≤ Cd) (hCo : 0 ≤ Co) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (g : ℝ → ℝ) (hgc : ContinuousOn g (Ici T)) (hga : StrictAntiOn g (Ici T))
    (hgp : ∀ t ∈ Ici T, 0 < g t) (hscale : ∀ t ∈ Ici T, j ≤ g t * Real.exp (a * t))
    (hchart : RadiationGammaCharts hU.le hV x g T (1 + β) η C Y)
    (W : C(Icc 0 V, ℝ)) (hW0 : ∀ v, 0 ≤ W v)
    (hW : ∀ v, W v = g (max T ((v : ℝ) / (1 + β))))
    (l : Icc 0 V) (hlT : T < (l : ℝ) / (1 + β)) (hlg : g ((l : ℝ) / (1 + β)) = U)
    (hr : ∀ u v, ρ ≤ x.1 u v 0)
    (entry : Icc 0 U → Icc 0 V)
    (hentry : ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V,
      T < (v : ℝ) / (1 + β) → g ((v : ℝ) / (1 + β)) ≤ u →
        entry u ≤ v ∧ x.2.1 u (entry u) 0 < 0 ∧
          -x.2.1 u (entry u) 0 / Real.exp (x.1 u (entry u) 2) ≤ Cd * (u : ℝ))
    (hcorner : ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V,
      T < (v : ℝ) / (1 + β) → g ((v : ℝ) / (1 + β)) ≤ u →
        Real.exp (x.1 u v 2) ≤ Co * ((u : ℝ) ^ (-1 - 2 * k / a) * Real.exp (-(2 * k) * v)))
    (hflux : ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V,
      T < (v : ℝ) / (1 + β) → g ((v : ℝ) / (1 + β)) ≤ u →
        (∫ t in (entry u : ℝ)..v, intervalExtension hV (x.1 u) t 0 *
          (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ Jmax) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU.le hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    (∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V,
      T < (v : ℝ) / (1 + β) → g ((v : ℝ) / (1 + β)) ≤ u →
        |ν u v| ≤ N * (u : ℝ) ^ (k / a * β - 1)) →
    let ξ := k * β / (1 + β)
    let χ := 3 * ξ
    let L := Cd * Co * Real.exp Jmax
    let c := (L * C / (1 + β) * j ^ (-(2 * k / a))) / ρ
    let d := (L * N * C / (1 + β) * j ^ (-(2 * k / a - k / a * β))) /
      (ρ ^ 2 * (2 * k - χ))
    d * Real.exp (-χ * l) ≤ k / 2 →
    let H := movingSpatialRadiationEnvelope W hW0 0 k 0 x
    let M := lateSpatialRadiationEnvelope W k x
    ∃ A : C(Icc 0 V, ℝ), (∀ v, 0 ≤ A v) ∧
      (∀ v, l ≤ v → A v = |g ((v : ℝ) / (1 + β)) * Real.exp (k * ((v : ℝ) / (1 + β))) *
        (x.1 (projIcc 0 U hU.le (g ((v : ℝ) / (1 + β)))) v 0 *
          derivWithin (fun u => intervalExtension hU.le x.1 u v 1)
            (Icc 0 U) (g ((v : ℝ) / (1 + β))))|) ∧
      (∀ q : ℝ, q < k → q ≤ ξ → q ≤ χ →
        (∫ t in (l : ℝ)..V,
          (Real.exp (q * t) * ‖lateRadiationDifferenceRows hU.le W k x (projIcc 0 V hV t)‖) ^ 2) ≤
            2 * (c / (k - q)) ^ 2 * (∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2) +
              2 * (d / (k - q)) ^ 2 * ∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ∧
      (∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
        8 * (∫ t in (l : ℝ)..V, (H (projIcc 0 V hV t)) ^ 2) +
          8 * (c * Real.exp (-ξ * l) / k) ^ 2 *
            ∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2 := by
  dsimp only
  intro hν hsmall
  let ξ := k * β / (1 + β)
  let χ := 3 * ξ
  let L := Cd * Co * Real.exp Jmax
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hlam (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 V)
      (hTv : T < (v : ℝ) / (1 + β)) (hgu : g ((v : ℝ) / (1 + β)) ≤ u) :
      |x.2.1 u v 0| ≤ L * (u : ℝ) ^ (-(2 * k / a)) * Real.exp (-(2 * k) * v) := by
    obtain ⟨hentryv, hneg, hDy⟩ := hentry u hu v hTv hgu
    exact hx.lambda_corner_of_optical_flux hU.le hV hUR hc hi hrc hr0 hφ hrd hp hf hCd hCo
      u hu (entry u) v hentryv hneg hDy (hcorner u hu v hTv hgu) (hflux u hu v hTv hgu)
  let c := (L * C / (1 + β) * j ^ (-(2 * k / a))) / ρ
  let d := (L * N * C / (1 + β) * j ^ (-(2 * k / a - k / a * β))) / (ρ ^ 2 * (2 * k - χ))
  let H := movingSpatialRadiationEnvelope W hW0 0 k 0 x
  let M := lateSpatialRadiationEnvelope W k x
  have hα : 0 < 1 + β := by linarith only [hβ]
  have hξ : 0 ≤ ξ := div_nonneg (mul_nonneg hk.le hβ) hα.le
  have hχ : 0 ≤ χ := mul_nonneg (by norm_num) hξ
  have hgap : 0 < 2 * k - χ := by
    have hh : 3 * (k * β) < 2 * k * (1 + β) := by
      nlinarith only [mul_pos hk (show 0 < 2 - β by linarith only [hβ8])]
    have hh' : χ < 2 * k := by
      dsimp only [χ, ξ]
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hα).2 hh
    exact sub_pos.2 hh'
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hM0 (v) : 0 ≤ M v := norm_nonneg (lateSpatialRadiationRows W k x v)
  have hWB (v : Icc 0 V) (hv : T ≤ (v : ℝ) / (1 + β)) : W v = g ((v : ℝ) / (1 + β)) := by
    rw [hW, max_eq_right hv]
  have hpost (v : Icc 0 V) (hv : l ≤ v) :
      T < (v : ℝ) / (1 + β) ∧ g ((v : ℝ) / (1 + β)) ≤ U := by
    have hdiv := div_le_div_of_nonneg_right (show (l : ℝ) ≤ v from hv) hα.le
    have ht := hlT.trans_le hdiv
    exact ⟨ht, (hga.antitoneOn hlT.le ht.le hdiv).trans_eq hlg⟩
  obtain ⟨A, hA0, hAval, hlate⟩ := hx.exists_late_gamma_source hU hV hUR hp hf hfc ha hk hβ hβ8
    hj hC hL hN hρ g hgc hga.antitoneOn hgp hscale hchart
  have hweight (B : C(Icc 0 V, ℝ)) (hB : ∀ v, 0 ≤ B v) {q : ℝ} (hq : 0 ≤ q)
      (s b : Icc 0 V) (hls : (l : ℝ) ≤ s) (hsb : s ≤ b) :
      (∫ t in (s : ℝ)..b, Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-q * t) * B (projIcc 0 V hV t)) ≤
        Real.exp (-q * l) * causalExpIntegralFrom hV l k B b := by
    let F := fun t => Real.exp (-k * ((b : ℝ) - t)) * B (projIcc 0 V hV t)
    have hFc : Continuous F := by fun_prop
    have hi := intervalIntegral.integral_mono_on (show (s : ℝ) ≤ b from hsb)
      (show IntervalIntegrable (fun t => Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-q * t) *
        B (projIcc 0 V hV t)) volume s b from (by fun_prop : Continuous _).intervalIntegrable _ _)
      ((hFc.const_mul (Real.exp (-q * l))).intervalIntegrable s b) (fun t ht => ?_)
    · rw [intervalIntegral.integral_const_mul] at hi
      exact hi.trans (mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_interval hls (show (s : ℝ) ≤ b from hsb) le_rfl
          (Filter.Eventually.of_forall (fun t => mul_nonneg (Real.exp_pos _).le (hB _)))
          (hFc.intervalIntegrable l b)) (Real.exp_pos _).le)
    · have he := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left (hls.trans ht.1) (neg_nonpos.2 hq))
      have hh := mul_le_mul_of_nonneg_left he
        (mul_nonneg (Real.exp_pos (-k * ((b : ℝ) - t))).le (hB (projIcc 0 V hV t)))
      dsimp only [F]
      nlinarith only [hh]
  have hprop (b : Icc 0 V) (hlb : l ≤ b) (u : Icc 0 U)
      (hgu : g ((b : ℝ) / (1 + β)) ≤ u) :
      ∃ s : Icc 0 V, l ≤ s ∧ s ≤ b ∧
        let K := c * (∫ t in (s : ℝ)..b,
          Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-ξ * t) * A (projIcc 0 V hV t)) +
            d * ∫ t in (s : ℝ)..b,
              Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-χ * t) * M (projIcc 0 V hV t)
        (Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1 -
          x.1 (projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))) b 0 *
            x.2.1 (projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))) b 1| ≤ K) ∧
        Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1| ≤
          Real.exp (k * b) * |x.1 (projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))) b 0 *
            x.2.1 (projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))) b 1| + K := by
    have hbT := (hpost b hlb).1
    have hrow (t : ℝ) (ht : t ∈ Icc (g ((b : ℝ) / (1 + β))) u) : t ∈ Icc 0 U :=
      ⟨(hgp _ hbT.le).le.trans ht.1, ht.2.trans u.property.2⟩
    obtain ⟨s, hsT, hsg, hsb, hdiff, hbnd⟩ := hlate M hM0 u b hbT hgu (fun t ht => by
      have hh := hlam (projIcc 0 U hU.le t)
        (by rw [projIcc_of_mem hU.le (hrow t ht)]; exact (hgp _ hbT.le).trans_le ht.1)
        b hbT (by rw [projIcc_of_mem hU.le (hrow t ht)]; exact ht.1)
      simpa only [projIcc_of_mem hU.le (hrow t ht)] using hh) (fun t ht w hwT hgw _hwb => by
      refine ⟨hr _ _, ?_, ?_⟩
      · have hh := hν (projIcc 0 U hU.le t)
          (by rw [projIcc_of_mem hU.le (hrow t ht)]; exact (hgp _ hbT.le).trans_le ht.1)
          w hwT (by rw [projIcc_of_mem hU.le (hrow t ht)]; exact hgw)
        simpa only [projIcc_of_mem hU.le (hrow t ht)] using hh
      · apply (lateSpatialRadiationEnvelope_le_iff hU.le W x w).1 le_rfl
        rw [projIcc_of_mem hU.le (hrow t ht), hWB w hwT.le]
        exact (min_le_right _ _).trans hgw)
    have hls : (l : ℝ) ≤ s := by
      by_contra hn
      have hh := hga hsT.le hlT.le (div_lt_div_of_pos_right (not_le.1 hn) hα)
      rw [hlg, hsg] at hh
      exact (not_lt_of_ge u.property.2) hh
    exact ⟨s, hls, hsb, hdiff, by simpa only [add_assoc] using hbnd⟩
  have hcausal (b : Icc 0 V) (hlb : l ≤ b) :
      M b ≤ H b + (c * Real.exp (-ξ * l)) * causalExpIntegralFrom hV l k A b +
        (d * Real.exp (-χ * l)) * causalExpIntegralFrom hV l k M b := by
    apply (lateSpatialRadiationEnvelope_le_iff hU.le W x b).2
    intro u hu
    have hbT := (hpost b hlb).1
    have hbu := (hpost b hlb).2
    have hgu : g ((b : ℝ) / (1 + β)) ≤ u := by
      rwa [hWB b hbT.le, min_eq_right hbu] at hu
    obtain ⟨s, hls, hsb, _hdiff, hbnd⟩ := hprop b hlb u hgu
    have hboundary : Real.exp (k * b) *
        |x.1 (projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))) b 0 *
          x.2.1 (projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))) b 1| ≤ H b := by
      have hh := (movingSpatialRadiationEnvelope_le_iff (a := 0) (k := k) (σ := 0)
        hU.le W hW0 x b).1 le_rfl (projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))) (by
          rw [projIcc_of_mem hU.le ⟨(hgp _ hbT.le).le, hbu⟩, hWB b hbT.le])
      simpa only [zero_mul, sub_zero] using hh
    have hf' := mul_le_mul_of_nonneg_left (hweight A hA0 hξ s b hls hsb) hc0
    have hm' := mul_le_mul_of_nonneg_left (hweight M hM0 hχ s b hls hsb) hd0
    change _ ≤ _ + (c * _ + d * _) at hbnd
    nlinarith only [hbnd, hboundary, hf', hm']
  refine ⟨A, hA0, fun v hv => hAval v (hpost v hv).1.le (hpost v hv).2, ?_,
    causalExpIntegralFrom_forcing_energy hV hk (mul_nonneg hd0 (Real.exp_pos _).le)
      hsmall l H A M hM0 hcausal⟩
  intro q hqk hqξ hqχ
  let D := lateRadiationDifferenceRows hU.le W k x
  let F : C(Icc 0 V, ℝ) := ⟨fun v => Real.exp (q * v) * ‖D v‖, by fun_prop⟩
  have hF0 (v : Icc 0 V) : 0 ≤ F v := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hweighted (b : Icc 0 V) (hlb : l ≤ b) :
      F b ≤ c * causalExpIntegralFrom hV l (k - q) A b +
        d * causalExpIntegralFrom hV l (k - q) M b := by
    change Real.exp (q * b) * ‖D b‖ ≤ _
    rw [mul_comm]
    apply (le_div_iff₀ (Real.exp_pos _)).1
    have : Nonempty (Icc (0 : ℝ) U) := ⟨⟨0, le_rfl, hU.le⟩⟩
    apply (ContinuousMap.norm_le_of_nonempty (D b)).2
    intro u
    apply (le_div_iff₀ (Real.exp_pos _)).2
    have hbT := (hpost b hlb).1
    have hbu := (hpost b hlb).2
    let z := projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))
    have hgu : g ((b : ℝ) / (1 + β)) ≤ (max z u : Icc 0 U) := by
      have hh : (z : ℝ) ≤ (max z u : Icc 0 U) := le_max_left z u
      simpa only [z, projIcc_of_mem hU.le ⟨(hgp _ hbT.le).le, hbu⟩] using hh
    obtain ⟨s, hls, hsb, hdiff, _⟩ := hprop b hlb (max z u) hgu
    have hf' := mul_le_mul_of_nonneg_left
      (causalExpIntegralFrom_weighted_le (k := k) hV hqξ l s b hls hsb A hA0) hc0
    have hm' := mul_le_mul_of_nonneg_left
      (causalExpIntegralFrom_weighted_le (k := k) hV hqχ l s b hls hsb M hM0) hd0
    have hh := mul_le_mul_of_nonneg_left hdiff (Real.exp_pos (q * b)).le
    simp only [D, lateRadiationDifferenceRows, transverseRadiationRows, ContinuousMap.curry_apply,
      ContinuousMap.coe_mk, ContinuousMap.const_apply, min_eq_left (show u ≤ ⟨U, hU.le, le_rfl⟩ from u.property.2),
      hWB b hbT.le, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    dsimp only [z] at hh
    nlinarith only [hh, hf', hm']
  have hh := causalExpIntegralFrom_sum_energy hV (sub_pos.2 hqk) l A M F hF0 hweighted
  calc
    _ = ∫ t in (l : ℝ)..V, (F (projIcc 0 V hV t)) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le l.property.2] at ht
      have htV : t ∈ Icc (0 : ℝ) V := ⟨l.property.1.trans ht.1, ht.2⟩
      simp only [F, D, ContinuousMap.coe_mk, projIcc_of_mem hV htV]
    _ ≤ _ := hh

end CauchyHorizon
