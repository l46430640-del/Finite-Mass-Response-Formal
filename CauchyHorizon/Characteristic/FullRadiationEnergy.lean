import CauchyHorizon.Characteristic.LateRadiationEnergy

/-! The early and gamma energies control the full spatial supremum, including first entry. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

theorem exists_radiation_absorption_width {a k β j d Umax : ℝ}
    (ha : 0 < a) (hk : 0 < k) (hβ : 0 < β) (hj : 0 < j) (hd : 0 ≤ d) (hUmax : 0 < Umax) :
    ∃ W : ℝ, 0 < W ∧ W ≤ Umax ∧ ∀ U : ℝ, 0 ≤ U → U ≤ W →
      d * j ^ (-(3 * k * β / a)) * U ^ (3 * k * β / a) ≤ k / 2 := by
  let q := 3 * k * β / a
  have hq : 0 < q := by dsimp only [q]; positivity
  let F := fun u : ℝ => d * j ^ (-q) * u ^ q
  have hFc : Continuous F := by dsimp only [F]; fun_prop (disch := positivity)
  have hF0 : F 0 = 0 := by simp only [F, Real.zero_rpow hq.ne', mul_zero]
  have he : ∀ᶠ u : ℝ in 𝓝 0, F u < k / 2 :=
    hFc.continuousAt.tendsto.eventually_lt_const (by rw [hF0]; positivity)
  obtain ⟨W, hW, hWmax, hFW⟩ := ((eventually_lt_nhds hUmax).and he).exists_gt
  refine ⟨W, hW, hWmax.le, ?_⟩
  intro U hU hUW
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hU hUW hq.le)
    (by positivity : 0 ≤ d * j ^ (-q))).trans hFW.le

set_option maxHeartbeats 1600000 in
theorem IsWaveIntegral.full_radiation_energy_of_optical_flux
    {M₀ e Λ U V a k β j C Cd Co Jmax N T η Y ρ Ee Eg : ℝ} {h r : ℝ → ℝ}
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
    (hT : 0 ≤ T) (hEg : 0 ≤ Eg)
    (g : ℝ → ℝ) (hgc : ContinuousOn g (Ici T)) (hga : StrictAntiOn g (Ici T))
    (hstart : U < g T)
    (hgp : ∀ t ∈ Ici T, 0 < g t) (hscale : ∀ t ∈ Ici T, j ≤ g t * Real.exp (a * t))
    (hchart : RadiationGammaCharts hU.le hV x g T (1 + β) η C Y)
    (W : C(Icc 0 V, ℝ)) (hW0 : ∀ v, 0 ≤ W v)
    (hW : ∀ v, W v = g (max T ((v : ℝ) / (1 + β))))
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
    let L := Cd * Co * Real.exp Jmax
    let c := (L * C / (1 + β) * j ^ (-(2 * k / a))) / ρ
    let d := (L * N * C / (1 + β) * j ^ (-(2 * k / a - k / a * β))) /
      (ρ ^ 2 * (2 * k - 3 * (k * β / (1 + β))))
    d * j ^ (-(3 * k * β / a)) * U ^ (3 * k * β / a) ≤ k / 2 →
    let H := movingSpatialRadiationEnvelope W hW0 0 k 0 x
    let Z := fun t v : ℝ => g t * Real.exp (k * t) *
      (intervalExtension hV (intervalExtension hU.le x.1 (g t)) v 0 *
        derivWithin (fun u => intervalExtension hV (intervalExtension hU.le x.1 u) v 1)
          (Icc 0 U) (g t))
    (∫ t in (0 : ℝ)..V, (H (projIcc 0 V hV t)) ^ 2) ≤ Ee →
    (∀ s t : ℝ, T ≤ s → s ≤ t → (1 + β) * t ≤ V → g s ≤ U →
      (∫ w in s..t, (Z w ((1 + β) * w)) ^ 2) ≤ Eg) →
    let S := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 V) U) (fun _ => hU.le) 0 k 0 x
    ((∫ t in (0 : ℝ)..V, (S (projIcc 0 V hV t)) ^ 2) ≤
      9 * Ee + 8 * (1 + β) * (c / k) ^ 2 * Eg) ∧
    ∀ q : ℝ, q < k → q ≤ k * β / (1 + β) → q ≤ 3 * (k * β / (1 + β)) →
      (∫ t in (0 : ℝ)..V,
        (Real.exp (q * t) * ‖lateRadiationDifferenceRows hU.le W k x (projIcc 0 V hV t)‖) ^ 2) ≤
      2 * (c / (k - q)) ^ 2 * ((1 + β) * Eg) +
        2 * (d / (k - q)) ^ 2 * (8 * Ee + 8 * (1 + β) * (c / k) ^ 2 * Eg) := by
  dsimp only
  intro hν hsmall hE hZ
  let α := 1 + β
  let ξ := k * β / α
  let χ := 3 * ξ
  let L := Cd * Co * Real.exp Jmax
  let c := (L * C / α * j ^ (-(2 * k / a))) / ρ
  let d := (L * N * C / α * j ^ (-(2 * k / a - k / a * β))) / (ρ ^ 2 * (2 * k - χ))
  let H := movingSpatialRadiationEnvelope W hW0 0 k 0 x
  let M := lateSpatialRadiationEnvelope W k x
  let S := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 V) U) (fun _ => hU.le) 0 k 0 x
  let D := lateRadiationDifferenceRows hU.le W k x
  let Z := fun t v : ℝ => g t * Real.exp (k * t) *
    (intervalExtension hV (intervalExtension hU.le x.1 (g t)) v 0 *
      derivWithin (fun u => intervalExtension hV (intervalExtension hU.le x.1 u) v 1)
        (Icc 0 U) (g t))
  change ((∫ t in (0 : ℝ)..V, (S (projIcc 0 V hV t)) ^ 2) ≤
      9 * Ee + 8 * α * (c / k) ^ 2 * Eg) ∧
    ∀ q : ℝ, q < k → q ≤ ξ → q ≤ χ →
      (∫ t in (0 : ℝ)..V, (Real.exp (q * t) * ‖D (projIcc 0 V hV t)‖) ^ 2) ≤
      2 * (c / (k - q)) ^ 2 * (α * Eg) +
        2 * (d / (k - q)) ^ 2 * (8 * Ee + 8 * α * (c / k) ^ 2 * Eg)
  have hα : 0 < α := by dsimp only [α]; linarith only [hβ]
  have hH0 (v) : 0 ≤ H v := norm_nonneg (movingSpatialRadiationRows W hW0 0 k 0 x v)
  have hM0 (v) : 0 ≤ M v := norm_nonneg (lateSpatialRadiationRows W k x v)
  have hS0 (v) : 0 ≤ S v :=
    norm_nonneg (movingSpatialRadiationRows (ContinuousMap.const (Icc 0 V) U) (fun _ => hU.le) 0 k 0 x v)
  have hHc : Continuous (fun t => (H (projIcc 0 V hV t)) ^ 2) := by fun_prop
  have hMc : Continuous (fun t => (M (projIcc 0 V hV t)) ^ 2) := by fun_prop
  have hSc : Continuous (fun t => (S (projIcc 0 V hV t)) ^ 2) := by fun_prop
  have hEe : 0 ≤ Ee := (intervalIntegral.integral_nonneg hV (fun _ _ => sq_nonneg _)).trans hE
  have hpreD (v : Icc 0 V) (hv : U ≤ W v) : D v = 0 := by
    ext u
    simp only [D, lateRadiationDifferenceRows, transverseRadiationRows, ContinuousMap.curry_apply,
      ContinuousMap.coe_mk, ContinuousMap.const_apply, projIcc_of_right_le hU.le hv,
      min_eq_left (show u ≤ ⟨U, hU.le, le_rfl⟩ from u.property.2),
      max_eq_left (show u ≤ ⟨U, hU.le, le_rfl⟩ from u.property.2), sub_self, mul_zero,
      ContinuousMap.zero_apply]
  have hpre (v : Icc 0 V) (hv : U ≤ W v) : S v ≤ H v := by
    apply (movingSpatialRadiationEnvelope_le_iff hU.le _ _ x v).2
    intro u _
    simpa only [zero_mul, sub_zero] using
      (movingSpatialRadiationEnvelope_le_iff (a := 0) (k := k) (σ := 0) hU.le W hW0 x v).1
        le_rfl u (u.property.2.trans hv)
  have hsplit (v : Icc 0 V) : S v ^ 2 ≤ H v ^ 2 + M v ^ 2 := by
    have hb : S v ≤ max (H v) (M v) := by
      apply (movingSpatialRadiationEnvelope_le_iff hU.le _ _ x v).2
      intro u _
      simp only [zero_mul, sub_zero]
      by_cases hu : (u : ℝ) ≤ W v
      · have hh := (movingSpatialRadiationEnvelope_le_iff (a := 0) (k := k) (σ := 0)
          hU.le W hW0 x v).1 le_rfl u hu
        apply le_trans _ (le_max_left (H v) (M v))
        simpa only [zero_mul, sub_zero] using hh
      · exact ((lateSpatialRadiationEnvelope_le_iff hU.le W x v).1 le_rfl u
          ((min_le_right _ _).trans (not_le.1 hu).le)).trans (le_max_right _ _)
    rcases le_total (H v) (M v) with hh | hh
    · rw [max_eq_right hh] at hb
      nlinarith only [sq_le_sq₀ (hS0 v) (hM0 v) |>.2 hb, sq_nonneg (H v)]
    · rw [max_eq_left hh] at hb
      nlinarith only [sq_le_sq₀ (hS0 v) (hH0 v) |>.2 hb, sq_nonneg (M v)]
  by_cases hentered : T < V / α ∧ g (V / α) ≤ U
  · obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' hentered.1.le
      (hgc.mono (show Icc T (V / α) ⊆ Ici T from fun _ h => h.1))
      (show U ∈ Icc (g (V / α)) (g T) from ⟨hentered.2, hstart.le⟩)
    have htT : T < t := by
      by_contra hn
      have he := le_antisymm (not_lt.1 hn) ht.1
      rw [he] at hgt
      exact hstart.ne hgt.symm
    let l : Icc 0 V := ⟨α * t, mul_nonneg hα.le (hT.trans ht.1),
      by simpa only [mul_comm] using (le_div_iff₀ hα).1 ht.2⟩
    have hldiv : (l : ℝ) / α = t := by dsimp only [l]; field_simp
    have hlT : T < (l : ℝ) / α := by rwa [hldiv]
    have hlg : g ((l : ℝ) / α) = U := by rwa [hldiv]
    have hgap : 0 < 2 * k - χ := by
      have hh : 3 * (k * β) < 2 * k * α := by
        dsimp only [α]
        nlinarith only [mul_pos hk (show 0 < 2 - β by linarith only [hβ8])]
      have hh' : χ < 2 * k := by
        dsimp only [χ, ξ]
        rw [← mul_div_assoc]
        exact (div_lt_iff₀ hα).2 hh
      exact sub_pos.2 hh'
    have hd : 0 ≤ d := by dsimp only [d, L]; positivity
    have hc0 : 0 ≤ c := by dsimp only [c, L]; positivity
    have hξ : 0 ≤ ξ := by dsimp only [ξ]; positivity
    have hscaleU : j ≤ U * Real.exp (a * t) := by simpa only [hgt] using hscale t ht.1
    have he := arrival_exp_power ha hU hj (by positivity : 0 ≤ 3 * k * β) hscaleU
    have hexp : -(3 * k * β) * t = -χ * (l : ℝ) := by
      dsimp only [χ, ξ, l]
      field_simp
    rw [hexp] at he
    change d * j ^ (-(3 * k * β / a)) * U ^ (3 * k * β / a) ≤ k / 2 at hsmall
    have hsmall' : d * Real.exp (-χ * l) ≤ k / 2 :=
      (mul_le_mul_of_nonneg_left he hd).trans (by simpa only [mul_assoc] using hsmall)
    obtain ⟨A, _hA0, hAval, hweighted, hlate⟩ := hx.late_moving_radiation_energy hU hV hUR hc hi hrc hr0 hφ hrd
      hp hf hfc ha hk hβ hβ8 hj hC hCd hCo hN hρ g hgc hga hgp hscale hchart
      W hW0 hW l hlT hlg hr entry hentry hcorner hflux hν hsmall'
    have hAE : (∫ v in (l : ℝ)..V, (A (projIcc 0 V hV v)) ^ 2) ≤ α * Eg := by
      calc
        _ = ∫ v in (l : ℝ)..V, (Z (v / α) (α * (v / α))) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro v hv
          rw [uIcc_of_le l.property.2] at hv
          have hvV : v ∈ Icc 0 V := ⟨l.property.1.trans hv.1, hv.2⟩
          have hvα : α * (v / α) = v := by field_simp
          dsimp only
          rw [hAval _ (by rw [projIcc_of_mem hV hvV]; exact hv.1)]
          simp only [Z, hvα, intervalExtension_apply,
            projIcc_of_mem hV hvV, sq_abs, α]
        _ = α * ∫ t in (l : ℝ) / α..V / α, (Z t (α * t)) ^ 2 := by
          simpa only [smul_eq_mul] using
            (intervalIntegral.integral_comp_div (fun t => (Z t (α * t)) ^ 2)
              (a := (l : ℝ)) (b := V) hα.ne')
        _ ≤ α * Eg := mul_le_mul_of_nonneg_left
          (hZ _ _ hlT.le (div_le_div_of_nonneg_right l.property.2 hα.le)
            (by change α * (V / α) ≤ V; exact le_of_eq (by field_simp)) hlg.le) hα.le
    have hHE : (∫ v in (l : ℝ)..V, (H (projIcc 0 V hV v)) ^ 2) ≤ Ee :=
      (intervalIntegral.integral_mono_interval l.property.1 l.property.2 le_rfl
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (hHc.intervalIntegrable 0 V)).trans hE
    have hcoef : (c * Real.exp (-ξ * l) / k) ^ 2 ≤ (c / k) ^ 2 := by
      apply (sq_le_sq₀ (by positivity) (div_nonneg hc0 hk.le)).2
      apply div_le_div_of_nonneg_right _ hk.le
      simpa only [neg_mul] using (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2
        (neg_nonpos.2 (mul_nonneg hξ l.property.1))) hc0).trans_eq (mul_one c)
    have hlateE : (∫ v in (l : ℝ)..V, (M (projIcc 0 V hV v)) ^ 2) ≤
        8 * Ee + 8 * α * (c / k) ^ 2 * Eg := by
      have hI0 : 0 ≤ ∫ v in (l : ℝ)..V, (A (projIcc 0 V hV v)) ^ 2 :=
        intervalIntegral.integral_nonneg l.property.2 (fun _ _ => sq_nonneg _)
      exact (hlate.trans (add_le_add (mul_le_mul_of_nonneg_left hHE (by norm_num))
        ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hI0).trans
          (mul_le_mul_of_nonneg_left hAE (by positivity))))).trans_eq (by ring)
    have hbeforeW (v : Icc 0 V) (hv : v ≤ l) : U ≤ W v := by
      rw [hW, ← hgt]
      apply hga.antitoneOn (show T ≤ max T ((v : ℝ) / α) from le_max_left _ _) ht.1
      exact max_le ht.1 (by rw [← hldiv]; exact div_le_div_of_nonneg_right hv hα.le)
    have hbefore : (∫ v in (0 : ℝ)..l, (S (projIcc 0 V hV v)) ^ 2) ≤
        ∫ v in (0 : ℝ)..l, (H (projIcc 0 V hV v)) ^ 2 := by
      apply intervalIntegral.integral_mono_on l.property.1 (hSc.intervalIntegrable _ _) (hHc.intervalIntegrable _ _)
      intro v hv
      apply (sq_le_sq₀ (hS0 _) (hH0 _)).2
      have hvV : v ∈ Icc 0 V := ⟨hv.1, hv.2.trans l.property.2⟩
      exact hpre _ (hbeforeW _ (by rw [projIcc_of_mem hV hvV]; exact hv.2))
    have hafter : (∫ v in (l : ℝ)..V, (S (projIcc 0 V hV v)) ^ 2) ≤
        (∫ v in (l : ℝ)..V, (H (projIcc 0 V hV v)) ^ 2) +
          ∫ v in (l : ℝ)..V, (M (projIcc 0 V hV v)) ^ 2 := by
      rw [← intervalIntegral.integral_add (hHc.intervalIntegrable _ _) (hMc.intervalIntegrable _ _)]
      exact intervalIntegral.integral_mono_on l.property.2 (hSc.intervalIntegrable _ _)
        ((hHc.add hMc).intervalIntegrable _ _) (fun _ _ => hsplit _)
    have hjS := intervalIntegral.integral_add_adjacent_intervals
      (hSc.intervalIntegrable (μ := volume) 0 l) (hSc.intervalIntegrable (l : ℝ) V)
    have hjH := intervalIntegral.integral_add_adjacent_intervals
      (hHc.intervalIntegrable (μ := volume) 0 l) (hHc.intervalIntegrable (l : ℝ) V)
    constructor
    · linarith only [hbefore, hafter, hjS, hjH, hE, hlateE]
    intro q hqk hqξ hqχ
    let F := fun t : ℝ => (Real.exp (q * t) * ‖D (projIcc 0 V hV t)‖) ^ 2
    have hFc : Continuous F := by fun_prop
    have hzero : ∫ t in (0 : ℝ)..l, F t = 0 := by
      apply Eq.trans (b := ∫ _t in (0 : ℝ)..l, (0 : ℝ)) _ (intervalIntegral.integral_zero)
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le l.property.1] at ht
      have htV : t ∈ Icc 0 V := ⟨ht.1, ht.2.trans l.property.2⟩
      have hh := hpreD (projIcc 0 V hV t)
        (hbeforeW _ (by rw [projIcc_of_mem hV htV]; exact ht.2))
      simp only [F, hh, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0)]
    have hjoin := intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable (μ := volume) 0 l) (hFc.intervalIntegrable (l : ℝ) V)
    rw [hzero, zero_add] at hjoin
    change (∫ t in (0 : ℝ)..V, F t) ≤ _
    rw [← hjoin]
    exact (hweighted q hqk hqξ hqχ).trans
      (add_le_add (mul_le_mul_of_nonneg_left hAE (by positivity))
        (mul_le_mul_of_nonneg_left hlateE (by positivity)))
  · have hend : U ≤ g (max T (V / α)) := by
      by_cases ht : T < V / α
      · rw [max_eq_right ht.le]
        exact (not_le.1 (fun hh => hentered ⟨ht, hh⟩)).le
      · rw [max_eq_left (not_lt.1 ht)]
        exact hstart.le
    have hnoW (v : Icc 0 V) : U ≤ W v := by
      rw [hW]
      exact hend.trans (hga.antitoneOn
        (show T ≤ max T ((v : ℝ) / α) from le_max_left _ _)
        (show T ≤ max T (V / α) from le_max_left _ _)
        (max_le_max_left T (div_le_div_of_nonneg_right v.property.2 hα.le)))
    have hall : (∫ v in (0 : ℝ)..V, (S (projIcc 0 V hV v)) ^ 2) ≤ Ee := by
      apply le_trans _ hE
      apply intervalIntegral.integral_mono_on hV (hSc.intervalIntegrable _ _) (hHc.intervalIntegrable _ _)
      intro v hv
      apply (sq_le_sq₀ (hS0 _) (hH0 _)).2
      exact hpre _ (hnoW _)
    have hnonneg : 0 ≤ 8 * α * (c / k) ^ 2 * Eg := by positivity
    constructor
    · linarith only [hall, hEe, hnonneg]
    intro q _ _ _
    simp only [hpreD _ (hnoW _), norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0),
      intervalIntegral.integral_zero]
    positivity

end CauchyHorizon
