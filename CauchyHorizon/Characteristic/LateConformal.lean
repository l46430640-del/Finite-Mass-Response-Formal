import CauchyHorizon.Characteristic.LateHorizontal
import CauchyHorizon.Reduced.LongitudinalConstraint
import CauchyHorizon.Analysis.ArrivalPower

/-! Small incoming width controls the actual conformal source without a late mass bound. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

set_option maxHeartbeats 800000 in
theorem IsWaveIntegral.late_conformal_source_bound {U V R φ₀ e Λ ρ O N L H P C G d s q : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hpq : p.toReal.HolderConjugate q)
    {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hρ : 0 < ρ) (hO : 0 ≤ O) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hG : 0 ≤ G) (hd : 0 < d) (hs : 0 < s)
    (z u : Icc 0 U) (hz : 0 < (z : ℝ)) (hzu : z ≤ u) (v : Icc 0 V)
    (hgeom : ∀ w ∈ Icc z u,
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose w v
      ρ ≤ x.1 w v 0 ∧ |ν| ≤ N * (w : ℝ) ^ (d - 1) ∧
        Real.exp (x.1 w v 2) ≤ O * (w : ℝ) ^ (d - 1) ∧ |x.2.1 w v 0| ≤ L ∧
        |x.2.1 w v 1| ≤ H ∧ |conformalPotential (x.1 w v 0) e| ≤ P)
    (hψ : ∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.2.2 t v 1| ≤ C * |f t| + G * t ^ (s - 1)) :
    |x.2.1 u v 2 - x.2.1 z v 2| ≤
      (O * P + 2 * L * N / ρ ^ 2) * U ^ d / d +
        2 * H * (C * (eLpNorm f p (volume.restrict (Icc 0 U))).toReal * U ^ (1 / q) +
          G * U ^ s / s) := by
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose
  let W := fun t => intervalExtension hU x.2.1 t v 2
  let K := O * P + 2 * L * N / ρ ^ 2
  let B := fun t : ℝ => K * t ^ (d - 1) + 2 * H * C * |f t| + 2 * H * G * t ^ (s - 1)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let ev : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (2 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  have hWc : AbsolutelyContinuousOnInterval W 0 U :=
    absolutelyContinuous_comp_contDiffAt (g := ev) hx.velocity_horizontal_absolutelyContinuous
      (fun _ _ => ev.contDiff.contDiffAt)
  have hbound : ∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u → |deriv W t| ≤ B t := by
    filter_upwards [hx.wave_equation, hx.radialNu_ae hx.choose
      (incomingWave_constraint_data hU hUR hp hf φ₀).1, hψ, ae_restrict_mem measurableSet_Icc,
      (volume.restrict (Icc 0 U)).ae_ne 0, (volume.restrict (Icc 0 U)).ae_ne U]
      with t hw hn hψt ht ht0 htU
    intro htm
    let w : Icc 0 U := ⟨t, ht⟩
    have hg := hgeom w htm
    have hder := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hw v)
    have hdW := (hder.hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne ht.1 ht0.symm)
      (lt_of_le_of_ne ht.2 htU))).deriv
    change deriv W t = _ at hdW
    simp only [ContinuousLinearMap.proj_apply, waveSource, Matrix.cons_val,
      projIcc_of_mem hU ht, hn v] at hdW
    have hscalar : |-2 * x.2.2 t v 1 * x.2.1 w v 1| ≤
        2 * H * (C * |f t| + G * t ^ (s - 1)) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hh := mul_le_mul (hψt htm) hg.2.2.2.2.1 (abs_nonneg _) (by positivity [ht.1])
      nlinarith only [hh]
    have hpot : |Real.exp (x.1 w v 2) * conformalPotential (x.1 w v 0) e| ≤ O * P * (w : ℝ) ^ (d - 1) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul hg.2.2.1 hg.2.2.2.2.2 (abs_nonneg _) (by positivity [w.property.1])).trans_eq (by ring)
    have hmix : |2 * ν w v * x.2.1 w v 0 / (x.1 w v 0) ^ 2| ≤
        (2 * L * N / ρ ^ 2) * (w : ℝ) ^ (d - 1) := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_pow, sq_abs]
      have hh := div_le_div₀ (by positivity : 0 ≤ 2 * |ν w v| * L)
        (mul_le_mul_of_nonneg_left hg.2.2.2.1 (by positivity : 0 ≤ 2 * |ν w v|))
        (sq_pos_of_pos hρ) (pow_le_pow_left₀ hρ.le hg.1 2)
      exact (hh.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg.2.1 (by norm_num : (0 : ℝ) ≤ 2)) hL)
        (sq_nonneg ρ))).trans_eq (by ring)
    rw [hdW]
    have habs (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    exact ((habs _ _ _).trans (add_le_add (add_le_add hscalar hpot) hmix)).trans_eq
      (by dsimp only [B, K]; ring)
  have hsub : uIcc (z : ℝ) u ⊆ uIcc (0 : ℝ) U := by
    rw [uIcc_of_le (show (z : ℝ) ≤ u from hzu), uIcc_of_le hU]
    exact Icc_subset_Icc z.property.1 u.property.2
  have hpi (b : ℝ) : IntervalIntegrable (fun t : ℝ => t ^ b) volume (z : ℝ) u :=
    (continuousOn_id.rpow_const (fun t ht => Or.inl (hz.trans_le ht.1).ne')).intervalIntegrable_of_Icc hzu
  have hfi : IntervalIntegrable (fun t => |f t|) volume 0 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      (hf.integrable ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp)).abs
  have hi1 := (hpi (d - 1)).const_mul K
  have hi2 := (hfi.mono_set hsub).const_mul (2 * H * C)
  have hi3 := (hpi (s - 1)).const_mul (2 * H * G)
  have hI := intervalIntegral.norm_integral_le_of_norm_le (show (z : ℝ) ≤ u from hzu)
    (f := deriv W) (g := B) (by
      apply (ae_restrict_iff' measurableSet_Ioc).1
      filter_upwards [ae_mono (Measure.restrict_mono (show Ioc (z : ℝ) u ⊆ Icc 0 U from
        fun _ ht => ⟨z.property.1.trans ht.1.le, ht.2.trans u.property.2⟩) le_rfl) hbound,
        ae_restrict_mem measurableSet_Ioc] with t ht htm
      simpa only [Real.norm_eq_abs] using ht (Ioc_subset_Icc_self htm)) ((hi1.add hi2).add hi3)
  rw [(hWc.mono hsub).integral_deriv_eq_sub, Real.norm_eq_abs] at hI
  simp only [W, intervalExtension_apply, projIcc_of_mem hU u.property, projIcc_of_mem hU z.property] at hI
  dsimp only [B] at hI
  rw [intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hI
  have hpw (b : ℝ) (hb : 0 < b) : (∫ t in (z : ℝ)..u, t ^ (b - 1)) ≤ U ^ b / b := by
    rw [integral_rpow (Or.inl (by linarith only [hb])), sub_add_cancel]
    exact div_le_div_of_nonneg_right ((sub_le_self _ (Real.rpow_nonneg z.property.1 _)).trans
      (Real.rpow_le_rpow u.property.1 u.property.2 hb.le)) hb.le
  have hplain : (∫ t in (z : ℝ)..u, |f t|) ≤
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal * U ^ (1 / q) := by
    have hh := (intervalIntegral.integral_mono_interval z.property.1 hzu u.property.2
      (Filter.Eventually.of_forall (fun t => abs_nonneg (f t))) hfi).trans
      (incoming_integral_abs_le_lp_power hU ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp) hf)
    simpa only [one_div, hpq.one_sub_inv] using hh
  exact (hI.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (hpw d hd) (by positivity))
    (mul_le_mul_of_nonneg_left hplain (by positivity)))
    (mul_le_mul_of_nonneg_left (hpw s hs) (by positivity)))).trans_eq (by dsimp only [K]; ring)

set_option maxHeartbeats 800000 in
theorem IsWaveIntegral.late_conformal_bound {U V R φ₀ e Λ ρ N L H P C G d s q : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hpq : p.toReal.HolderConjugate q)
    {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) vOut
      (incomingWaveVelocity hUR hp hf) x)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hG : 0 ≤ G) (hd : 0 < d) (hs : 0 < s)
    (z u : Icc 0 U) (hz : 0 < (z : ℝ)) (hzu : z ≤ u) (v : Icc 0 V)
    (hgeom : ∀ w ∈ Icc z u,
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose w v
      ρ ≤ x.1 w v 0 ∧ -ν ≤ N * (w : ℝ) ^ (d - 1) ∧
        Real.exp (x.1 w v 2) ≤ 4 * (-ν) ∧ |x.2.1 w v 0| ≤ L ∧
        |x.2.1 w v 1| ≤ H ∧ |conformalPotential (x.1 w v 0) e| ≤ P)
    (hψ : ∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.2.2 t v 1| ≤ C * |f t| + G * t ^ (s - 1)) :
    |x.2.1 u v 2 - x.2.1 z v 2| ≤
      (4 * P + 2 * L / ρ ^ 2) * N * U ^ d / d +
        2 * H * (C * (eLpNorm f p (volume.restrict (Icc 0 U))).toReal * U ^ (1 / q) +
          G * U ^ s / s) := by
  have hh := hx.late_conformal_source_bound hU hV hUR hp hpq hf hρ
    (O := 4 * N) (by positivity) hN hL hH hP hC hG hd hs z u hz hzu v (by
      intro w hw
      have hg := hgeom w hw
      have hn : 0 < -(radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf φ₀) x.1 hx.choose w v) := by
        have he := (Real.exp_pos (x.1 w v 2)).trans_le hg.2.2.1
        linarith only [he]
      refine ⟨hg.1, ?_, ?_, hg.2.2.2⟩
      · simpa only [abs_of_neg (neg_pos.1 hn)] using hg.2.1
      · exact (hg.2.2.1.trans (mul_le_mul_of_nonneg_left hg.2.1 (by norm_num : (0 : ℝ) ≤ 4))).trans_eq (by ring)) hψ
  exact hh.trans_eq (by ring)

set_option maxHeartbeats 800000 in
theorem exists_late_conformal_improvement {ρ N L H P C G d s q a τ E j A ε Umax k : ℝ}
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hpq : p.toReal.HolderConjugate q)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hd : 0 < d) (hs : 0 < s)
    (ha : 0 < a) (hτ : 0 < τ) (hE : 0 ≤ E) (hj : 0 < j) (hA : 0 ≤ A)
    (hε : 0 < ε) (hUmax : 0 < Umax) :
    ∃ W : ℝ, 0 < W ∧ W ≤ Umax ∧ E * j ^ (-(τ / a)) * W ^ (τ / a) < ε ∧
      ∀ (U V R φ₀ e Λ : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < R)
        (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (vOut : C(Icc 0 V, WaveVector)) (x : WaveState U V)
        (hx : IsWaveIntegral hU.le hV e Λ (incomingWaveCurve hU.le hUR hp hf φ₀)
          vOut (incomingWaveVelocity hUR hp hf) x), U ≤ W →
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        ∀ γ : ℝ → ℝ, ContinuousOn γ (Ioc 0 U) → StrictAntiOn γ (Ioc 0 U) →
          Tendsto γ (𝓝[>] (0 : ℝ)) atTop →
          (∀ z ∈ Ioc 0 U, j ≤ z * Real.exp (a * γ z)) →
          (∀ z : Icc 0 U, 0 < (z : ℝ) → ∀ v : Icc 0 V, γ z = v →
            |x.2.1 z v 2 + 2 * k| ≤ E * Real.exp (-τ * v)) →
          (∀ z u : Icc 0 U, 0 < (z : ℝ) → z ≤ u → ∀ v : Icc 0 V, γ z = v →
            |x.2.1 u v 0| ≤ L) →
          (∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V, γ u ≤ v →
            let ν := radialNuField hV e Λ (incomingWaveCurve hU.le hUR hp hf φ₀) x.1 hx.choose u v
            ρ ≤ x.1 u v 0 ∧ -ν ≤ N * (u : ℝ) ^ (d - 1) ∧
              Real.exp (x.1 u v 2) ≤ 4 * (-ν) ∧ |x.2.1 u v 1| ≤ H ∧
              |conformalPotential (x.1 u v 0) e| ≤ P) →
          (∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, 0 < t → γ t ≤ v →
            |x.2.2 t v 1| ≤ C * |f t| + G * t ^ (s - 1)) →
          ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V, γ u ≤ v →
            |x.2.1 u v 2 + 2 * k| < ε := by
  let F := fun w : ℝ => E * j ^ (-(τ / a)) * w ^ (τ / a) +
    (4 * P + 2 * L / ρ ^ 2) * N * w ^ d / d +
    2 * H * (C * A * w ^ (1 / q) + G * w ^ s / s)
  have hb : 0 < 1 / q := one_div_pos.2 hpq.symm.pos
  have hta : 0 < τ / a := div_pos hτ ha
  have hFc : Continuous F := by unfold F; fun_prop (disch := positivity)
  have hF0 : F 0 = 0 := by
    simp only [F, Real.zero_rpow hta.ne', Real.zero_rpow hd.ne', Real.zero_rpow hb.ne',
      Real.zero_rpow hs.ne', mul_zero, zero_div, add_zero]
  have hsmall : ∀ᶠ w : ℝ in 𝓝 0, F w < ε :=
    hFc.continuousAt.tendsto.eventually_lt_const (by rwa [hF0])
  obtain ⟨W, hW, hWmax, hFW⟩ := ((eventually_lt_nhds hUmax).and hsmall).exists_gt
  refine ⟨W, hW, hWmax.le, ?_, ?_⟩
  · have hg : 0 ≤ (4 * P + 2 * L / ρ ^ 2) * N * W ^ d / d := by positivity
    have hs' : 0 ≤ 2 * H * (C * A * W ^ (1 / q) + G * W ^ s / s) := by positivity
    dsimp only [F] at hFW
    linarith only [hg, hs', hFW]
  intro U V R φ₀ e Λ hU hV hUR f hf vOut x hx hUW hfn γ hγc hγa hγl hscale hentry hlam hgeom hψ u hu v huv
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (u : ℝ) :=
    (show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and
      ((eventually_lt_nhds hu).filter_mono nhdsWithin_le_nhds)
  obtain ⟨z₀, hz₀, hzV⟩ := (hnear.and (hγl.eventually (eventually_gt_atTop (v : ℝ)))).exists
  have hsub : Icc z₀ (u : ℝ) ⊆ Ioc 0 U :=
    fun _ ht => ⟨hz₀.1.trans_le ht.1, ht.2.trans u.property.2⟩
  obtain ⟨z, hz, hzt⟩ := intermediate_value_Icc' hz₀.2.le (hγc.mono hsub) ⟨huv, hzV.le⟩
  let z' : Icc 0 U := ⟨z, (hsub hz).1.le, (hsub hz).2⟩
  have hz0 := (hsub hz).1
  have hlate (t : ℝ) (ht : t ∈ Icc z u) : γ t ≤ v :=
    (hγa.antitoneOn (hsub hz) ⟨hz0.trans_le ht.1, ht.2.trans u.property.2⟩ ht.1).trans_eq hzt
  have hbound := hx.late_conformal_bound hU.le hV hUR hp hpq hf hρ hN hL hH hP hC hG hd hs
    z' u hz0 hz.2 v (by
      intro w hw
      have hg := hgeom w (hz0.trans_le hw.1) v (hlate w hw)
      exact ⟨hg.1, hg.2.1, hg.2.2.1, hlam z' w hz0 hw.1 v hzt, hg.2.2.2⟩) (by
      filter_upwards [hψ] with t ht
      intro htm
      exact ht v (hz0.trans_le htm.1) (hlate t htm))
  have hgamma : |x.2.1 z' v 2 + 2 * k| ≤ E * j ^ (-(τ / a)) * W ^ (τ / a) := by
    have hsc : j ≤ z * Real.exp (a * (v : ℝ)) := by simpa only [hzt] using hscale z (hsub hz)
    have he := (arrival_exp_power ha hz0 hj hτ.le hsc).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz0.le ((hsub hz).2.trans hUW) hta.le) (by positivity))
    exact ((hentry z' hz0 v hzt).trans (mul_le_mul_of_nonneg_left he hE)).trans_eq (by ring)
  have hgeomW := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hU.le hUW hd.le) (by positivity : 0 ≤ (4 * P + 2 * L / ρ ^ 2) * N)) hd.le
  have hscalarW := add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hfn hC)
    (Real.rpow_le_rpow hU.le hUW hb.le) (by positivity) (by positivity))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hU.le hUW hs.le) hG) hs.le)
  have hh := (abs_add_le (x.2.1 u v 2 - x.2.1 z' v 2) (x.2.1 z' v 2 + 2 * k)).trans
    (add_le_add (hbound.trans (add_le_add hgeomW
      (mul_le_mul_of_nonneg_left hscalarW (by positivity)))) hgamma)
  rw [← add_assoc, sub_add_cancel] at hh
  exact hh.trans_lt (by dsimp only [F] at hFW; linarith only [hFW])

end CauchyHorizon
