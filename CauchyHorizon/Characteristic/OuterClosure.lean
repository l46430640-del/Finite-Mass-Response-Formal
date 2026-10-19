import CauchyHorizon.Characteristic.OuterBootstrap
import CauchyHorizon.Characteristic.PrefixData
import CauchyHorizon.Reduced.RadialRestriction
import CauchyHorizon.Analysis.PrefixBootstrap

/-! The outer bootstrap assumptions are removed on every existing thin rectangle. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_horizon_outer_bounds {M e Λ a c ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (ha : 0 < a) (hc0 : 0 ≤ c) (hac : c < a) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (c * t) * |h t| ≤ H)
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass M h t) e Λ| ≤ W) :
    ∃ δ L : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧ 0 ≤ L ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        c ≤ a * (1 - 1 / p.toReal) → U * Real.exp (a * V) ≤ δ →
        ∀ (u : Icc 0 U) (v : Icc 0 V),
          let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          7 * ρ / 4 ≤ x.1 u v 0 ∧ x.1 u v 0 ≤ R ∧ |x.2.1 u v 0| ≤ L ∧
            ((9 / 16) * nH) * Real.exp (a * v) ≤ -ν u v ∧
            -ν u v ≤ ((5 / 3) * NH) * Real.exp (a * v) := by
  obtain ⟨δ, L, hδ, hδ1, hδr, hL, himprove⟩ := exists_horizon_outer_bootstrap
    hc hi hrc hr0 hφ hrd ha hc0 hac hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, L, hδ, hδ1, hδr, hL, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb hwidth
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let Q := fun z : ℝ × Icc 0 V => -intervalExtension hU ν z.1 z.2 / Real.exp (a * z.2)
  let G := fun z : ℝ × Icc 0 V => max (ρ - intervalExtension hU x.1 z.1 z.2 0)
    (max (nH / 2 - Q z) (Q z - 2 * NH))
  have hnc := (intervalExtension hU ν).continuous
  have hxc := (intervalExtension hU x.1).continuous
  have hQ : Continuous Q := by
    apply Continuous.div ?_ (by fun_prop) (fun _ => Real.exp_ne_zero _)
    fun_prop
  have hG : Continuous G := by dsimp only [G]; fun_prop
  have hdecode (q : Icc 0 U) (v : Icc 0 V) (hg : G (q, v) ≤ 0) :
      ρ ≤ x.1 q v 0 ∧ (nH / 2) * Real.exp (a * v) ≤ -ν q v ∧
        |ν q v| ≤ (2 * NH) * Real.exp (a * v) := by
    simp only [G, Q, intervalExtension_apply, projIcc_of_mem hU q.property, max_le_iff,
      sub_nonpos] at hg
    refine ⟨hg.1, (le_div_iff₀ (Real.exp_pos _)).1 hg.2.1, ?_⟩
    rw [abs_of_neg (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf q v).2.2.1]
    exact (div_le_iff₀ (Real.exp_pos _)).1 hg.2.2
  have hzero (v : Icc 0 V) : G (0, v) < 0 := by
    have hz : (0 : ℝ) ∈ Icc 0 U := ⟨le_rfl, hU⟩
    have htr := (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v
    have hntr := hx.horizon_radial_trace hU hV hUR hc hi hrc hr0 hφ hrd hp hf v
    have hq : nH ≤ Q (0, v) ∧ Q (0, v) ≤ NH := by
      dsimp only [Q]
      rw [intervalExtension_apply, projIcc_of_mem hU hz, hntr]
      exact ⟨(le_div_iff₀ (Real.exp_pos _)).2 (hνaxis v v.property.1).1,
        (div_le_iff₀ (Real.exp_pos _)).2 (hνaxis v v.property.1).2⟩
    simp only [G, intervalExtension_apply, projIcc_of_mem hU hz, htr, max_lt_iff]
    change ρ - r v < 0 ∧ nH / 2 - Q (0, v) < 0 ∧ Q (0, v) - 2 * NH < 0
    exact ⟨by linarith only [(haxis v v.property.1).1, hρ],
      by linarith only [hq.1, hnH], by linarith only [hq.2, hNH]⟩
  have hstrict : ∀ t ∈ Icc (0 : ℝ) U, ∀ v, G (t, v) < 0 := by
    apply continuous_prefix_bootstrap hG hzero
    intro t ht hpref v
    let τ := intervalTranslate (a := 0) (U := t) le_rfl (show 0 + t ≤ U by simpa using ht.2)
    let hfT := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl)
    let y := waveTranslate (a := 0) (U := t) (b := 0) (V := V) le_rfl
      (show 0 + t ≤ U by simpa using ht.2) le_rfl (show 0 + V ≤ V by simp) x
    have hy := hx.horizon_prefix hU hV hUR ht.1 hV ht.2 le_rfl hc hi hrc hr0 hp hf
    have hzy : y.1 = x.1.comp τ := by
      ext q w i
      change x.1 (τ q) (intervalTranslate (a := 0) le_rfl (show 0 + V ≤ V by simp) w) i = x.1 (τ q) w i
      rw [intervalTranslate_zero, ContinuousMap.id_apply]
    have hny : radialNuField hV e Λ
        (incomingWaveCurve ht.1 (ht.2.trans_lt hUR) hp hfT (horizonPhi h r 0)) y.1 hy.choose = ν.comp τ := by
      have hzi : (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)).comp τ =
          incomingWaveCurve ht.1 (ht.2.trans_lt hUR) hp hfT (horizonPhi h r 0) :=
        incomingWaveCurve_prefix hU ht.1 hUR ht.2 hp hf hfT _
      simpa only [hzi, ← hzy] using
        radialNuField_comp_left hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose τ
    have hb (q : Icc 0 t) (w : Icc 0 V) := hdecode (τ q) w
      (hpref (τ q) (by change 0 + (q : ℝ) ∈ Icc 0 t; simpa only [zero_add] using q.property) w)
    have hb' (q : Icc 0 t) (w : Icc 0 V) :
        ρ ≤ y.1 q w 0 ∧ (nH / 2) * Real.exp (a * w) ≤
          -radialNuField hV e Λ (incomingWaveCurve ht.1 (ht.2.trans_lt hUR) hp hfT (horizonPhi h r 0)) y.1 hy.choose q w ∧
        |radialNuField hV e Λ (incomingWaveCurve ht.1 (ht.2.trans_lt hUR) hp hfT (horizonPhi h r 0)) y.1 hy.choose q w| ≤
          (2 * NH) * Real.exp (a * w) := by
      rw [hny, hzy]
      exact hb q w
    have hw : t * Real.exp (a * V) ≤ δ :=
      (mul_le_mul_of_nonneg_right ht.2 (Real.exp_pos _).le).trans hwidth
    have hresult := himprove t V ht.1 hV (ht.2.trans_lt hUR) p hp f hfT y hy
      ((scalar_prefix_norm_le ht.2 hf).trans hfn) hcb hw
      (fun q w => (hb' q w).1) (fun q w => (hb' q w).2.1) (fun q w => (hb' q w).2.2)
      ⟨t, ht.1, le_rfl⟩ v
    have htop : τ ⟨t, ht.1, le_rfl⟩ = ⟨t, ht⟩ := Subtype.ext (zero_add _)
    have hr : 7 * ρ / 4 ≤ x.1 ⟨t, ht⟩ v 0 := by
      simpa only [hzy, ContinuousMap.comp_apply, htop] using hresult.1
    have hnl : (9 / 16) * nH ≤ Q (t, v) := by
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa only [hny, ContinuousMap.comp_apply, htop, Q, intervalExtension_apply, projIcc_of_mem hU ht]
        using hresult.2.2.2.1
    have hnh : Q (t, v) ≤ (5 / 3) * NH := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      simpa only [hny, ContinuousMap.comp_apply, htop, Q, intervalExtension_apply, projIcc_of_mem hU ht]
        using hresult.2.2.2.2
    simp only [G, intervalExtension_apply, projIcc_of_mem hU ht, max_lt_iff]
    exact ⟨by linarith only [hr, hρ], by linarith only [hnl, hnH], by linarith only [hnh, hNH]⟩
  exact himprove U V hU hV hUR p hp f hf x hx hfn hcb hwidth
    (fun q v => (hdecode q v (hstrict q q.property v).le).1)
    (fun q v => (hdecode q v (hstrict q q.property v).le).2.1)
    (fun q v => (hdecode q v (hstrict q q.property v).le).2.2)

end CauchyHorizon
