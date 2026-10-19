import CauchyHorizon.Characteristic.OuterRadiation
import CauchyHorizon.Reduced.MovingRadiation
import CauchyHorizon.Characteristic.PhysicalOverlapNu

/-! The physical causal estimate holds for one continuous moving-domain envelope. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_horizon_moving_outer_radiation {m e Λ a k ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (hk : 0 ≤ k) (hka : k < a) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (k * t) * |h t| ≤ H)
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass m h t) e Λ| ≤ W) :
    ∃ (δ L N : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧ 0 ≤ L ∧ 0 < N ∧
      L * N * δ / (ρ ^ 2 * (a - k)) ≤ 1 / 4 ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        k ≤ a * (1 - 1 / p.toReal) →
        let M := outerRadiationEnvelope hδ.le a k x
        ∀ v : Icc 0 V, (M v ≤ Real.exp (k * v) * |h v| +
          (L * r 0 / ρ) * Real.exp (k * v) *
            (∫ t in (0 : ℝ)..min U (δ * Real.exp (-a * v)), |f t|) +
          (L * N * δ / ρ ^ 2) * causalExpIntegral hV (a - k) M v) ∧
          ∀ u : Icc 0 U, (u : ℝ) ≤ δ * Real.exp (-a * v) →
            (u : ℝ) * Real.exp (k * v) * |scalarTransportCorrection hV
              (radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
                x.1 hx.choose) x.2.1 u v| ≤
              (N * δ / ρ) * causalExpIntegral hV (a - k) M v := by
  obtain ⟨δ, L, N, hδ, hδ1, hδr, hL, hN, hsmall, hb⟩ :=
    exists_horizon_outer_radiation_kernel hc hi hrc hr0 hφ hrd hk hka hρ
      hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, L, N, hδ, hδ1, hδr, hL, hN, hsmall, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hkp M v
  let S := min U (δ * Real.exp (-a * v))
  have hS : 0 ≤ S := le_min hU (mul_nonneg hδ.le (Real.exp_pos _).le)
  have hSU : S ≤ U := min_le_left _ _
  have hSR : S < r 0 := hSU.trans_lt hUR
  have hSe : S * Real.exp (a * v) ≤ δ := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right U (δ * Real.exp (-a * v)))
      (Real.exp_pos (a * v)).le
    simpa only [S, mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] using hh
  let hfS := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hSU) le_rfl)
  let y := waveTranslate (a := 0) (U := S) (b := 0) (V := (v : ℝ))
    le_rfl (by linarith) le_rfl (by linarith only [v.property.2]) x
  have hy : IsWaveIntegral hS v.property.1 e Λ
      (incomingWaveCurve hS hSR hp hfS (horizonPhi h r 0))
      (horizonWaveVelocity m e Λ (v : ℝ) hc hi hrc hr0) (incomingWaveVelocity hSR hp hfS) y :=
    hx.horizon_prefix hU hV hUR hS v.property.1 hSU v.property.2 hc hi hrc hr0 hp hf
  let j : C(Icc 0 (v : ℝ), Icc 0 V) :=
    ⟨fun t => ⟨t, t.property.1, t.property.2.trans v.property.2⟩, by fun_prop⟩
  have hj (t : Icc 0 (v : ℝ)) : δ * Real.exp (-a * v) ≤ δ * Real.exp (-a * (j t)) := by
    apply mul_le_mul_of_nonneg_left _ hδ.le
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonpos_left t.property.2 (neg_nonpos.2 (hk.trans hka.le))
  have hM (u : Icc 0 S) (t : Icc 0 (v : ℝ)) :
      Real.exp (k * t) * |y.1 u t 0 * y.2.1 u t 1| ≤ (M.comp j) t := by
    have hh := (outerRadiationEnvelope_le_iff (k := k) hU hδ.le x (j t)).1 le_rfl
      ⟨u, u.property.1, u.property.2.trans hSU⟩
      (u.property.2.trans ((min_le_right _ _).trans (hj t)))
    change Real.exp (k * t) *
      |x.1 ⟨0 + u, by simpa using u.property.1, by simpa using u.property.2.trans hSU⟩
          ⟨0 + t, by simpa using t.property.1, by simpa using t.property.2.trans v.property.2⟩ 0 *
        x.2.1 ⟨0 + u, by simpa using u.property.1, by simpa using u.property.2.trans hSU⟩
          ⟨0 + t, by simpa using t.property.1, by simpa using t.property.2.trans v.property.2⟩ 1| ≤ _
    simpa only [M, j, ContinuousMap.comp_apply, ContinuousMap.coe_mk, zero_add] using hh
  have hkern := hb S v hS v.property.1 hSR p hp f hfS y hy
    ((scalar_prefix_norm_le hSU hf).trans hfn) hkp hSe (M.comp j) hM
  have hQ := causalExpIntegral_prefix hV v.property.1 v.property.2 (d := a - k) M
  have hfi : IntervalIntegrable (fun t => |f t|) volume 0 S := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hS).2
    exact (hfS.integrable ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp)).abs
  constructor
  · apply (outerRadiationEnvelope_le_iff hU hδ.le x v).2
    intro u hu
    have huS : (u : ℝ) ≤ S := le_min u.property.2 hu
    have hbnd := hkern.2 ⟨u, u.property.1, huS⟩ ⟨v, v.property.1, le_rfl⟩
    rw [hQ] at hbnd
    change Real.exp (k * v) *
      |x.1 ⟨0 + u, by simpa using u.property.1, by simpa using u.property.2⟩
          ⟨0 + v, by simpa using v.property.1, by simpa using v.property.2⟩ 0 *
        x.2.1 ⟨0 + u, by simpa using u.property.1, by simpa using u.property.2⟩
          ⟨0 + v, by simpa using v.property.1, by simpa using v.property.2⟩ 1| ≤ _ at hbnd
    simp only [zero_add] at hbnd
    have hint := intervalIntegral.integral_mono_interval le_rfl u.property.1 huS
      (Filter.Eventually.of_forall (fun t => abs_nonneg (f t))) hfi
    have hcoeff : 0 ≤ (L * r 0 / ρ) * Real.exp (k * v) := by
      have hrpos : 0 < r 0 := hU.trans_lt hUR
      positivity
    exact hbnd.trans (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hint hcoeff)) le_rfl)
  · intro u hu
    have huS : (u : ℝ) ∈ Icc 0 S := ⟨u.property.1, le_min u.property.2 hu⟩
    have hbnd := hkern.1 ⟨u, huS⟩ ⟨v, v.property.1, le_rfl⟩
    rw [hQ] at hbnd
    have he : scalarTransportCorrection v.property.1
        (radialNuField v.property.1 e Λ (incomingWaveCurve hS hSR hp hfS (horizonPhi h r 0))
          y.1 hy.choose) y.2.1 ⟨u, huS⟩ ⟨v, v.property.1, le_rfl⟩ =
        scalarTransportCorrection hV
          (radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            x.1 hx.choose) x.2.1 u v := by
      change (∫ t in (0 : ℝ)..v, _) = ∫ t in (0 : ℝ)..v, _
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le v.property.1] at ht
      have htV : t ∈ Icc 0 V := ⟨ht.1, ht.2.trans v.property.2⟩
      have hn := hy.horizon_overlap_nu hS v.property.1 hSR hU hV hUR hc hi hrc hr0 hp hfS hf hx
        huS u.property ht htV
      have hw := (hy.horizon_overlap hS v.property.1 hSR hU hV hUR hc hi hrc hr0 hp hfS hf hx
        huS u.property ht htV).2
      simp only [intervalExtension_apply, projIcc_of_mem v.property.1 ht, projIcc_of_mem hV htV]
      change -radialNuField v.property.1 e Λ
          (incomingWaveCurve hS hSR hp hfS (horizonPhi h r 0)) y.1 hy.choose ⟨u, huS⟩ ⟨t, ht⟩ *
          y.2.1 ⟨u, huS⟩ ⟨t, ht⟩ 1 =
        -radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          x.1 hx.choose u ⟨t, htV⟩ * x.2.1 u ⟨t, htV⟩ 1
      rw [hn, hw]
    rwa [he] at hbnd

end CauchyHorizon
