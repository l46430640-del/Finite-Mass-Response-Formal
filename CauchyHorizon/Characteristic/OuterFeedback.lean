import CauchyHorizon.Characteristic.OuterClosure
import CauchyHorizon.Characteristic.PhysicalOverlapNu
import CauchyHorizon.Reduced.MovingRadiation
import CauchyHorizon.Reduced.ScalarFeedback

/-! The actual outer feedback is small in L2 on every curve in the moving outer region. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_horizon_outer_feedback_energy {m e Λ a k ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
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
    ∃ δ₀ L N : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ δ₀ ≤ r 0 / 4 ∧ 0 ≤ L ∧ 0 < N ∧
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ →
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
          (x : WaveState U V)
          (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
          (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
          k ≤ a * (1 - 1 / p.toReal) →
          let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let F := scalarRadiationFeedback hU hV x.1 x.2.1 ν hx.choose
          let M := outerRadiationEnvelope hδ.le a k x
          (∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ δ * Real.exp (-a * v) →
            Real.exp (k * v) * |F u v| ≤
              (L * N * δ / ρ ^ 2) * causalExpIntegral hV (a - k) M v) ∧
          ∀ (l S : ℝ) (g : ℝ → ℝ), 0 ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
            (∀ t ∈ Icc l S, g t ∈ Icc 0 U ∧ g t ≤ δ * Real.exp (-a * t)) →
            (∫ t in l..S, (Real.exp (k * t) * F (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2) ≤
              (L * N * δ / (ρ ^ 2 * (a - k))) ^ 2 *
                ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  have ha := hk.trans_lt hka
  obtain ⟨δ₀, L, hδ₀, hδ₀1, hδ₀r, hL, hb⟩ := exists_horizon_outer_bounds
    hc hi hrc hr0 hφ hrd ha hk hka hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  let N := (5 / 3) * NH
  have hN : 0 < N := by dsimp only [N]; positivity
  refine ⟨δ₀, L, N, hδ₀, hδ₀1, hδ₀r, hL, hN, ?_⟩
  intro δ hδ hδδ U V hU hV hUR p hp f hf x hx hfn hkp ν F M
  have hscale (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ δ * Real.exp (-a * v)) :
      (u : ℝ) * Real.exp (a * v) ≤ δ := by
    have hh := mul_le_mul_of_nonneg_right hu (Real.exp_pos (a * v)).le
    simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] using hh
  have hgeo (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ δ * Real.exp (-a * v)) :
      ρ ≤ x.1 u v 0 ∧ |x.2.1 u v 0| ≤ L ∧ -ν u v ≤ N * Real.exp (a * v) := by
    let hfS := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
    have huR : (u : ℝ) < r 0 := u.property.2.trans_lt hUR
    let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (v : ℝ))
      le_rfl (by linarith only [u.property.2]) le_rfl (by linarith only [v.property.2]) x
    have hy : IsWaveIntegral u.property.1 v.property.1 e Λ
        (incomingWaveCurve u.property.1 huR hp hfS (horizonPhi h r 0))
        (horizonWaveVelocity m e Λ (v : ℝ) hc hi hrc hr0) (incomingWaveVelocity huR hp hfS) y :=
      hx.horizon_prefix hU hV hUR u.property.1 v.property.1 u.property.2 v.property.2 hc hi hrc hr0 hp hf
    have hg := hb u v u.property.1 v.property.1 huR p hp f hfS y hy
      ((scalar_prefix_norm_le u.property.2 hf).trans hfn) hkp ((hscale u v hu).trans hδδ)
      ⟨u, u.property.1, le_rfl⟩ ⟨v, v.property.1, le_rfl⟩
    have he := hy.horizon_overlap u.property.1 v.property.1 huR hU hV hUR hc hi hrc hr0 hp hfS hf hx
      (show (u : ℝ) ∈ Icc 0 (u : ℝ) from ⟨u.property.1, le_rfl⟩) u.property
      (show (v : ℝ) ∈ Icc 0 (v : ℝ) from ⟨v.property.1, le_rfl⟩) v.property
    have hn := hy.horizon_overlap_nu u.property.1 v.property.1 huR hU hV hUR hc hi hrc hr0 hp hfS hf hx
      (show (u : ℝ) ∈ Icc 0 (u : ℝ) from ⟨u.property.1, le_rfl⟩) u.property
      (show (v : ℝ) ∈ Icc 0 (v : ℝ) from ⟨v.property.1, le_rfl⟩) v.property
    dsimp only at hg
    rw [he.1, he.2, hn] at hg
    exact ⟨by linarith only [hg.1, hρ], hg.2.2.1, hg.2.2.2.2⟩
  have hν (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ δ * Real.exp (-a * v)) :
      |ν u v| ≤ N * Real.exp (a * v) := by
    rw [abs_of_neg (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1]
    exact (hgeo u v hu).2.2
  have hin (u : Icc 0 U) : |incomingWaveCurve hU hUR hp hf (horizonPhi h r 0) u 0| ≤ r 0 := by
    rw [incomingWaveCurve_apply]
    change |r 0 - (u : ℝ)| ≤ r 0
    rw [abs_of_pos (sub_pos.2 (u.property.2.trans_lt hUR))]
    linarith only [u.property.1]
  have hB : Antitone (fun v : Icc 0 V => δ * Real.exp (-a * v)) := by
    intro v w hvw
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonpos_left hvw (neg_nonpos.2 ha.le))) hδ.le
  have hfb := hx.outer_feedback_kernel_on hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 hρ hN.le hL
    (fun v => δ * Real.exp (-a * v)) hB (fun u v hu => (hgeo u v hu).1) hin hν
    (fun u v hu => (hgeo u v hu).2.1) hscale M (outerRadiationEnvelope_nonneg hδ.le a k x)
    (fun u v hu => (outerRadiationEnvelope_le_iff hU hδ.le x v).1 le_rfl u hu)
  refine ⟨hfb, ?_⟩
  intro l S g hl hlS hSV hgc hg
  have hup : ContinuousOn (fun t => projIcc 0 U hU (g t)) (Icc l S) :=
    (continuous_projIcc (a := (0 : ℝ)) (b := U) (h := hU)).comp_continuousOn hgc
  have hvp : ContinuousOn (fun t : ℝ => projIcc 0 V hV t) (Icc l S) :=
    (continuous_projIcc (a := (0 : ℝ)) (b := V) (h := hV)).continuousOn
  have hFc : ContinuousOn (fun t => F (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) (Icc l S) := by
    have hh := F.uncurry.continuous.comp_continuousOn (hup.prodMk hvp)
    simpa only [Function.comp_def, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair] using hh
  have hEc : ContinuousOn (fun t => Real.exp (k * t) * F (projIcc 0 U hU (g t))
      (projIcc 0 V hV t)) (Icc l S) := by fun_prop
  have he := causalExpIntegral_dominated_energy hV (sub_pos.2 hka) hl hlS hSV M hEc
    (C := L * N * δ / ρ ^ 2) (fun t ht => ?_)
  · simpa only [div_div] using he
  · have htV : t ∈ Icc 0 V := ⟨hl.trans ht.1, ht.2.trans hSV⟩
    rw [abs_mul, abs_of_pos (Real.exp_pos _), projIcc_of_mem hU (hg t ht).1, projIcc_of_mem hV htV]
    exact hfb ⟨g t, (hg t ht).1⟩ ⟨t, htV⟩ (hg t ht).2

end CauchyHorizon
