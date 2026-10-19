import CauchyHorizon.Characteristic.FiniteGeometry

/-! Radius and outgoing radial estimates retain the small outer width. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.horizon_outer_radial {M e Λ U V a d ρ R rmin N P H δ : ℝ} {h r : ℝ → ℝ}
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
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hρ : 0 < ρ) (hR : ρ ≤ R) (hN : 0 ≤ N) (hP : 0 ≤ P) (hH : 0 ≤ H)
    (hpot : ∀ t ∈ Icc ρ R, |radialPotential t e Λ| ≤ P)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (haxis : ∀ v : Icc 0 V, r v ∈ Icc rmin R)
    (hν : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ N * Real.exp (a * v))
    (hout : ∀ v : Icc 0 V, |horizonFunction (r v) (horizonMass M h v) e Λ| ≤ H * Real.exp (-d * v))
    (hwidth : U * Real.exp (a * V) ≤ δ) (u : Icc 0 U) (v : Icc 0 V) :
    0 ≤ r v - x.1 u v 0 ∧ r v - x.1 u v 0 ≤ N * u * Real.exp (a * v) ∧
      rmin - N * δ ≤ x.1 u v 0 ∧ x.1 u v 0 ≤ R ∧
      |x.2.1 u v 0| ≤ (R * H / ρ) * Real.exp (-d * v) + (4 * R * P * N / ρ) * u * Real.exp (a * v) ∧
      |x.2.1 u v 0| ≤ R * H / ρ + (4 * R * P * N / ρ) * δ := by
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hRp : 0 ≤ R := hρ.le.trans hR
  have hn (u : Icc 0 U) (v : Icc 0 V) : ν u v < 0 :=
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1
  have hOmega (u : Icc 0 U) (v : Icc 0 V) : Real.exp (x.1 u v 2) ≤ -4 * ν u v := by
    have hk := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.2.2
    have hh := (div_le_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) (hn u v))).1 hk
    linarith only [hh]
  have htr := (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2
  have hax (v : Icc 0 V) : x.1 ⟨0, le_rfl, hU⟩ v 0 ≤ R := by
    rw [htr v]
    exact (haxis v).2
  have hinu := (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1
  have hg := hx.radial_gap_weighted_bound hx.choose rfl hinu (fun u v => (hn u v).le) hν u v
  rw [htr v] at hg
  change 0 ≤ r v - x.1 u v 0 ∧ r v - x.1 u v 0 ≤ N * u * Real.exp (a * v) at hg
  have hf := hx.radial_flux_gap_bound hx.choose rfl hinu hρ hR hP hpot hlo hax
    (fun u v => (hn u v).le) hOmega u v
  have hgap : u * Real.exp (a * v) ≤ δ :=
    (mul_le_mul u.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 ha))
      (Real.exp_pos _).le hU).trans hwidth
  have hrmin : rmin - N * δ ≤ x.1 u v 0 := by
    have hh := mul_le_mul_of_nonneg_left hgap hN
    have hm := (haxis v).1
    nlinarith only [hg.2, hh, hm]
  have hl : |x.2.1 u v 0| ≤ (R * H / ρ) * Real.exp (-d * v) +
      (4 * R * P * N / ρ) * u * Real.exp (a * v) := by
    apply hf.2.2.trans
    rw [htr v]
    change (R * |horizonFunction (r v) (horizonMass M h v) e Λ| + 4 * R * P *
      (r v - x.1 u v 0)) / ρ ≤ _
    have hb := add_le_add (mul_le_mul_of_nonneg_left (hout v) hRp)
      (mul_le_mul_of_nonneg_left hg.2 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hRp) hP))
    exact (div_le_div_of_nonneg_right hb hρ.le).trans_eq (by ring)
  refine ⟨hg.1, hg.2, hrmin, hf.1, hl, hl.trans ?_⟩
  have he : Real.exp (-d * v) ≤ 1 := Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hd) v.property.1)
  have hv := mul_le_mul_of_nonneg_left he (div_nonneg (mul_nonneg hRp hH) hρ.le)
  have hw := mul_le_mul_of_nonneg_left hgap
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hRp) hP) hN) hρ.le)
  nlinarith only [hv, hw]

end CauchyHorizon
