import CauchyHorizon.Characteristic.OuterClosure
import CauchyHorizon.Characteristic.FiniteUniqueness

/-! Every finite prefix of a uniformly thin outer region has its physical solution. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_horizon_outer_wave {M e Λ a c ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
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
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        c ≤ a * (1 - 1 / p.toReal) → U * Real.exp (a * V) ≤ δ →
        ∃! x : WaveState U V, ∃ hx : IsWaveIntegral hU hV e Λ
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x,
          ∀ (u : Icc 0 U) (v : Icc 0 V),
            let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
            7 * ρ / 4 ≤ x.1 u v 0 ∧ x.1 u v 0 ≤ R ∧ |x.2.1 u v 0| ≤ L ∧
              ((9 / 16) * nH) * Real.exp (a * v) ≤ -ν u v ∧
              -ν u v ≤ ((5 / 3) * NH) * Real.exp (a * v) := by
  obtain ⟨δ₀, L, hδ₀, hδ₀1, hδ₀r, hL, hb⟩ := exists_horizon_outer_bounds
    hc hi hrc hr0 hφ hrd ha hc0 hac hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  have hrp : 0 < r 0 := by
    have hh := (haxis 0 (by simp only [mem_Ici, le_refl])).1
    linarith only [hh, hρ]
  obtain ⟨d₀, hd₀, _hd₀r, _hd₀1, hstart⟩ :=
    exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0 hrp hφ hrd A hA
  let δ := min δ₀ d₀
  have hδ : 0 < δ := lt_min hδ₀ hd₀
  refine ⟨δ, L, hδ, (min_le_left _ _).trans hδ₀1, (min_le_left _ _).trans hδ₀r, hL, ?_⟩
  intro U V hU hV hUR p hp f hf hfn hcb hwidth
  have hUδ : U ≤ δ := (le_mul_of_one_le_right hU
    (Real.one_le_exp_iff.2 (mul_nonneg ha.le hV))).trans hwidth
  have hU1 : U ≤ 1 := hUδ.trans ((min_le_left _ _).trans hδ₀1)
  have hw (t : ℝ) (ht : t ≤ V) : U * Real.exp (a * t) ≤ δ₀ :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht ha.le)) hU).trans
      (hwidth.trans (min_le_left _ _))
  obtain ⟨d, hd, _hd1, hext⟩ := exists_horizon_row_extension hV hrp hc hi hrc hr0 hφ hrd hρ hA
  let P := fun t : ℝ => ∃ ht : 0 ≤ t, ∃ x : WaveState U t,
    IsWaveIntegral hU ht e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ t hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x
  have hbase : P 0 := by
    obtain ⟨x, hx, _⟩ := hstart hU le_rfl hUR (hUδ.trans (min_le_right _ _)) hd₀.le hp hf hfn
    exact ⟨le_rfl, x, hx⟩
  have hstep (t s : ℝ) (_ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s ≤ V) (hsd : s ≤ d)
      (hP : P t) : P (t + s) := by
    obtain ⟨ht, x, hx⟩ := hP
    have hrx (u : Icc 0 U) (v : Icc 0 t) : ρ ≤ x.1 u v 0 := by
      have hh := (hb U t hU ht hUR p hp f hf x hx hfn hcb (hw t (by linarith only [hts, hs])) u v).1
      linarith only [hh, hρ]
    obtain ⟨y, hy, _, _⟩ := hext hU ht hs hU1 hsd hts hUR hp hf hfn hx hrx
    exact ⟨add_nonneg ht hs, y, hy⟩
  obtain ⟨_ht, x, hx⟩ := interval_subdivision_induction hV hd hbase hstep
  refine ⟨x, ⟨hx, hb U V hU hV hUR p hp f hf x hx hfn hcb (hw V le_rfl)⟩, ?_⟩
  intro y hy
  obtain ⟨hy, _⟩ := hy
  exact hy.incoming_unique hU hV hUR hp hf hx

end CauchyHorizon
