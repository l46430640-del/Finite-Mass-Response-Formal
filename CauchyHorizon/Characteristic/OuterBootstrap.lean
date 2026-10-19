import CauchyHorizon.Characteristic.OuterNu
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Outer bootstrap parameters are chosen before the incoming scalar data. -/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CauchyHorizon

theorem incoming_exponent_bounds {p : ℝ≥0∞} (hp : 4 ≤ p) :
    (3 / 4 : ℝ) ≤ 1 - 1 / p.toReal ∧ (1 / 2 : ℝ) ≤ 1 - 2 / p.toReal := by
  by_cases ht : p = ∞
  · simp only [ht, ENNReal.toReal_top, div_zero, sub_zero]
    norm_num
  · have hp' : (4 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono ht hp
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 4) hp'
    have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 4) hp'
    norm_num only [one_div] at h1
    norm_num only [show (2 : ℝ) / 4 = 1 / 2 by norm_num] at h2
    rw [one_div]
    constructor <;> linarith only [h1, h2]

theorem exists_small_outer_width {r₀ ρ ε : ℝ} (hr₀ : 0 < r₀) (hρ : 0 < ρ) (hε : 0 < ε)
    (N W C D : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ r₀ / 4 ∧ N * δ ≤ ρ / 4 ∧ W * δ ≤ 1 / 2 ∧
      C * δ ^ (1 / 2 : ℝ) + D * δ ≤ ε := by
  have hpow := Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hc : Continuous (fun δ : ℝ => C * δ ^ (1 / 2 : ℝ) + D * δ) :=
    (hpow.const_mul C).add (continuous_id.const_mul D)
  have h1 : ∀ᶠ δ : ℝ in 𝓝 0, δ < 1 := eventually_lt_nhds zero_lt_one
  have h2 : ∀ᶠ δ : ℝ in 𝓝 0, δ < r₀ / 4 := eventually_lt_nhds (by positivity)
  have h3 : ∀ᶠ δ : ℝ in 𝓝 0, N * δ < ρ / 4 :=
    (continuous_id.const_mul N).continuousAt.tendsto.eventually_lt_const (by simpa using div_pos hρ (by norm_num : (0 : ℝ) < 4))
  have h4 : ∀ᶠ δ : ℝ in 𝓝 0, W * δ < 1 / 2 :=
    (continuous_id.const_mul W).continuousAt.tendsto.eventually_lt_const (by norm_num)
  have h5 : ∀ᶠ δ : ℝ in 𝓝 0, C * δ ^ (1 / 2 : ℝ) + D * δ < ε :=
    hc.continuousAt.tendsto.eventually_lt_const (by simpa using hε)
  obtain ⟨δ, hδ, hb⟩ := (h1.and (h2.and (h3.and (h4.and h5)))).exists_gt
  exact ⟨δ, hδ, hb.1.le, hb.2.1.le, hb.2.2.1.le, hb.2.2.2.1.le, hb.2.2.2.2.le⟩

theorem exists_horizon_outer_bootstrap {M e Λ a c ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
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
        (∀ u v, ρ ≤ x.1 u v 0) →
        (∀ (u : Icc 0 U) (v : Icc 0 V), (nH / 2) * Real.exp (a * v) ≤
          -radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v) →
        (∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          x.1 hx.choose u v| ≤ (2 * NH) * Real.exp (a * v)) →
        ∀ (u : Icc 0 U) (v : Icc 0 V),
          let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          7 * ρ / 4 ≤ x.1 u v 0 ∧ x.1 u v 0 ≤ R ∧ |x.2.1 u v 0| ≤ L ∧
            ((9 / 16) * nH) * Real.exp (a * v) ≤ -ν u v ∧
            -ν u v ≤ ((5 / 3) * NH) * Real.exp (a * v) := by
  have haxis0 := haxis 0 (by simp only [mem_Ici, le_refl])
  have hrp : 0 < r 0 := hρ.trans_le (by linarith only [haxis0.1, hρ])
  have hρR : ρ ≤ R := by linarith only [haxis0.1, haxis0.2, hρ]
  have hR : 0 ≤ R := hρ.le.trans hρR
  obtain ⟨P, hP, hpot⟩ := radialPotential_bounded e Λ (R := R) hρ
  obtain ⟨J, hlip⟩ := radialPotential_lipschitzOn (R := R) (e := e) (Λ := Λ) hρ
  let n := nH / 2
  let N := 2 * NH
  let L := R * W / ρ + 4 * R * P * N / ρ
  let E₀ := 2 * (H + L * (r 0 / ρ) * A) / ρ
  let β₀ := N / (ρ * (a - c)) * E₀
  let C := (8 * P * R / n) * (r 0 / ρ) ^ 2 * A ^ 2
  let D := (8 * P * R / n) * β₀ ^ 2 + 4 * J * N
  have hn : 0 < n := by dsimp only [n]; positivity
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  obtain ⟨δ, hδ, hδ1, hδr, hδρ, hδsmall, hδerr⟩ :=
    exists_small_outer_width hrp hρ
      (mul_pos ha (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)))
      N (L * N / (ρ ^ 2 * (a - c))) C D
  refine ⟨δ, L, hδ, hδ1, hδr, hL, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb hwidth hlo hνlo hνhi u v
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let E := 2 * (H + L * (r 0 / ρ) * (A * δ ^ (1 - 1 / p.toReal))) / ρ
  let β := N / (ρ * (a - c)) * E
  let ε := (C * (u : ℝ) ^ (1 - 2 / p.toReal) + ((8 * P * R / n) * β ^ 2 + 4 * J * N) * δ) / a
  let S := -horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v
  have hrad (q : Icc 0 U) (w : Icc 0 V) := hx.horizon_outer_radial (d := 0)
    hU hV hUR hc hi hrc hr0 hφ hrd hp hf ha.le le_rfl hρ hρR hN hP hW hpot hlo
    (fun t => haxis t t.property.1) hνhi (fun t => by simpa using hlout t t.property.1) hwidth q w
  have hrhi (q : Icc 0 U) (w : Icc 0 V) : x.1 q w 0 ≤ R := (hrad q w).2.2.2.1
  have hlam (q : Icc 0 U) (w : Icc 0 V) : |x.2.1 q w 0| ≤ L := by
    apply (hrad q w).2.2.2.2.2.trans
    exact add_le_add le_rfl (mul_le_of_le_one_right (by positivity) hδ1)
  have hsmall : L * N * δ / (ρ ^ 2 * (a - c)) ≤ 1 / 2 := by
    simpa only [div_mul_eq_mul_div] using hδsmall
  have hb := hx.horizon_outer_nu_comparison hU hV hUR hc hi hrc hr0 hφ hrd hp hf
    hA hfn ha hc0 hac hcb hρ hR hn hN hL hH hδ.le hP hpot hlip hlo hrhi hνlo hνhi hlam
    (fun t => hout t t.property.1) hwidth hsmall u v
  change _ ≤ ε ∧ ((r 0 - (u : ℝ)) / r 0) * S * Real.exp (-ε) ≤ -ν u v ∧
    -ν u v ≤ (1 + N * δ / ρ) * S * Real.exp ε at hb
  have huδ : (u : ℝ) ≤ δ := u.property.2.trans ((le_mul_of_one_le_right hU
    (Real.one_le_exp_iff.2 (mul_nonneg ha.le hV))).trans hwidth)
  have hu : 0 ≤ (u : ℝ) := u.property.1
  obtain ⟨hb1, hb2⟩ := incoming_exponent_bounds hp
  have hpow : δ ^ (1 - 1 / p.toReal) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by linarith only [hb1])
  have hE : E ≤ E₀ := by
    dsimp only [E, E₀]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hA hpow)
        (mul_nonneg hL (div_nonneg hrp.le hρ.le)))) (by norm_num)) hρ.le
  have hβ : β ≤ β₀ := mul_le_mul_of_nonneg_left hE (by positivity)
  have hβ0 : 0 ≤ β := by dsimp only [β, E]; positivity
  have hupow : (u : ℝ) ^ (1 - 2 / p.toReal) ≤ δ ^ (1 / 2 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge' hu (huδ.trans hδ1) (by norm_num) hb2).trans
      (Real.rpow_le_rpow hu huδ (by norm_num))
  have heps : ε ≤ Real.log (4 / 3) := by
    apply (div_le_iff₀ ha).2
    have hbsq : β ^ 2 ≤ β₀ ^ 2 := sq_le_sq₀ hβ0 (hβ0.trans hβ) |>.2 hβ
    have hcoeff := mul_le_mul_of_nonneg_left hbsq (by positivity : 0 ≤ 8 * P * R / n)
    have hD := mul_le_mul_of_nonneg_right (add_le_add hcoeff (le_refl (4 * J * N))) hδ.le
    have hh := add_le_add (mul_le_mul_of_nonneg_left hupow hC) hD
    exact hh.trans (hδerr.trans_eq (mul_comm _ _))
  have hS : 0 ≤ S := (neg_pos.2 (horizon_normalization _ (v : ℝ)).1).le
  have hinit : (3 / 4 : ℝ) ≤ (r 0 - (u : ℝ)) / r 0 := by
    apply (le_div_iff₀ hrp).2
    linarith only [huδ.trans hδr]
  have hgeom : 1 + N * δ / ρ ≤ (5 / 4 : ℝ) := by
    have hh : N * δ / ρ ≤ (1 / 4 : ℝ) := (div_le_iff₀ hρ).2 (by linarith only [hδρ])
    linarith only [hh]
  have hel : (3 / 4 : ℝ) ≤ Real.exp (-ε) := by
    have hh := Real.exp_le_exp.2 (neg_le_neg heps)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at hh
    norm_num only at hh
    exact hh
  have heu : Real.exp ε ≤ (4 / 3 : ℝ) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] using Real.exp_le_exp.2 heps
  have hlow := mul_le_mul (mul_le_mul_of_nonneg_right hinit hS) hel (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (mul_nonneg ((by norm_num : (0 : ℝ) ≤ 3 / 4).trans hinit) hS)
  have hhigh := mul_le_mul (mul_le_mul_of_nonneg_right hgeom hS) heu (Real.exp_pos _).le
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4) hS)
  have hslo := mul_le_mul_of_nonneg_left (hνaxis v v.property.1).1 (by norm_num : (0 : ℝ) ≤ 9 / 16)
  have hshi := mul_le_mul_of_nonneg_left (hνaxis v v.property.1).2 (by norm_num : (0 : ℝ) ≤ 5 / 3)
  refine ⟨?_, hrhi u v, hlam u v, ?_, ?_⟩
  · linarith only [(hrad u v).2.2.1, hδρ]
  · nlinarith only [hlow, hb.2.1, hslo]
  · nlinarith only [hhigh, hb.2.2, hshi]

end CauchyHorizon
