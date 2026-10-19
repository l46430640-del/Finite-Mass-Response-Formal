import CauchyHorizon.Characteristic.OuterGeometry
import CauchyHorizon.Characteristic.OuterRadial
import CauchyHorizon.Analysis.ExponentialError

/-! Comparison of the actual radial flux with its horizon value. -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CauchyHorizon

theorem radialPotential_lipschitzOn {ρ R e Λ : ℝ} (hρ : 0 < ρ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun t => radialPotential t e Λ) (Icc ρ R) := by
  have hc : ContDiffOn ℝ 1 (fun t => radialPotential t e Λ) (Icc ρ R) := by
    intro t ht
    have ht0 : t ≠ 0 := (hρ.trans_le ht.1).ne'
    unfold radialPotential
    fun_prop (disch := positivity)
  exact hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc

variable {M e Λ U V : ℝ} {h r : ℝ → ℝ}
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

include hφ hrd hx

theorem IsWaveIntegral.horizon_radial_ratio (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let G := fun (q : Icc 0 U) (t : ℝ) => Real.exp (intervalExtension hV (x.1 q) t 2) *
      radialPotential (intervalExtension hV (x.1 q) t 0) e Λ / intervalExtension hV (N q) t
    let T := ((r 0 - (u : ℝ)) / r 0) * (r v / x.1 u v 0) *
      (-horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v)
    (-N u v) = T * Real.exp (∫ t in (0 : ℝ)..v, G u t - G ⟨0, le_rfl, hU⟩ t) := by
  let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let z : Icc 0 U := ⟨0, le_rfl, hU⟩
  let G := fun (q : Icc 0 U) (t : ℝ) => Real.exp (intervalExtension hV (x.1 q) t 2) *
    radialPotential (intervalExtension hV (x.1 q) t 0) e Λ / intervalExtension hV (N q) t
  have hn (q : Icc 0 U) (w : Icc 0 V) : N q w < 0 :=
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf q w).2.2.1
  have hGc (q : Icc 0 U) : Continuous (G q) :=
    ((continuous_apply (0 : Fin 3)).comp (intervalExtension hV (wavePotentialField e Λ (x.1 q) (hx.choose q))).continuous).div
      (intervalExtension hV (N q)).continuous (fun t => ne_of_lt (hn q (projIcc 0 V hV t)))
  have hfu := radialNuField_flux_exponential hx.choose (hx.incoming_radius_pos hU hV hUR hp hf) hn u v
  have hfz := radialNuField_flux_exponential hx.choose (hx.incoming_radius_pos hU hV hUR hp hf) hn z v
  dsimp only at hfu hfz
  rw [incomingWaveCurve_apply] at hfu
  change x.1 u v 0 * N u v = -(r 0 - (u : ℝ)) * Real.exp (∫ t in (0 : ℝ)..v, G u t) at hfu
  rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v,
    hx.horizon_radial_trace hU hV hUR hc hi hrc hr0 hφ hrd hp hf v, incomingWaveCurve_apply] at hfz
  change r v * horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v =
    -(r 0 - 0) * Real.exp (∫ t in (0 : ℝ)..v, G z t) at hfz
  have hzero : Real.exp (∫ t in (0 : ℝ)..v, G z t) =
      r v * (-horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v) / r 0 := by
    apply (eq_div_iff (hr0 0)).2
    nlinarith only [hfz]
  have hsplit : Real.exp (∫ t in (0 : ℝ)..v, G u t) =
      Real.exp (∫ t in (0 : ℝ)..v, G z t) * Real.exp (∫ t in (0 : ℝ)..v, G u t - G z t) := by
    rw [intervalIntegral.integral_sub ((hGc u).intervalIntegrable _ _) ((hGc z).intervalIntegrable _ _), Real.exp_sub]
    field_simp [Real.exp_ne_zero]
  change -N u v = _
  calc
    _ = -(x.1 u v 0 * N u v) / x.1 u v 0 := by field_simp [hx.choose u v]
    _ = ((r 0 - (u : ℝ)) * Real.exp (∫ t in (0 : ℝ)..v, G u t)) / x.1 u v 0 := by rw [hfu]; ring
    _ = _ := by rw [hsplit, hzero]; ring

theorem IsWaveIntegral.horizon_outer_nu_comparison {a c ρ R n N L H A δ P : ℝ} {J : ℝ≥0}
    (hA : 0 ≤ A) (hfn : (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A)
    (ha : 0 < a) (hc0 : 0 ≤ c) (hac : c < a) (hcb : c ≤ a * (1 - 1 / p.toReal))
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hn : 0 < n) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H) (hδ : 0 ≤ δ) (hP : 0 ≤ P)
    (hpot : ∀ t ∈ Icc ρ R, |radialPotential t e Λ| ≤ P)
    (hlip : LipschitzOnWith J (fun t => radialPotential t e Λ) (Icc ρ R))
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hrhi : ∀ u v, x.1 u v 0 ≤ R)
    (hνlo : ∀ (u : Icc 0 U) (v : Icc 0 V), n * Real.exp (a * v) ≤
      -radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v)
    (hνhi : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hout : ∀ v : Icc 0 V, Real.exp (c * v) * |h v| ≤ H)
    (hwidth : U * Real.exp (a * V) ≤ δ) (hsmall : L * N * δ / (ρ ^ 2 * (a - c)) ≤ 1 / 2)
    (u : Icc 0 U) (v : Icc 0 V) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let G := fun (q : Icc 0 U) (t : ℝ) => Real.exp (intervalExtension hV (x.1 q) t 2) *
      radialPotential (intervalExtension hV (x.1 q) t 0) e Λ / intervalExtension hV (ν q) t
    let E := 2 * (H + L * (r 0 / ρ) * (A * δ ^ (1 - 1 / p.toReal))) / ρ
    let β := N / (ρ * (a - c)) * E
    let ε := ((8 * P * R / n) * (r 0 / ρ) ^ 2 * A ^ 2 * (u : ℝ) ^ (1 - 2 / p.toReal) +
      ((8 * P * R / n) * β ^ 2 + 4 * J * N) * δ) / a
    let S := -horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v
    (∫ t in (0 : ℝ)..v, |G u t - G ⟨0, le_rfl, hU⟩ t|) ≤ ε ∧
      ((r 0 - (u : ℝ)) / r 0) * S * Real.exp (-ε) ≤ -ν u v ∧
      -ν u v ≤ (1 + N * δ / ρ) * S * Real.exp ε := by
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let z : Icc 0 U := ⟨0, le_rfl, hU⟩
  let G := fun (q : Icc 0 U) (t : ℝ) => Real.exp (intervalExtension hV (x.1 q) t 2) *
    radialPotential (intervalExtension hV (x.1 q) t 0) e Λ / intervalExtension hV (ν q) t
  let E := 2 * (H + L * (r 0 / ρ) * (A * δ ^ (1 - 1 / p.toReal))) / ρ
  let β := N / (ρ * (a - c)) * E
  let C := (8 * P * R / n) * (r 0 / ρ) ^ 2 * A ^ 2 * (u : ℝ) ^ (1 - 2 / p.toReal)
  let D := (8 * P * R / n) * β ^ 2 + 4 * J * N
  let B := fun w : Icc 0 V => (2 * R / n) * ((r 0 / ρ) ^ 2 * A ^ 2 * Real.exp (-a * w) *
    (u : ℝ) ^ (1 - 2 / p.toReal) + β ^ 2 * u * Real.exp ((a - 2 * c) * w))
  let κ := fun (q : Icc 0 U) (w : Icc 0 V) => -Real.exp (x.1 q w 2) / (4 * ν q w)
  have hn' (q : Icc 0 U) (w : Icc 0 V) : ν q w < 0 :=
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf q w).2.2.1
  have hu : 0 ≤ (u : ℝ) := u.property.1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) v) :
      |G u t - G z t| ≤ C * Real.exp (-a * t) + D * u * Real.exp (a * t) := by
    let w : Icc 0 V := ⟨t, ht.1, ht.2.trans v.property.2⟩
    have hB : 0 ≤ B w := by dsimp only [B]; positivity
    have hb := hx.horizon_outer_feedback hU hV hUR hc hi hrc hr0 hφ hrd hp hf hA hfn
      hc0 hac hcb hρ hR hn hN hL hH hδ hlo hrhi hνlo hνhi hlam hout hwidth hsmall u w
    have hklo : Real.exp (-B w) ≤ κ u w := hb.2.1
    have hkhi : κ u w ≤ 1 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u w).2.2.2.2
    have hk : |κ u w - 1| ≤ B w := by
      rw [abs_of_nonpos (sub_nonpos.2 hkhi)]
      linarith only [hklo, Real.add_one_le_exp (-B w)]
    have hg := hx.radial_gap_weighted_bound hx.choose rfl
      (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 (fun q w => (hn' q w).le) hνhi u w
    have hrabs : |x.1 u w 0 - x.1 z w 0| ≤ N * u * Real.exp (a * t) := by
      rw [abs_sub_comm, abs_of_nonneg hg.1]
      exact hg.2
    have hdiff := hlip.dist_le_mul (x.1 u w 0) ⟨hlo u w, hrhi u w⟩ (x.1 z w 0) ⟨hlo z w, hrhi z w⟩
    simp only [Real.dist_eq] at hdiff
    have hpd := hdiff.trans (mul_le_mul_of_nonneg_left hrabs J.coe_nonneg)
    have hprod : |(κ u w - 1) * radialPotential (x.1 u w 0) e Λ| ≤ B w * P := by
      rw [abs_mul]
      exact mul_le_mul hk (hpot _ ⟨hlo u w, hrhi u w⟩) (abs_nonneg _) hB
    have heq (q : Icc 0 U) : G q t = -4 * κ q w * radialPotential (x.1 q w 0) e Λ := by
      simp only [G, intervalExtension_apply, projIcc_of_mem hV (show t ∈ Icc 0 V from w.property)]
      change Real.exp (x.1 q w 2) * radialPotential (x.1 q w 0) e Λ / ν q w = _
      dsimp only [κ]
      field_simp [ne_of_lt (hn' q w)]
    have hkz : κ z w = 1 := (hx.horizon_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf w).2.2
    have herr : G u t - G z t = -4 * ((κ u w - 1) * radialPotential (x.1 u w 0) e Λ +
        (radialPotential (x.1 u w 0) e Λ - radialPotential (x.1 z w 0) e Λ)) := by rw [heq, heq, hkz]; ring
    have hraw := mul_le_mul_of_nonneg_left
      ((abs_add_le ((κ u w - 1) * radialPotential (x.1 u w 0) e Λ)
        (radialPotential (x.1 u w 0) e Λ - radialPotential (x.1 z w 0) e Λ)).trans (add_le_add hprod hpd))
      (by norm_num : (0 : ℝ) ≤ 4)
    rw [herr, abs_mul, show |(-4 : ℝ)| = 4 by norm_num]
    apply hraw.trans
    have het : Real.exp ((a - 2 * c) * t) ≤ Real.exp (a * t) := Real.exp_le_exp.2 (by nlinarith only [mul_nonneg hc0 ht.1])
    have heb := mul_le_mul_of_nonneg_left het (mul_nonneg (sq_nonneg β) u.property.1)
    have heB := mul_le_mul_of_nonneg_left heb (by positivity : 0 ≤ (8 * P * R / n))
    dsimp only [B, C, D, w]
    simp only [div_eq_mul_inv] at heB ⊢
    nlinarith only [heB]
  have hw : u * Real.exp (a * v) ≤ δ :=
    (mul_le_mul u.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 ha.le))
      (Real.exp_pos _).le hU).trans hwidth
  have hierr := exponential_error_integral_bound ha u.property.1 v.property.1 hC hD hsource hw
  have herr := (intervalIntegral.abs_integral_le_integral_abs (f := fun t => G u t - G z t) v.property.1).trans hierr
  have hratio := hx.horizon_radial_ratio hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v
  let T := ((r 0 - (u : ℝ)) / r 0) * (r v / x.1 u v 0) *
    (-horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v)
  let S := -horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v
  have hS : 0 ≤ S := (neg_pos.2 (horizon_normalization _ (v : ℝ)).1).le
  have hrp := hx.incoming_radius_pos hU hV hUR hp hf u v
  have hinit : 0 ≤ (r 0 - (u : ℝ)) / r 0 :=
    div_nonneg (sub_pos.2 (u.property.2.trans_lt hUR)).le (hU.trans hUR.le)
  have hinit1 : (r 0 - (u : ℝ)) / r 0 ≤ 1 := (div_le_one (hU.trans_lt hUR)).2 (sub_le_self _ hu)
  have hgap := hx.radial_gap_weighted_bound hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 (fun q w => (hn' q w).le) hνhi u v
  rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v] at hgap
  change 0 ≤ r v - x.1 u v 0 ∧ r v - x.1 u v 0 ≤ N * u * Real.exp (a * v) at hgap
  have hgδ : r v - x.1 u v 0 ≤ N * δ := hgap.2.trans (by nlinarith only [mul_le_mul_of_nonneg_left hw hN])
  have hratio1 : 1 ≤ r v / x.1 u v 0 := (one_le_div hrp).2 (sub_nonneg.1 hgap.1)
  have hratioup : r v / x.1 u v 0 ≤ 1 + N * δ / ρ := by
    calc
      _ = 1 + (r v - x.1 u v 0) / x.1 u v 0 := by field_simp [hrp.ne']; ring
      _ ≤ _ := add_le_add le_rfl (div_le_div₀ (mul_nonneg hN hδ) hgδ hρ (hlo u v))
  have hTlo : ((r 0 - (u : ℝ)) / r 0) * S ≤ T := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio1 hinit) hS
  have hThi : T ≤ (1 + N * δ / ρ) * S :=
    mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (zero_le_one.trans hratio1) hinit1).trans hratioup) hS
  have hT : 0 ≤ T := by
    exact (mul_nonneg hinit hS).trans hTlo
  change -ν u v = T * Real.exp (∫ t in (0 : ℝ)..v, G u t - G z t) at hratio
  refine ⟨hierr, ?_, ?_⟩
  · apply (mul_le_mul_of_nonneg_right hTlo (Real.exp_pos _).le).trans
    rw [hratio]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (abs_le.1 herr).1) hT
  · apply LE.le.trans _ (mul_le_mul_of_nonneg_right hThi (Real.exp_pos _).le)
    rw [hratio]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (abs_le.1 herr).2) hT

end CauchyHorizon
