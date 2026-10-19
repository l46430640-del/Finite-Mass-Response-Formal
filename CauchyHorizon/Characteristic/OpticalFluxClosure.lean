import CauchyHorizon.Characteristic.OpticalCorner

/-! The actual Raychaudhuri constraint converts radiation energy into logarithmic optical flux. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem optical_density_le_of_corner {R ell P S u k v σ ρ Co : ℝ}
    (hu : 0 < u) (hρ : 0 < ρ) (hCo : 0 < Co) (hR : ρ ≤ R)
    (hcorner : Co * (u ^ (-1 - σ) * Real.exp (-(2 * k) * v)) ≤ Real.exp ell)
    (hS : Real.exp (k * v) * |R * P| ≤ S) :
    R * Real.exp (-ell) * P ^ 2 ≤ u ^ (1 + σ) / (ρ * Co) * S ^ 2 := by
  have hR0 : 0 < R := hρ.trans_le hR
  have hden : ρ * Co * u ^ (-1 - σ) ≤ R * Real.exp ell * Real.exp ((2 * k) * v) := by
    calc
      _ ≤ R * (Co * (u ^ (-1 - σ) * Real.exp (-(2 * k) * v))) *
          Real.exp ((2 * k) * v) := by
        rw [neg_mul, Real.exp_neg]
        field_simp
        exact hR
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcorner hR0.le) (Real.exp_pos _).le
  have hsq := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) hS 2
  have hid : R * Real.exp (-ell) * P ^ 2 =
      (Real.exp (k * v) * |R * P|) ^ 2 / (R * Real.exp ell * Real.exp ((2 * k) * v)) := by
    rw [mul_pow, sq_abs, ← Real.exp_nat_mul, Real.exp_neg]
    have he : 2 * (k * v) = (2 * k) * v := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he]
    field_simp
  rw [hid]
  calc
    _ ≤ S ^ 2 / (ρ * Co * u ^ (-1 - σ)) :=
      div_le_div₀ (by positivity) hsq (by positivity) hden
    _ = _ := by
      rw [show -1 - σ = -(1 + σ) by ring, Real.rpow_neg hu.le]
      field_simp

theorem IsWaveIntegral.optical_flux_of_radiation_energy
    {M e Λ U V k σ Cd Co ρ E J₀ : ℝ} {h r : ℝ → ℝ}
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
    (hCd : 0 < Cd) (hCo : 0 < Co) (hρ : 0 < ρ) (u : Icc 0 U) (hu : 0 < (u : ℝ))
    (a γ b : Icc 0 V) (haγ : a ≤ γ) (hγb : γ ≤ b)
    (hentry : Cd * (u : ℝ) ≤ -x.2.1 u a 0 / Real.exp (x.1 u a 2))
    (hr : ∀ v : Icc 0 V, γ ≤ v → v ≤ b → ρ ≤ x.1 u v 0)
    (hcorner : ∀ v : Icc 0 V, γ ≤ v → v ≤ b →
      Co * ((u : ℝ) ^ (-1 - σ) * Real.exp (-(2 * k) * v)) ≤ Real.exp (x.1 u v 2))
    (S : C(Icc 0 V, ℝ))
    (hS : ∀ v : Icc 0 V, γ ≤ v → v ≤ b → Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ S v)
    (henergy : (∫ t in (0 : ℝ)..V, (S (projIcc 0 V hV t)) ^ 2) ≤ E)
    (hinitial : (∫ t in (a : ℝ)..γ, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ J₀) :
    (-x.2.1 u b 0 / Real.exp (x.1 u b 2)) -
        (-x.2.1 u γ 0 / Real.exp (x.1 u γ 2)) ≤ (u : ℝ) ^ (1 + σ) / (ρ * Co) * E ∧
    (∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤
      J₀ + Real.log (1 + (u : ℝ) ^ σ / (Cd * ρ * Co) * E) := by
  let D := fun v : Icc 0 V => -x.2.1 u v 0 / Real.exp (x.1 u v 2)
  let F := fun t : ℝ => intervalExtension hV (x.1 u) t 0 *
    Real.exp (-intervalExtension hV (x.1 u) t 2) * (intervalExtension hV (x.2.1 u) t 1) ^ 2
  let J := fun t : ℝ => intervalExtension hV (x.1 u) t 0 *
    (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)
  let A := (u : ℝ) ^ (1 + σ) / (ρ * Co)
  let Z := (u : ℝ) ^ σ / (Cd * ρ * Co) * E
  have hFc : Continuous F := by fun_prop
  have hSc : Continuous (fun t => (S (projIcc 0 V hV t)) ^ 2) := by fun_prop
  have hE : 0 ≤ E := (intervalIntegral.integral_nonneg hV (fun t _ => sq_nonneg _)).trans henergy
  have hA : 0 ≤ A := by positivity
  have hZ : 0 ≤ Z := by positivity
  have ha : x.2.1 u a 0 < 0 :=
    neg_pos.1 ((div_pos_iff_of_pos_right (Real.exp_pos _)).1 ((mul_pos hCd hu).trans_le hentry))
  have hinc : D b - D γ = ∫ t in (γ : ℝ)..b, F t := by
    have hcg := hx.outgoing_integral_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp hf u γ
    have hcb := hx.outgoing_integral_constraint hU hV hUR hc hi hrc hr0 hφ hrd hp hf u b
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hFc.intervalIntegrable (0 : ℝ) γ) (hFc.intervalIntegrable (γ : ℝ) b)
    dsimp only [D, F] at hsplit ⊢
    simp only [neg_div, Real.exp_neg, ← div_eq_mul_inv] at hcg hcb hsplit ⊢
    linarith only [hcg, hcb, hsplit]
  have hpoint (t : ℝ) (ht : t ∈ Icc (γ : ℝ) b) : F t ≤ A * (S (projIcc 0 V hV t)) ^ 2 := by
    have htV : t ∈ Icc 0 V := ⟨γ.property.1.trans ht.1, ht.2.trans b.property.2⟩
    simpa only [F, A, intervalExtension_apply, projIcc_of_mem hV htV] using
      optical_density_le_of_corner hu hρ hCo (hr ⟨t, htV⟩ ht.1 ht.2)
        (hcorner ⟨t, htV⟩ ht.1 ht.2) (hS ⟨t, htV⟩ ht.1 ht.2)
  have hsubenergy : (∫ t in (γ : ℝ)..b, (S (projIcc 0 V hV t)) ^ 2) ≤ E :=
    (intervalIntegral.integral_mono_interval (μ := volume) γ.property.1 hγb b.property.2
      (Filter.Eventually.of_forall (fun t => sq_nonneg _)) (hSc.intervalIntegrable 0 V)).trans henergy
  have hbound : D b - D γ ≤ A * E := by
    rw [hinc]
    calc
      _ ≤ ∫ t in (γ : ℝ)..b, A * (S (projIcc 0 V hV t)) ^ 2 :=
        intervalIntegral.integral_mono_on hγb (hFc.intervalIntegrable _ _)
          ((hSc.const_mul A).intervalIntegrable _ _) hpoint
      _ = A * ∫ t in (γ : ℝ)..b, (S (projIcc 0 V hV t)) ^ 2 :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ A * E := mul_le_mul_of_nonneg_left hsubenergy hA
  have hg := (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a γ haγ ha).1
  obtain ⟨hJag, hJag0, _hqg, _hqg0, _hqgm, htg⟩ :=
    hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a γ haγ ha
  obtain ⟨hJgb, _hJgb0, _hqb, _hqb0, _hqbm, htb⟩ :=
    hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u γ b hγb hg
  have hDg : D γ = D a * Real.exp (∫ t in (a : ℝ)..γ, J t) := by
    dsimp only [D, J]
    rw [htg, Real.exp_add, Real.exp_sub]
    field_simp
  have hDb : D b = D γ * Real.exp (∫ t in (γ : ℝ)..b, J t) := by
    dsimp only [D, J]
    rw [htb, Real.exp_add, Real.exp_sub]
    field_simp
  have hDlower : Cd * (u : ℝ) ≤ D γ := by
    apply hentry.trans
    rw [hDg]
    exact le_mul_of_one_le_right (div_nonneg (neg_pos.2 ha).le (Real.exp_pos _).le)
      (Real.one_le_exp_iff.2 hJag0)
  have hDpos : 0 < D γ := (mul_pos hCd hu).trans_le hDlower
  have hpower : Cd * (u : ℝ) * Z = A * E := by
    dsimp only [Z, A]
    rw [Real.rpow_add hu, Real.rpow_one]
    field_simp
  have hlog : (∫ t in (γ : ℝ)..b, J t) ≤ Real.log (1 + Z) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < 1 + Z)).2
    apply le_of_mul_le_mul_left (a := D γ) _ hDpos
    calc
      _ = D b := hDb.symm
      _ = D γ + (D b - D γ) := by ring
      _ ≤ D γ + A * E := add_le_add le_rfl hbound
      _ = D γ + (Cd * (u : ℝ)) * Z := by rw [hpower]
      _ ≤ D γ + D γ * Z := add_le_add le_rfl (mul_le_mul_of_nonneg_right hDlower hZ)
      _ = D γ * (1 + Z) := by ring
  refine ⟨hbound, ?_⟩
  change (∫ t in (a : ℝ)..b, J t) ≤ J₀ + Real.log (1 + Z)
  rw [← intervalIntegral.integral_add_adjacent_intervals hJag hJgb]
  exact add_le_add hinitial hlog

end CauchyHorizon
