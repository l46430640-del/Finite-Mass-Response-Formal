import CauchyHorizon.Characteristic.OuterClosure

/-! The actual thin outer rectangle has the horizon's radial normalization. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.radial_gap_relative_bound
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {S ε : ℝ} (hS : 0 < S) (v : Icc 0 V)
    (hbound : ∀ q : Icc 0 U, |(-radialNuField hV e Λ zIn x.1 hr q v) / S - 1| ≤ ε)
    (u : Icc 0 U) (hu : 0 < (u : ℝ)) :
    |(x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) / ((u : ℝ) * S) - 1| ≤ ε := by
  let N := fun t => -intervalExtension hU (radialNuField hV e Λ zIn x.1 hr) t v
  have hNc : Continuous N := by dsimp [N]; fun_prop
  have hI := hx.radial_horizontal_integral hr hzin hinu u v
  have heq : (∫ t in (0 : ℝ)..u, N t / S - 1) =
      (u : ℝ) * ((x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) / ((u : ℝ) * S) - 1) := by
    rw [intervalIntegral.integral_sub ((hNc.div_const S).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_div, intervalIntegral.integral_const]
    change (∫ t in (0 : ℝ)..u, N t) / S - ((u : ℝ) - 0) • (1 : ℝ) = _
    rw [hI, sub_zero, smul_eq_mul, mul_one]
    field_simp [hu.ne', hS.ne']
  have hb : ‖∫ t in (0 : ℝ)..u, N t / S - 1‖ ≤ ε * |(u : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    simpa only [N, Real.norm_eq_abs, intervalExtension_apply] using
      hbound (projIcc 0 U hU t)
  rw [Real.norm_eq_abs, heq, abs_mul, abs_of_pos hu, sub_zero, abs_of_pos hu] at hb
  exact (mul_le_mul_iff_right₀ hu).1 (by simpa only [mul_comm] using hb)

theorem exists_horizon_outer_normalization {M e Λ a c ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
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
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ C ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        c ≤ a * (1 - 1 / p.toReal) → U * Real.exp (a * V) ≤ δ →
        let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
        let S := fun v => -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) v
        let σ := U * Real.exp (a * V)
        let ε := C * (U ^ (1 - 2 / p.toReal) + σ)
        let E := (1 + C * σ) * Real.exp ε - (1 - U / r 0) * Real.exp (-ε)
        (∀ (u : Icc 0 U) (v : Icc 0 V), |(-ν u v) / S v - 1| ≤ E) ∧
        (∀ (u : Icc 0 U), 0 < (u : ℝ) → ∀ v : Icc 0 V,
          |(r v - x.1 u v 0) / ((u : ℝ) * S v) - 1| ≤ E) ∧
        (∀ (u : Icc 0 U) (v : Icc 0 V),
          |Real.exp (x.1 u v 2) / (4 * S v) - 1| ≤ E + (1 - Real.exp (-ε))) := by
  obtain ⟨δ₀, L, hδ₀, hδ₁, _, hL, houter⟩ := exists_horizon_outer_bounds
    hc hi hrc hr0 hφ hrd ha hc0 hac hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  have hrp : 0 < r 0 := by linarith [(haxis 0 (by simp)).1]
  have hR : 0 ≤ R := by linarith [(haxis 0 (by simp)).1, (haxis 0 (by simp)).2]
  obtain ⟨P, hP, hpot⟩ := radialPotential_bounded e Λ (R := R) hρ
  obtain ⟨J, hlip⟩ := radialPotential_lipschitzOn (R := R) (e := e) (Λ := Λ) hρ
  let n := nH / 2
  let N := 2 * NH
  let E₀ := 2 * (H + L * (r 0 / ρ) * A) / ρ
  let β₀ := N / (ρ * (a - c)) * E₀
  let C₀ := (8 * P * R / n) * (r 0 / ρ) ^ 2 * A ^ 2
  let D₀ := (8 * P * R / n) * β₀ ^ 2 + 4 * J * N
  let K := (2 * R / n) * ((r 0 / ρ) ^ 2 * A ^ 2 + β₀ ^ 2)
  let C := (C₀ + D₀) / a + N / ρ + K
  have hn : 0 < n := by dsimp [n]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨δ₁, hδ₂, _, _, _, hsmall, _⟩ := exists_small_outer_width hrp hρ
    (by norm_num : (0 : ℝ) < 1) 0 (L * N / (ρ ^ 2 * (a - c))) 0 0
  refine ⟨min δ₀ δ₁, C, lt_min hδ₀ hδ₂, (min_le_left _ _).trans hδ₁, hC, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb hwidth
  let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let S := fun v => -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) v
  let σ := U * Real.exp (a * V)
  let ε := C * (U ^ (1 - 2 / p.toReal) + σ)
  let lo := (1 - U / r 0) * Real.exp (-ε)
  let up := (1 + C * σ) * Real.exp ε
  have hσ0 : 0 ≤ σ := mul_nonneg hU (Real.exp_pos _).le
  have hσ1 : σ ≤ 1 := (hwidth.trans (min_le_left _ _)).trans hδ₁
  have hgeo := houter U V hU hV hUR p hp f hf x hx hfn hcb (hwidth.trans (min_le_left _ _))
  have hneg (q w) : ν q w < 0 := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf q w).2.2.1
  have hlo (q w) : ρ ≤ x.1 q w 0 := by linarith only [(hgeo q w).1, hρ]
  have hhi (q w) : x.1 q w 0 ≤ R := (hgeo q w).2.1
  have hνlo (q : Icc 0 U) (w : Icc 0 V) : n * Real.exp (a * w) ≤ -ν q w := by
    have hh := (hgeo q w).2.2.2.1
    dsimp [n]
    nlinarith only [hh, mul_pos hnH (Real.exp_pos (a * w))]
  have hνhi (q : Icc 0 U) (w : Icc 0 V) : |ν q w| ≤ N * Real.exp (a * w) := by
    rw [abs_of_neg (hneg q w)]
    have hh := (hgeo q w).2.2.2.2
    dsimp [N]
    nlinarith only [hh, mul_pos hNH (Real.exp_pos (a * w))]
  have hsmall' : L * N * σ / (ρ ^ 2 * (a - c)) ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left (hwidth.trans (min_le_right _ _))
      (by positivity : 0 ≤ L * N / (ρ ^ 2 * (a - c)))
    apply le_trans _ hsmall
    simpa only [div_mul_eq_mul_div] using hh
  obtain ⟨hb1, hb2⟩ := incoming_exponent_bounds hp
  have hpow : σ ^ (1 - 1 / p.toReal) ≤ 1 := Real.rpow_le_one hσ0 hσ1 (by linarith only [hb1])
  let E₁ := 2 * (H + L * (r 0 / ρ) * (A * σ ^ (1 - 1 / p.toReal))) / ρ
  let β := N / (ρ * (a - c)) * E₁
  have hE : E₁ ≤ E₀ := by
    dsimp [E₁, E₀]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hA hpow)
        (mul_nonneg hL (div_nonneg hrp.le hρ.le)))) (by norm_num)) hρ.le
  have hβ : β ≤ β₀ := mul_le_mul_of_nonneg_left hE (by positivity)
  have hβ0 : 0 ≤ β := by dsimp [β, E₁]; positivity
  have hβsq := (sq_le_sq₀ hβ0 (hβ0.trans hβ)).2 hβ
  have hUp : 0 ≤ U ^ (1 - 2 / p.toReal) := Real.rpow_nonneg hU _
  have hε0 : 0 ≤ ε := mul_nonneg hC (add_nonneg hUp hσ0)
  have hinit0 : 0 ≤ 1 - U / r 0 := by rw [sub_nonneg, div_le_one hrp]; exact hUR.le
  have hinit1 : 1 - U / r 0 ≤ 1 := sub_le_self _ (div_nonneg hU hrp.le)
  have hlo1 : lo ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (neg_nonpos.2 hε0)) hinit0).trans
      (by simpa only [mul_one] using hinit1)
  have hup1 : 1 ≤ up := by
    have h1 : 1 ≤ 1 + C * σ := le_add_of_nonneg_right (mul_nonneg hC hσ0)
    exact one_le_mul_of_one_le_of_one_le h1 (Real.one_le_exp_iff.2 hε0)
  have hnu (q : Icc 0 U) (v : Icc 0 V) : |(-ν q v) / S v - 1| ≤ up - lo := by
    let η := (C₀ * (q : ℝ) ^ (1 - 2 / p.toReal) +
      ((8 * P * R / n) * β ^ 2 + 4 * J * N) * σ) / a
    have hh := hx.horizon_outer_nu_comparison hU hV hUR hc hi hrc hr0 hφ hrd hp hf
      hA hfn ha hc0 hac hcb hρ hR hn hN hL hH hσ0 hP hpot hlip hlo hhi hνlo hνhi
      (fun q w => (hgeo q w).2.2.1) (fun v => hout v v.property.1) le_rfl hsmall' q v
    change _ ≤ η ∧ ((r 0 - (q : ℝ)) / r 0) * S v * Real.exp (-η) ≤ -ν q v ∧
      -ν q v ≤ (1 + N * σ / ρ) * S v * Real.exp η at hh
    have hη : η ≤ ε := by
      have hqp := Real.rpow_le_rpow q.property.1 q.property.2 (by linarith only [hb2] : 0 ≤ 1 - 2 / p.toReal)
      have hd : ((8 * P * R / n) * β ^ 2 + 4 * J * N) * σ ≤ D₀ * σ :=
        mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_left hβsq (by positivity : 0 ≤ 8 * P * R / n)) le_rfl) hσ0
      have he := add_le_add (mul_le_mul_of_nonneg_left hqp hC₀) hd
      have hcross₁ := mul_nonneg hC₀ hσ0
      have hcross₂ := mul_nonneg hD₀ hUp
      calc
        η ≤ (C₀ * U ^ (1 - 2 / p.toReal) + D₀ * σ) / a :=
          div_le_div_of_nonneg_right he ha.le
        _ ≤ ((C₀ + D₀) * (U ^ (1 - 2 / p.toReal) + σ)) / a :=
          div_le_div_of_nonneg_right (by nlinarith only [hcross₁, hcross₂]) ha.le
        _ = ((C₀ + D₀) / a) * (U ^ (1 - 2 / p.toReal) + σ) := by ring
        _ ≤ ε := mul_le_mul_of_nonneg_right
          (show (C₀ + D₀) / a ≤ C by dsimp only [C]; linarith only [div_nonneg hN hρ.le, hK])
          (add_nonneg hUp hσ0)
    have hS : 0 < S v := neg_pos.2 (horizon_normalization _ v).1
    have hgeom : 1 + N * σ / ρ ≤ 1 + C * σ := by
      have hh := mul_le_mul_of_nonneg_right (show N / ρ ≤ C from
        by dsimp only [C]; linarith only [div_nonneg (add_nonneg hC₀ hD₀) ha.le, hK]) hσ0
      simpa only [div_mul_eq_mul_div] using (add_le_add (le_refl (1 : ℝ)) hh)
    have hlow : lo * S v ≤ -ν q v := by
      have hinit : 1 - U / r 0 ≤ (r 0 - (q : ℝ)) / r 0 := by
        have hh := div_le_div_of_nonneg_right q.property.2 hrp.le
        rw [sub_div, div_self hrp.ne']
        linarith only [hh]
      have he := mul_le_mul (mul_le_mul_of_nonneg_right hinit hS.le)
        (Real.exp_le_exp.2 (neg_le_neg hη)) (Real.exp_pos _).le
        (mul_nonneg (hinit0.trans hinit) hS.le)
      calc
        lo * S v = ((1 - U / r 0) * S v) * Real.exp (-ε) := by dsimp [lo]; ring
        _ ≤ _ := he
        _ ≤ _ := hh.2.1
    have hhigh : -ν q v ≤ up * S v := by
      apply hh.2.2.trans
      have he := mul_le_mul (mul_le_mul_of_nonneg_right hgeom hS.le)
        (Real.exp_le_exp.2 hη) (Real.exp_pos _).le
        (mul_nonneg (by positivity : 0 ≤ 1 + C * σ) hS.le)
      calc
        _ ≤ _ := he
        _ = up * S v := by dsimp [up]; ring
    have hl := (le_div_iff₀ hS).2 hlow
    have hu := (div_le_iff₀ hS).2 hhigh
    exact abs_le.2 ⟨by linarith only [hl, hup1], by linarith only [hu, hlo1]⟩
  refine ⟨hnu, ?_, ?_⟩
  · intro u hu v
    have hh := hx.radial_gap_relative_bound hx.choose rfl
      (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1
      (neg_pos.2 (horizon_normalization _ v).1) v (fun q => hnu q v) u hu
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v] at hh
    exact hh
  · intro u v
    let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
    have hk := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.2
    change 0 < κ ∧ κ ≤ 1 at hk
    have hfb := (hx.horizon_outer_feedback hU hV hUR hc hi hrc hr0 hφ hrd hp hf hA hfn
      hc0 hac hcb hρ hR hn hN hL hH hσ0 hlo hhi hνlo hνhi
      (fun q w => (hgeo q w).2.2.1) (fun v => hout v v.property.1) le_rfl hsmall' u v).2.1
    let D := (2 * R / n) * ((r 0 / ρ) ^ 2 * A ^ 2 * Real.exp (-a * v) * (u : ℝ) ^ (1 - 2 / p.toReal) +
      β ^ 2 * u * Real.exp ((a - 2 * c) * v))
    change Real.exp (-D) ≤ κ at hfb
    have huσ : (u : ℝ) * Real.exp (a * v) ≤ σ :=
      mul_le_mul u.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 ha.le))
        (Real.exp_pos _).le hU
    have hp := Real.rpow_le_rpow u.property.1 u.property.2 (by linarith only [hb2] : 0 ≤ 1 - 2 / p.toReal)
    have hterm₁ : Real.exp (-a * v) * (u : ℝ) ^ (1 - 2 / p.toReal) ≤ U ^ (1 - 2 / p.toReal) :=
      (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.2 (by nlinarith only [ha, v.property.1]))
        (Real.rpow_nonneg u.property.1 _)).trans (by simpa only [one_mul] using hp)
    have hterm₂ : (u : ℝ) * Real.exp ((a - 2 * c) * v) ≤ σ :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith only [hc0, v.property.1]))
        u.property.1).trans huσ
    have hD : D ≤ ε := by
      have hfirst := mul_le_mul_of_nonneg_left hterm₁ (by positivity : 0 ≤ (r 0 / ρ) ^ 2 * A ^ 2)
      have hsecond := mul_le_mul hβsq hterm₂ (mul_nonneg u.property.1 (Real.exp_pos _).le) (sq_nonneg β₀)
      have hinside : (r 0 / ρ) ^ 2 * A ^ 2 * Real.exp (-a * v) * (u : ℝ) ^ (1 - 2 / p.toReal) +
          β ^ 2 * u * Real.exp ((a - 2 * c) * v) ≤
          ((r 0 / ρ) ^ 2 * A ^ 2 + β₀ ^ 2) * (U ^ (1 - 2 / p.toReal) + σ) := by
        nlinarith only [hfirst, hsecond, mul_nonneg (sq_nonneg β₀) hUp,
          mul_nonneg (mul_nonneg (sq_nonneg (r 0 / ρ)) (sq_nonneg A)) hσ0]
      calc
        D ≤ K * (U ^ (1 - 2 / p.toReal) + σ) := by
          simpa only [D, K, mul_assoc] using
            mul_le_mul_of_nonneg_left hinside (div_nonneg (mul_nonneg (by norm_num) hR) hn.le)
        _ ≤ ε := mul_le_mul_of_nonneg_right
          (show K ≤ C by
            dsimp only [C]
            linarith only [div_nonneg (add_nonneg hC₀ hD₀) ha.le, div_nonneg hN hρ.le])
          (add_nonneg hUp hσ0)
    have hklo := (Real.exp_le_exp.2 (neg_le_neg hD)).trans hfb
    have hS : 0 < S v := neg_pos.2 (horizon_normalization _ v).1
    have heq : Real.exp (x.1 u v 2) / (4 * S v) - 1 = κ * ((-ν u v) / S v - 1) + (κ - 1) := by
      dsimp only [κ]
      field_simp [(hneg u v).ne, hS.ne']
      ring
    rw [heq]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_pos hk.1, abs_of_nonpos (sub_nonpos.2 hk.2)]
    have hnub := mul_le_of_le_one_left (abs_nonneg ((-ν u v) / S v - 1)) hk.2
    exact add_le_add (hnub.trans (hnu u v)) (by linarith only [hklo])

theorem IsWaveIntegral.radial_outer_reference_bound
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {S ε η cν a rplus : ℝ} (hS : 0 < S) (hcν : 0 < cν) (v : Icc 0 V)
    (hbound : ∀ q : Icc 0 U, |(-radialNuField hV e Λ zIn x.1 hr q v) / S - 1| ≤ ε)
    (hscale : |S / (cν * Real.exp (a * v)) - 1| ≤ η)
    (u : Icc 0 U) (hu : 0 < (u : ℝ)) :
    |(-radialNuField hV e Λ zIn x.1 hr u v) / (cν * Real.exp (a * v)) - 1| ≤
        ε * (1 + η) + η ∧
      |(rplus - x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (a * v))) - 1| ≤
        ε * (1 + η) + η +
          |x.1 ⟨0, le_rfl, hU⟩ v 0 - rplus| / ((u : ℝ) * (cν * Real.exp (a * v))) := by
  let T := cν * Real.exp (a * v)
  have hT : 0 < T := mul_pos hcν (Real.exp_pos _)
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hbound u)
  have hST : |S / T| ≤ 1 + η := by
    have hh := abs_add_le (S / T - 1) 1
    rw [sub_add_cancel, abs_one] at hh
    linarith only [hh, hscale]
  have transfer (z : ℝ) (hz : |z / S - 1| ≤ ε) :
      |z / T - 1| ≤ ε * (1 + η) + η := by
    have heq : z / T - 1 = (z / S - 1) * (S / T) + (S / T - 1) := by
      field_simp [hS.ne', hT.ne']
      ring
    rw [heq]
    calc
      _ ≤ |(z / S - 1) * (S / T)| + |S / T - 1| := abs_add_le _ _
      _ = |z / S - 1| * |S / T| + |S / T - 1| := by rw [abs_mul]
      _ ≤ ε * (1 + η) + η :=
        add_le_add (mul_le_mul hz hST (abs_nonneg _) hε) hscale
  refine ⟨transfer _ (hbound u), ?_⟩
  have hgap := hx.radial_gap_relative_bound hr hzin hinu hS v hbound u hu
  have hg := transfer ((x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) / (u : ℝ))
    (by simpa only [div_div] using hgap)
  have heq : (rplus - x.1 u v 0) / ((u : ℝ) * T) - 1 =
      ((x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) / (u : ℝ) / T - 1) +
        (rplus - x.1 ⟨0, le_rfl, hU⟩ v 0) / ((u : ℝ) * T) := by
    field_simp [hu.ne', hT.ne']
    ring
  change |(rplus - x.1 u v 0) / ((u : ℝ) * T) - 1| ≤ _
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_of_pos (mul_pos hu hT), abs_sub_comm rplus]
  exact add_le_add hg le_rfl

end CauchyHorizon
