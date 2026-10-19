import CauchyHorizon.Analysis.ExponentialError

/-! Combine the partial conformal and restoring errors at the end of the early window. -/

namespace CauchyHorizon

theorem gamma_decay_envelope {β η q C D L Z T : ℝ}
    (hβ : 0 ≤ β) (hη : 0 < η) (hq : 0 < q) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hZ : 0 ≤ Z) (hT : 0 ≤ T) :
    let ηg := min (η / 2) (q * β) / (1 + β)
    (0 < β → 0 < ηg) ∧
      C * Real.exp (-η * ((1 + β) * T)) ≤ C * Real.exp (-ηg * ((1 + β) * T)) ∧
      L * (Z * Real.exp (-q * (β * T)) + D * (C * (1 + β * T) * Real.exp (-η * T))) ≤
        (L * (Z + D * (C * (1 + 2 * β / η)))) *
        Real.exp (-ηg * ((1 + β) * T)) := by
  let μ := min (η / 2) (q * β)
  let ηg := μ / (1 + β)
  have hα : 0 < 1 + β := by positivity
  have hid : ηg * ((1 + β) * T) = μ * T := by
    dsimp only [ηg]
    field_simp
  have he (a : ℝ) (ha : μ ≤ a) :
      Real.exp (-a * T) ≤ Real.exp (-ηg * ((1 + β) * T)) := by
    simp only [neg_mul, hid]
    exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right ha hT))
  have hp : C * Real.exp (-η * ((1 + β) * T)) ≤ C * Real.exp (-ηg * ((1 + β) * T)) := by
    apply mul_le_mul_of_nonneg_left ?_ hC
    have hh := he (η * (1 + β)) ((min_le_left _ _).trans (by nlinarith only [hη, hβ]))
    simpa only [neg_mul, mul_assoc] using hh
  have hm : C * (1 + β * T) * Real.exp (-η * T) ≤
      (C * (1 + 2 * β / η)) * Real.exp (-ηg * ((1 + β) * T)) := by
    have hh := mul_le_mul_of_nonneg_left (linear_mul_exp_decay hη hβ hT) hC
    rw [← mul_assoc, ← mul_assoc] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (he (η / 2) (min_le_left _ _)) (by positivity))
  have hk := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left (show Real.exp (-q * (β * T)) ≤
      Real.exp (-ηg * ((1 + β) * T)) by
        simpa only [neg_mul, mul_assoc] using he (q * β) (min_le_right _ _)) hZ)
    (mul_le_mul_of_nonneg_left hm hD)) hL
  refine ⟨fun hb => div_pos (lt_min (by positivity) (mul_pos hq hb)) hα, hp, ?_⟩
  exact hk.trans_eq (by ring)

theorem gamma_conformal_bound {β η q C D L Z T ℓ K k : ℝ}
    (hβ : 0 ≤ β) (hη : 0 < η) (hq : 0 < q) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hZ : 0 ≤ Z) (hT : 0 ≤ T)
    (hpartial : |ℓ - 2 * K| ≤ C * Real.exp (-η * ((1 + β) * T)))
    (hK : |K + k| ≤ L * (Z * Real.exp (-q * (β * T)) +
      D * (C * (1 + β * T) * Real.exp (-η * T)))) :
    let ηg := min (η / 2) (q * β) / (1 + β)
    (0 < β → 0 < ηg) ∧
      |ℓ + 2 * k| ≤ (C + 2 * L * (Z + D * (C * (1 + 2 * β / η)))) *
        Real.exp (-ηg * ((1 + β) * T)) := by
  obtain ⟨hpos, hp, hk⟩ := gamma_decay_envelope hβ hη hq hC hD hL hZ hT
  refine ⟨hpos, ?_⟩
  let ηg := min (η / 2) (q * β) / (1 + β)
  calc
    |ℓ + 2 * k| = |(ℓ - 2 * K) + 2 * (K + k)| := by congr 1; ring
    _ ≤ |ℓ - 2 * K| + 2 * |K + k| := by
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
        abs_add_le (ℓ - 2 * K) (2 * (K + k))
    _ ≤ C * Real.exp (-ηg * ((1 + β) * T)) + 2 *
        ((L * (Z + D * (C * (1 + 2 * β / η)))) * Real.exp (-ηg * ((1 + β) * T))) :=
      add_le_add (hpartial.trans hp) (mul_le_mul_of_nonneg_left (hK.trans hk) (by norm_num))
    _ = _ := by ring

end CauchyHorizon
