import CauchyHorizon.Characteristic.EarlyScalarClosure

/-! Linked coarse decay rates and losses with strict early-region margins. -/

namespace CauchyHorizon

theorem exists_linked_inner_parameters {k s l : ℝ} (hk : 0 < k) (hks : k < s)
    (hl : l < 2 * s + k) :
    ∃ hc c β ε : ℝ, 0 < hc ∧ hc < k ∧ l < 2 * s + hc ∧ c = (k + hc) / 2 ∧
      0 < c ∧ c < k ∧ c < s ∧ 0 < β ∧ β < 1 / 8 ∧ hc + (k + hc) * β < c ∧
      0 < ε ∧ ε ≤ k / 8 ∧ ε < k * β / 8 ∧
      k ≤ 2 * (2 / 3) * (k - ε) ∧ c < 2 * (k - ε) - ε ∧
      0 < 2 * c - max 0 (2 * (k + ε) + ε - 2 * c) * β ∧
      0 < 2 * c - 2 * (k + ε) * β := by
  let hc := (max 0 (l - 2 * s) + k) / 2
  have hm0 : 0 ≤ max 0 (l - 2 * s) := le_max_left _ _
  have hmk : max 0 (l - 2 * s) < k := max_lt hk (by linarith only [hl])
  have hhc : 0 < hc := by dsimp only [hc]; linarith only [hm0, hk]
  have hhck : hc < k := by dsimp only [hc]; linarith only [hmk]
  have htail : l < 2 * s + hc := by
    have hh := le_max_right 0 (l - 2 * s)
    dsimp only [hc]
    linarith only [hh, hmk]
  let c := (k + hc) / 2
  have hc0 : 0 < c := by dsimp only [c]; positivity
  have hck : c < k := by dsimp only [c]; linarith only [hhck]
  have hcc : hc < c := by dsimp only [c]; linarith only [hhck]
  have hkc : k < 2 * c := by dsimp only [c]; linarith only [hhc]
  let β := min (1 / 16) ((c - hc) / (2 * (k + hc)))
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hβ16 : β ≤ 1 / 16 := min_le_left _ _
  have hβgap : β ≤ (c - hc) / (2 * (k + hc)) := min_le_right _ _
  have hlink : hc + (k + hc) * β < c := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (k + hc))).1 hβgap
    nlinarith only [hh, hcc]
  let ε := min (k / 8) (k * β / 16)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεk : ε ≤ k / 8 := min_le_left _ _
  have hεβ : ε < k * β / 8 :=
    (min_le_right _ _).trans_lt (by nlinarith only [mul_pos hk hβ])
  have hmax : max 0 (2 * (k + ε) + ε - 2 * c) ≤ 3 * k := by
    apply max_le (by positivity)
    linarith only [hεk, hc0, hk]
  have hprod := mul_le_mul hmax hβ16 hβ.le (by positivity : 0 ≤ 3 * k)
  have hprod' := mul_le_mul (show 2 * (k + ε) ≤ 3 * k by linarith only [hεk, hk])
    hβ16 hβ.le (by positivity : 0 ≤ 3 * k)
  refine ⟨hc, c, β, ε, hhc, hhck, htail, rfl, hc0, hck, hck.trans hks,
    hβ, by linarith only [hβ16], hlink, hε, hεk, hεβ, ?_, ?_, ?_, ?_⟩
  · linarith only [hεk, hk]
  · linarith only [hck, hεk, hk]
  · nlinarith only [hprod, hkc, hk]
  · nlinarith only [hprod', hkc, hk]

theorem exists_small_scalar_speed {ρ q gap : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hg : 0 < gap) :
    ∃ L : ℝ, 0 < L ∧ Real.exp 1 * L ^ 2 / (ρ ^ 2 * gap * q) ≤ 1 / 4 := by
  let D := ρ ^ 2 * gap * q
  have hD : 0 < D := by dsimp only [D]; positivity
  let L := min 1 (D / (8 * Real.exp 1))
  have hL : 0 < L := by dsimp only [L]; positivity
  have hL1 : L ≤ 1 := min_le_left _ _
  have hLD : L ≤ D / (8 * Real.exp 1) := min_le_right _ _
  have hsq : L ^ 2 ≤ L := by nlinarith only [mul_le_mul_of_nonneg_left hL1 hL.le]
  refine ⟨L, hL, ?_⟩
  apply (div_le_iff₀ hD).2
  have hh := (le_div_iff₀ (by positivity : 0 < 8 * Real.exp 1)).1 hLD
  have hh' := mul_le_mul_of_nonneg_left hsq (Real.exp_pos 1).le
  nlinarith only [hh, hh', hD.le]

end CauchyHorizon
