import CauchyHorizon.Analysis.PacketPair

/-! The terminal pair response keeps the overlap integral and its relative sign. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem packetPairTotal_interference {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hcomp : HasCompactSupport ψ) (hM : 0 < ∫ z, ψ z ^ 2) (δ σ : ℝ) :
    packetPairTotal ψ δ σ = (1 + σ ^ 2) / 2 +
      σ * (∫ z, ψ z * ψ (z - δ)) / (∫ z, ψ z ^ 2) := by
  have hsq : HasCompactSupport (fun z => ψ z ^ 2) :=
    hcomp.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have hi : Integrable (fun z => ψ z ^ 2) := (hc.pow 2).integrable_of_hasCompactSupport hsq
  have hj : Integrable (fun z => ψ (z - δ) ^ 2) := by
    simpa only [sub_eq_add_neg] using hi.comp_add_right (-δ)
  have hm : Integrable (fun z => ψ z * ψ (z - δ)) :=
    (hc.mul (hc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      hcomp.mul_right
  have hsum : Integrable (fun z => ψ z ^ 2 + (2 * σ) * (ψ z * ψ (z - δ))) :=
    hi.add (hm.const_mul (2 * σ))
  unfold packetPairTotal
  simp_rw [show ∀ z, (ψ z + σ * ψ (z - δ)) ^ 2 =
    ψ z ^ 2 + (2 * σ) * (ψ z * ψ (z - δ)) + σ ^ 2 * ψ (z - δ) ^ 2 from fun _ => by ring]
  rw [integral_add hsum (hj.const_mul (σ ^ 2)),
    integral_add hi (hm.const_mul (2 * σ)), integral_const_mul, integral_const_mul,
    integral_sub_right_eq_self (fun z => ψ z ^ 2) δ]
  field_simp [hM.ne']
  ring

theorem packetPairTotal_strict_overlap {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hcomp : HasCompactSupport ψ) (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    1 < packetPairTotal ψ δ 1 ∧ 0 ≤ packetPairTotal ψ δ (-1) ∧
      packetPairTotal ψ δ (-1) < 1 := by
  have hnonneg (x : ℝ) : 0 ≤ ψ x := by
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · exact (hpos x hx).le
    · rw [hsupp x hx]
  have hsq : HasCompactSupport (fun z => ψ z ^ 2) :=
    hcomp.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have hM : 0 < ∫ z, ψ z ^ 2 :=
    (hc.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero hsq (fun z => sq_nonneg _)
      (pow_ne_zero 2 (hpos (1 / 2) (by constructor <;> norm_num)).ne')
  have hx : (1 + δ) / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hy : (1 + δ) / 2 - δ ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hm : 0 < ∫ z, ψ z * ψ (z - δ) :=
    (hc.mul (hc.comp (continuous_id.sub continuous_const))).integral_pos_of_hasCompactSupport_nonneg_nonzero
      hcomp.mul_right (fun z => mul_nonneg (hnonneg z) (hnonneg (z - δ)))
      (mul_pos (hpos _ hx) (hpos _ hy)).ne'
  have hp := packetPairTotal_interference hc hcomp hM δ 1
  have hn := packetPairTotal_interference hc hcomp hM δ (-1)
  have hratio := div_pos hm hM
  refine ⟨?_, div_nonneg (integral_nonneg (fun z => sq_nonneg _)) (by positivity), ?_⟩
  · norm_num at hp
    linarith
  · norm_num at hn
    rw [neg_div] at hn
    linarith

theorem packetPairTotal_separated {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hcomp : HasCompactSupport ψ) (hM : 0 < ∫ z, ψ z ^ 2)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) {δ : ℝ} (hδ : 1 ≤ δ) (σ : ℝ) :
    packetPairTotal ψ δ σ = (1 + σ ^ 2) / 2 := by
  have hz (z : ℝ) : ψ z * ψ (z - δ) = 0 := by
    by_cases hx : z ∈ Ioo (0 : ℝ) 1
    · rw [hsupp (z - δ) (by intro hy; have := hy.1; have := hx.2; linarith), mul_zero]
    · rw [hsupp z hx, zero_mul]
  rw [packetPairTotal_interference hc hcomp hM δ σ]
  simp only [hz, integral_zero, mul_zero, zero_div, add_zero]

theorem packetPairCumulative_plateau {ψ : ℝ → ℝ} (hM : 0 < ∫ z, ψ z ^ 2)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) {δ y : ℝ}
    (hy : 1 ≤ y) (hyδ : y ≤ δ) (σ : ℝ) :
    packetPairCumulative ψ δ σ y = 1 / 2 := by
  have he : (∫ z in Iic y, (ψ z + σ * ψ (z - δ)) ^ 2) = ∫ z in Iic y, ψ z ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro z hz
    dsimp only
    have hzδ : z - δ ∉ Ioo (0 : ℝ) 1 := by
      intro h
      have := hz.trans hyδ
      linarith only [h.1, this]
    rw [hsupp _ hzδ, mul_zero, add_zero]
  have hf : (∫ z in Iic y, ψ z ^ 2) = ∫ z, ψ z ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [hsupp z (fun h => hz (h.2.le.trans hy)), zero_pow (by decide)])
  rw [packetPairCumulative, he, hf]
  field_simp

end CauchyHorizon
