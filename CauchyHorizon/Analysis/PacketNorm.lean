import CauchyHorizon.Analysis.NormalizedPacket
import CauchyHorizon.Analysis.CriticalIncoming

/-! Incoming packet regularity at the corner and exact norms on the initial interval. -/

open MeasureTheory Set Filter
open scoped ENNReal BoundedContinuousFunction Topology ContDiff

namespace CauchyHorizon

theorem logarithmicIncoming_contDiff_of_upper_support {n : WithTop ℕ∞} {P : ℝ → ℝ}
    (hP : ContDiff ℝ n P) {b T : ℝ} (hb : b ≠ 1) (ℓ : ℝ)
    (hs : ∀ x, T ≤ x → P x = 0) : ContDiff ℝ n (logarithmicIncoming b ℓ P) := by
  apply contDiff_iff_contDiffAt.2
  intro u
  by_cases hu : u = 0
  · subst u
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (Real.exp_pos (ℓ - T))] with u hu
    have huabs : |u| < Real.exp (ℓ - T) := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hu
    by_cases hu0 : u = 0
    · simp only [logarithmicIncoming, hu0, Real.zero_rpow (sub_ne_zero.mpr hb), mul_zero, zero_mul]
    · have hlog := (Real.log_lt_iff_lt_exp (abs_pos.mpr hu0)).2 huabs
      rw [Real.log_abs] at hlog
      rw [logarithmicIncoming, hs _ (by linarith only [hlog]), mul_zero]
  · exact (contDiffAt_const.mul (contDiffAt_id.rpow_const_of_ne hu)).mul
      (hP.contDiffAt.comp u (contDiffAt_const.sub (contDiffAt_id.log hu)))

theorem normalizedIncoming_contDiff {n : WithTop ℕ∞} {ψ : ℝ →ᵇ ℝ}
    (hψ : ContDiff ℝ n ψ) {b L : ℝ} (hb : b ≠ 1) (hL : 0 < L)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) (E ℓ t : ℝ) :
    ContDiff ℝ n (logarithmicIncoming b ℓ (normalizedPacket E ψ t L)) :=
  logarithmicIncoming_contDiff_of_upper_support (normalizedPacket_contDiff hψ E t L) hb ℓ
    (fun x hx => normalizedPacket_support hL E ψ hs t x (Or.inr hx))

theorem normalizedIncoming_lp_on {p : ℝ≥0∞} (hp : p ≠ 0) (hpfin : p ≠ ⊤)
    {b E L U : ℝ} (hb : 0 ≤ b) (hcrit : (b - 1) * p.toReal = -1)
    (hE : 0 ≤ E) (hL : 0 < L) (hU : 0 < U) (ψ : ℝ →ᵇ ℝ)
    (hM : 0 < ∫ x, ψ x ^ 2) (hi : Integrable (fun x => |ψ x| ^ p.toReal))
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (ℓ t : ℝ) (ht : ℓ - Real.log U ≤ t) :
    MemLp (logarithmicIncoming b ℓ (normalizedPacket E ψ t L)) p (volume.restrict (Icc 0 U)) ∧
      (eLpNorm (logarithmicIncoming b ℓ (normalizedPacket E ψ t L)) p
        (volume.restrict (Icc 0 U))).toReal =
        (b ^ p.toReal * ((E / (∫ x, ψ x ^ 2)) ^ (p.toReal / 2) *
          L ^ (1 - p.toReal / 2) * ∫ x, |ψ x| ^ p.toReal)) ^ p.toReal⁻¹ := by
  obtain ⟨hiP, hmoment⟩ := normalizedPacket_moment hE hL ψ hM p.toReal t hi
  obtain ⟨_, hnorm, hlocal⟩ := logarithmicIncoming_critical_lp hp hpfin hb hcrit ℓ
    (normalizedPacket E ψ t L) hiP
  have hsU : Function.support (logarithmicIncoming b ℓ (normalizedPacket E ψ t L)) ⊆ Iic U := by
    intro u hu
    by_contra h
    have huU : U < u := lt_of_not_ge h
    have ht' : ℓ - Real.log u ≤ t := by
      have := Real.log_le_log hU huU.le
      linarith only [ht, this]
    apply hu
    simp only [logarithmicIncoming, normalizedPacket_support hL E ψ hs t _ (Or.inl ht'), mul_zero]
  have he := eLpNorm_restrict_eq_of_support_subset (p := p)
    (μ := volume.restrict (Ici (0 : ℝ))) hsU
  rw [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ici] at he
  refine ⟨(hlocal U).1, ?_⟩
  rw [he, hnorm, hmoment]

theorem normalizedIncoming_lp_ratio {p : ℝ≥0∞} (hp : p ≠ 0) (hpfin : p ≠ ⊤)
    {b E L U n : ℝ} (hb : 0 < b) (hcrit : (b - 1) * p.toReal = -1)
    (hE : 0 < E) (hL : 0 < L) (hU : 0 < U) (hn : 1 ≤ n) (ψ : ℝ →ᵇ ℝ)
    (hM : 0 < ∫ x, ψ x ^ 2) (hi : Integrable (fun x => |ψ x| ^ p.toReal))
    (hMp : 0 < ∫ x, |ψ x| ^ p.toReal)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (ℓ : ℝ) (hstart : ℓ - Real.log U ≤ L) :
    (eLpNorm (logarithmicIncoming b ℓ (normalizedPacket E ψ (n * L) (n * L))) p
        (volume.restrict (Icc 0 U))).toReal /
      (eLpNorm (logarithmicIncoming b ℓ (normalizedPacket E ψ L L)) p
        (volume.restrict (Icc 0 U))).toReal = n ^ (1 / p.toReal - 1 / 2) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have ht : ℓ - Real.log U ≤ n * L :=
    hstart.trans (by nlinarith only [hL, hn])
  have h1 := (normalizedIncoming_lp_on hp hpfin hb.le hcrit hE.le hL hU ψ hM hi hs ℓ L hstart).2
  have hn' := (normalizedIncoming_lp_on hp hpfin hb.le hcrit hE.le (mul_pos hn0 hL) hU
    ψ hM hi hs ℓ (n * L) ht).2
  let A := b ^ p.toReal * ((E / (∫ x, ψ x ^ 2)) ^ (p.toReal / 2) *
    L ^ (1 - p.toReal / 2) * ∫ x, |ψ x| ^ p.toReal)
  have hA : 0 < A := by dsimp only [A]; positivity
  have he : b ^ p.toReal * ((E / (∫ x, ψ x ^ 2)) ^ (p.toReal / 2) *
      (n * L) ^ (1 - p.toReal / 2) * ∫ x, |ψ x| ^ p.toReal) =
      n ^ (1 - p.toReal / 2) * A := by
    rw [Real.mul_rpow hn0.le hL.le]
    dsimp only [A]
    ring
  rw [hn', h1, he]
  change (n ^ (1 - p.toReal / 2) * A) ^ p.toReal⁻¹ / A ^ p.toReal⁻¹ = _
  rw [Real.mul_rpow (Real.rpow_nonneg hn0.le _) hA.le,
    ← Real.rpow_mul hn0.le, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hA _).ne']
  congr 1
  field_simp [ENNReal.toReal_ne_zero.mpr ⟨hp, hpfin⟩]

end CauchyHorizon
