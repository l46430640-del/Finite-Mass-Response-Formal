import CauchyHorizon.Analysis.NormalizedPacket
import CauchyHorizon.Analysis.CriticalIncoming
import CauchyHorizon.Analysis.PrimitiveEnergy
import Mathlib.Topology.Order.LiminfLimsup

/-! The full explicit packet sequence has common incoming data budgets before choosing its width. -/

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ENNReal Topology ContDiff

namespace CauchyHorizon

theorem smooth_packet_incoming_data {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E)
    (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop) (ℓ : ℝ) :
    ∃ A Apt : ℝ, 0 < A ∧ 0 < Apt ∧ ∃ P Q : ℕ → ℝ →ᵇ ℝ, P 0 = 0 ∧ Q 0 = 0 ∧
      (∀ n, n ≠ 0 → ∀ x, P n x = Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) *
        ψ ((x - t n) / L n)) ∧
      (∀ n x, HasDerivAt (P n) (Q n x) x) ∧ (∀ n, ContDiff ℝ 1 (P n)) ∧
      (∀ n, Integrable (fun x => P n x ^ 2) ∧ (∫ x, P n x ^ 2) ≤ E) ∧
      (∀ n, n ≠ 0 → (∫ x, P n x ^ 2) = E) ∧
      (∀ n, Integrable (fun x => Q n x ^ 2)) ∧
      Tendsto (fun n => ∫ x, Q n x ^ 2) atTop (𝓝 0) ∧
      (∀ n x, x ≤ t n → P n x = 0) ∧
      Tendsto (fun n => t n - ℓ) atTop atTop ∧
      (∀ U : ℝ, 0 < U →
        (∀ n, 0 ≤ primitiveEnergy (1 - 1 / p.toReal)
          (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U ∧
          primitiveEnergy (1 - 1 / p.toReal) (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U ≤ E) ∧
        Tendsto (fun n => primitiveEnergy (1 - 1 / p.toReal)
          (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U) atTop (𝓝 E)) ∧
      ∀ δ : ℝ,
        (∀ n, MemLp (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p (volume.restrict (Icc 0 δ))) ∧
        (∀ n, (eLpNorm (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p
          (volume.restrict (Icc 0 δ))).toReal ≤ A) ∧
        (∀ n, ∀ᵐ u ∂volume.restrict (Icc 0 δ),
          |logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n) u| ≤ Apt * u ^ (-1 / p.toReal)) ∧
        Tendsto (fun n => (eLpNorm (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p
          (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 4).trans_le hp)
  have hpR : 4 ≤ p.toReal := by simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hpfin hp
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  let b := 1 - 1 / p.toReal
  have hb : 0 < b := by
    dsimp only [b]
    exact sub_pos.2 ((div_lt_one hq).2 (by linarith only [hpR]))
  have hcrit : (b - 1) * p.toReal = -1 := by
    dsimp only [b]
    field_simp
    ring
  obtain ⟨Φ, Φ', he, _he', hd, hΦ, hΦ', hM⟩ := smooth_packet_shape hψ hcomp
    (hpos (1 / 2) (by norm_num)).ne'
  have hΦsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → Φ x = 0 := fun x hx => (he x).trans (hsupp x hx)
  have hΦp : Integrable (fun x => |Φ x| ^ p.toReal) := by
    have hc : Continuous (fun x => |ψ x| ^ p.toReal) := hψ.continuous.abs.rpow_const (fun _ => Or.inr hq.le)
    have hs : HasCompactSupport (fun x => |ψ x| ^ p.toReal) :=
      hcomp.comp_left (g := fun x : ℝ => |x| ^ p.toReal) (by rw [abs_zero, Real.zero_rpow hq.ne'])
    simpa only [he] using hc.integrable_of_hasCompactSupport hs
  let B := fun n => normalizedPacket E Φ (t n) (L n)
  have hBp n := normalizedPacket_moment hE.le (hL n) Φ hM p.toReal (t n) hΦp
  have hBlim := normalizedPacket_moment_tendsto hE.le Φ hM (by linarith only [hpR]) hΦp t L hL hLtop
  have hbase : Tendsto (fun n => b ^ p.toReal * ∫ x, |B n x| ^ p.toReal) atTop (𝓝 0) := by
    simpa only [mul_zero] using hBlim.const_mul (b ^ p.toReal)
  have hnormlim := hbase.rpow_const_nhds_zero (inv_pos.2 hq)
  have hpointlim : Tendsto (fun n => b * ‖B n‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (normalizedPacket_norm_tendsto E Φ t L hLtop).const_mul b
  obtain ⟨A₀, hA₀⟩ := hnormlim.bddAbove_range
  obtain ⟨Apt₀, hApt₀⟩ := hpointlim.bddAbove_range
  let A := max 1 A₀
  let Apt := max 1 Apt₀
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hApt : 0 < Apt := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨P, Q, hP0, hQ0, hP, _hQ, hPQ, hPC, hEi, hEE, hQi, _hQE, hQt, hPs, hEsc⟩ :=
    normalizedPacket_sequence hE Φ Φ' hd hΦ hΦ' hM hΦsupp
      t L hL htop hLtop
  have hPp (n : ℕ) : Integrable (fun x => |P n x| ^ p.toReal) := by
    by_cases hn : n = 0
    · subst n
      simpa only [hP0, BoundedContinuousFunction.coe_zero, Pi.zero_apply, abs_zero,
        Real.zero_rpow hq.ne'] using (show Integrable (fun _ : ℝ => (0 : ℝ)) from integrable_zero _ _ _)
    · rw [hP n hn]
      exact (hBp n).1
  have hPlim : Tendsto (fun n => ∫ x, |P n x| ^ p.toReal) atTop (𝓝 0) := by
    apply hBlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [hP n hn.ne']
  have hglobal n := logarithmicIncoming_critical_lp hp0 hpfin hb.le hcrit ℓ (P n) (hPp n)
  have hnorm (n : ℕ) : (eLpNorm (logarithmicIncoming b ℓ (P n)) p (volume.restrict (Ici 0))).toReal ≤ A := by
    by_cases hn : n = 0
    · subst n
      have hz : logarithmicIncoming b ℓ (P 0) = fun _ => (0 : ℝ) := by
        ext u
        rw [hP0]
        exact mul_zero _
      rw [hz]
      simpa only [eLpNorm_zero', ENNReal.toReal_zero] using hA.le
    · rw [hP n hn, (logarithmicIncoming_critical_lp hp0 hpfin hb.le hcrit ℓ (B n) (hBp n).1).2.1]
      exact (hA₀ (mem_range_self n)).trans (le_max_right _ _)
  have hpoint (n : ℕ) : b * ‖P n‖ ≤ Apt := by
    by_cases hn : n = 0
    · subst n
      simpa only [hP0, norm_zero, mul_zero] using hApt.le
    · rw [hP n hn]
      exact (hApt₀ (mem_range_self n)).trans (le_max_right _ _)
  refine ⟨A, Apt, hA, hApt, P, Q, hP0, hQ0, ?_, hPQ, hPC, hEi, hEE, hQi, hQt,
    (fun n x hx => hPs n x (Or.inl hx)), ?_, ?_, ?_⟩
  · intro n hn x
    rw [hP n hn]
    change Real.sqrt (E / ((∫ y, Φ y ^ 2) * L n)) * Φ ((x - t n) / L n) = _
    simp_rw [he]
  · apply tendsto_atTop.2
    intro R
    filter_upwards [(tendsto_atTop.1 htop) (R + ℓ)] with n hn
    linarith only [hn]
  · intro U hU
    have he := logarithmicIncoming_primitive_energy_tendsto hb P Q hPQ
      (fun n => (hEi n).1) (fun n => (hEi n).2) hQi hQt hEsc ℓ hU
    have hEseq : Tendsto (fun n => ∫ x, P n x ^ 2) atTop (𝓝 E) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact (hEE n hn.ne').symm
    exact ⟨he.1, by simpa only [sub_add_cancel, zero_add] using he.2.add hEseq⟩
  · intro δ
    refine ⟨(fun n => ((hglobal n).2.2 δ).1), ?_, ?_,
      (logarithmicIncoming_critical_tendsto hp0 hpfin hb.le hcrit (fun _ => ℓ) P hPp hPlim δ).2⟩
    · intro n
      exact ((hglobal n).2.2 δ).2.trans ((hglobal n).2.1.symm.le.trans (hnorm n))
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (volume.restrict (Icc (0 : ℝ) δ)).ae_ne 0] with u hu hne
      have hu0 : 0 < u := hu.1.lt_of_ne hne.symm
      have hexp : b - 1 = -1 / p.toReal := by dsimp only [b]; ring
      change |b * u ^ (b - 1) * P n (ℓ - Real.log u)| ≤ _
      rw [abs_mul, abs_of_pos (mul_pos hb (Real.rpow_pos_of_pos hu0 _)), hexp]
      calc
        _ ≤ b * u ^ (-1 / p.toReal) * ‖P n‖ :=
          mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using (P n).norm_coe_le_norm (ℓ - Real.log u))
            (mul_pos hb (Real.rpow_pos_of_pos hu0 _)).le
        _ = (b * ‖P n‖) * u ^ (-1 / p.toReal) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hpoint n) (Real.rpow_nonneg hu0.le _)

end CauchyHorizon
