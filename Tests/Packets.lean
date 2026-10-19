import CauchyHorizon.Analysis.PacketData
import CauchyHorizon.Analysis.PacketCumulative
import CauchyHorizon.Analysis.EscapingProfile

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology ContDiff

namespace CauchyHorizon.Tests

-- The manuscript's fixed smooth shape supplies the actual profile and derivative sequence.
example {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop) (b ℓ : ℝ) :
    ∃ P Q : ℕ → ℝ →ᵇ ℝ, P 0 = 0 ∧
      (∀ n, n ≠ 0 → ∀ x, P n x =
        Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) * ψ ((x - t n) / L n)) ∧
      (∀ n x, HasDerivAt (P n) (Q n x) x) ∧
      (∀ n, ContDiffOn ℝ 1 (logarithmicIncoming b ℓ (P n)) (Ioi 0)) ∧
      (∀ n, Integrable (fun x => P n x ^ 2) ∧ (∫ x, P n x ^ 2) ≤ E) ∧
      (∀ n, n ≠ 0 → (∫ x, P n x ^ 2) = E) ∧
      (∀ n, Integrable (fun x => Q n x ^ 2)) ∧
      Tendsto (fun n => ∫ x, Q n x ^ 2) atTop (𝓝 0) ∧
      (∀ n x, x ≤ t n → P n x = 0) ∧
      ∀ T : ℝ, ∀ᶠ n in atTop, ∀ x ≤ T, P n x = 0 := by
  obtain ⟨Φ, Φ', he, _he', hd, hΦ, hΦ', hM⟩ := smooth_packet_shape hψ hcomp
    (hpos (1 / 2) (by norm_num)).ne'
  have hΦsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → Φ x = 0 := fun x hx => (he x).trans (hsupp x hx)
  obtain ⟨P, Q, hP0, _hQ0, hP, _hQ, hPQ, hPC, hEi, hEE, hQi, _hQE, hQt, hPs, hEsc⟩ :=
    normalizedPacket_sequence hE Φ Φ' hd hΦ hΦ' hM hΦsupp t L hL htop hLtop
  refine ⟨P, Q, hP0, ?_, hPQ, fun n => logarithmicIncoming_contDiff (hPC n) b ℓ,
    hEi, hEE, hQi, hQt, fun n x hx => hPs n x (Or.inl hx), hEsc⟩
  intro n hn x
  rw [hP n hn]
  change Real.sqrt (E / ((∫ y, Φ y ^ 2) * L n)) * Φ ((x - t n) / L n) = _
  simp_rw [he]

-- Support escape in the physical incoming coordinate needs no relation between delay and width.
example {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (E : ℝ) (ψ : ℝ →ᵇ ℝ)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) (b ℓ : ℝ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u ∈ Ici η,
      logarithmicIncoming b ℓ (normalizedPacket E ψ (t n) (L n)) u = 0 := by
  have hfront : Tendsto (fun n => t n - ℓ) atTop atTop := by
    apply tendsto_atTop.2
    intro R
    filter_upwards [(tendsto_atTop.1 ht) (R + ℓ)] with n hn
    linarith only [hn]
  exact (logarithmicIncoming_eventually_zero b hfront
    (fun n x hx => normalizedPacket_support (hL n) E ψ hsupp (t n) x (Or.inl hx))).1

-- At p=4 the profile moment tends to zero while its quadratic energy stays fixed.
example {E : ℝ} (hE : 0 < E) (ψ : ℝ →ᵇ ℝ)
    (h2 : Integrable (fun x => ψ x ^ 2)) (h4 : Integrable (fun x => |ψ x| ^ (4 : ℝ)))
    (hM : 0 < ∫ x, ψ x ^ 2) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (hLtop : Tendsto L atTop atTop) :
    (∀ n, (∫ x, normalizedPacket E ψ (t n) (L n) x ^ 2) = E) ∧
      Tendsto (fun n => ∫ x, |normalizedPacket E ψ (t n) (L n) x| ^ (4 : ℝ)) atTop (𝓝 0) := by
  exact ⟨fun n => (normalizedPacket_energy hE.le (hL n) ψ h2 hM (t n)).2,
    normalizedPacket_moment_tendsto hE.le ψ hM (by norm_num) h4 t L hL hLtop⟩

-- The critical p=4 change of measure retains the exact factor (3/4)^4.
example (P : ℝ →ᵇ ℝ) (hP : Integrable (fun x => |P x| ^ (4 : ℝ))) (ℓ : ℝ) :
    MemLp (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Ici 0)) ∧
      (eLpNorm (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Ici 0))).toReal =
        ((3 / 4 : ℝ) ^ (4 : ℝ) * ∫ x, |P x| ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
  have hh := logarithmicIncoming_critical_lp (p := 4) (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num) ℓ P (by simpa only [ENNReal.toReal_ofNat] using hP)
  simpa only [ENNReal.toReal_ofNat, one_div] using ⟨hh.1, hh.2.1⟩

-- The full original sequence satisfies both incoming budgets before its interval is chosen.
example {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop) (ℓ : ℝ) :
    ∃ A Apt : ℝ, 0 < A ∧ 0 < Apt ∧ ∃ P : ℕ → ℝ →ᵇ ℝ, P 0 = 0 ∧
      (∀ n, n ≠ 0 → ∀ x, P n x = Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) *
        ψ ((x - t n) / L n)) ∧
      (∀ n, n ≠ 0 → (∫ x, P n x ^ 2) = E) ∧
      (∀ U : ℝ, 0 < U →
        (∀ n, 0 ≤ primitiveEnergy (3 / 4) (logarithmicIncoming (3 / 4) ℓ (P n)) U ∧
          primitiveEnergy (3 / 4) (logarithmicIncoming (3 / 4) ℓ (P n)) U ≤ E) ∧
        Tendsto (fun n => primitiveEnergy (3 / 4) (logarithmicIncoming (3 / 4) ℓ (P n)) U)
          atTop (𝓝 E)) ∧
      ∀ δ : ℝ,
        (∀ n, MemLp (logarithmicIncoming (3 / 4) ℓ (P n)) 4 (volume.restrict (Icc 0 δ))) ∧
        (∀ n, (eLpNorm (logarithmicIncoming (3 / 4) ℓ (P n)) 4
          (volume.restrict (Icc 0 δ))).toReal ≤ A) ∧
        (∀ n, ∀ᵐ u ∂volume.restrict (Icc 0 δ),
          |logarithmicIncoming (3 / 4) ℓ (P n) u| ≤ Apt * u ^ (-1 / 4 : ℝ)) ∧
        Tendsto (fun n => (eLpNorm (logarithmicIncoming (3 / 4) ℓ (P n)) 4
          (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) := by
  obtain ⟨A, Apt, hA, hApt, P, _Q, hP0, _hQ0, hformula, _hd, _hc, _hEi, hEE, _hQi, _hQt, _hs, _ht, hprimitive, hdata⟩ :=
    smooth_packet_incoming_data (p := 4) le_rfl (by norm_num) hψ hcomp hpos hsupp hE
      t L hL htop hLtop ℓ
  norm_num only [ENNReal.toReal_ofNat] at hprimitive
  refine ⟨A, Apt, hA, hApt, P, hP0, hformula, hEE, hprimitive, ?_⟩
  intro δ
  have hh := hdata δ
  norm_num only [ENNReal.toReal_ofNat] at hh
  simpa only [neg_div] using hh

-- The exact cumulative identity uses the same normalized packet as the incoming construction.
example {E L : ℝ} (hE : 0 ≤ E) (hL : 0 < L) (ψ : ℝ →ᵇ ℝ)
    (hM : 0 < ∫ x, ψ x ^ 2) (t z : ℝ) :
    (∫ x in Iic z, normalizedPacket E ψ t L x ^ 2) =
      E * packetCumulative ψ ((z - t) / L) :=
  packet_cumulative_integral hE hL ψ hM t z

-- A fixed phase of either sign has a uniform inverse-width error.
example {ψ : ℝ → ℝ} (hi : Integrable (fun x => ψ x ^ 2))
    (hM : 0 < ∫ x, ψ x ^ 2) {R L : ℝ} (hb : ∀ x, |ψ x| ≤ R)
    (hL : 0 < L) (ℓ y : ℝ) :
    |packetCumulative ψ (y + ℓ / L) - packetCumulative ψ y| ≤
      (R ^ 2 / (∫ x, ψ x ^ 2)) * |ℓ| / L := by
  simpa only [add_sub_cancel_left, abs_div, abs_of_pos hL, mul_div_assoc] using
    packetCumulative_sub_le hi hM hb y (y + ℓ / L)

-- The reference primitive energy vanishes on every interval, including a retained finite prefix.
example (b U : ℝ) : primitiveEnergy b (fun _ => 0) U = 0 := by
  simp [primitiveEnergy]

example (b : ℝ) (f : ℝ → ℝ) : primitiveEnergy b f 0 = 0 := by
  simp [primitiveEnergy]

-- The physical du/u measure gives exactly the restricted logarithmic energy at critical p=4.
example {U uStar : ℝ} (hU : 0 < U) (B : ℝ →ᵇ ℝ)
    (hB : Integrable (fun t => B t ^ 2)) :
    primitiveEnergy (3 / 4) (logarithmicIncoming (3 / 4) (Real.log uStar) B) U =
      ∫ t in Ioi (Real.log uStar - Real.log U),
        ((3 / 4) * terminalGreen (by norm_num : (0 : ℝ) < 3 / 4) B t) ^ 2 :=
  (logarithmicIncoming_primitive_energy (by norm_num) hU (Real.log uStar) B hB).2

-- The quantitative constant is 2/b, with no positivity assumption on the profile or derivative.
example {U : ℝ} (hU : 0 < U) (ℓ : ℝ) (B D : ℝ →ᵇ ℝ)
    (hd : ∀ t, HasDerivAt B (D t) t) (hB : Integrable (fun t => B t ^ 2))
    (hD : Integrable (fun t => D t ^ 2))
    (hsupp : ∀ t, t ≤ ℓ - Real.log U → B t = 0) :
    |primitiveEnergy (3 / 4) (logarithmicIncoming (3 / 4) ℓ B) U - ∫ t, B t ^ 2| ≤
      (8 / 3) * Real.sqrt (∫ t, B t ^ 2) * Real.sqrt (∫ t, D t ^ 2) := by
  rw [(logarithmicIncoming_primitive_energy (by norm_num) hU ℓ B hB).2]
  convert terminalGreen_restricted_energy (by norm_num : (0 : ℝ) < 3 / 4) B D hd hB hD hsupp using 1
  norm_num

-- Reversing the actual incoming scalar sign preserves its primitive energy.
example (b U : ℝ) (f : ℝ → ℝ) :
    primitiveEnergy b (fun u => -f u) U = primitiveEnergy b f U := by
  simp only [primitiveEnergy, intervalIntegral.integral_neg, mul_neg, neg_sq]

end CauchyHorizon.Tests
