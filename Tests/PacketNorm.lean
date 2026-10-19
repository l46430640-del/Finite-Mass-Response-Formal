import CauchyHorizon.Analysis.PacketNorm
import CauchyHorizon.Analysis.PacketBump
import CauchyHorizon.Characteristic.PacketMedian

open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction ContDiff

namespace CauchyHorizon.Tests

-- Each physical critical packet is smooth at u=0 as well as on the open incoming ray.
example {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    {ψ : ℝ →ᵇ ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {L : ℝ} (hL : 0 < L) (E ℓ t : ℝ) :
    ContDiff ℝ ∞ (logarithmicIncoming (1 - 1 / p.toReal) ℓ (normalizedPacket E ψ t L)) := by
  have hp0 : p ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 4).trans_le hp)
  have hq := ENNReal.toReal_pos hp0 hpfin
  exact normalizedIncoming_contDiff hψ (by have := one_div_pos.2 hq; linarith) hL hs E ℓ t

-- Real signed sums preserve corner smoothness, including exact cancellation.
example {ι : Type*} [Fintype ι] {ψ : ℝ →ᵇ ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) {b : ℝ} (hb : b ≠ 1)
    (c E t L : ι → ℝ) (hL : ∀ i, 0 < L i) (ℓ : ℝ) :
    ContDiff ℝ ∞ (logarithmicIncoming b ℓ (fun x => ∑ i, c i * normalizedPacket (E i) ψ (t i) (L i) x)) := by
  have hh := ContDiff.sum (fun i (_hi : i ∈ Finset.univ) =>
    (contDiff_const (c := c i)).mul (normalizedIncoming_contDiff hψ hb (hL i) hs (E i) ℓ (t i)))
  change ContDiff ℝ ∞ (fun u => b * u ^ (b - 1) *
    ∑ i, c i * normalizedPacket (E i) ψ (t i) (L i) (ℓ - Real.log u))
  simpa only [logarithmicIncoming, Finset.mul_sum, mul_assoc, mul_left_comm] using! hh

-- The paper's exact p-th norm power holds eventually for independent positions and widths.
example {p : ℝ≥0∞} (hp : p ≠ 0) (hpfin : p ≠ ⊤)
    {b E U : ℝ} (hb : 0 ≤ b) (hcrit : (b - 1) * p.toReal = -1)
    (hE : 0 ≤ E) (hU : 0 < U) (ψ : ℝ →ᵇ ℝ)
    (hM : 0 < ∫ x, ψ x ^ 2) (hi : Integrable (fun x => |ψ x| ^ p.toReal))
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (ℓ : ℝ) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (ht : Tendsto t atTop atTop) :
    ∀ᶠ n in atTop,
      (eLpNorm (logarithmicIncoming b ℓ (normalizedPacket E ψ (t n) (L n))) p
        (volume.restrict (Icc 0 U))).toReal ^ p.toReal =
        (b ^ p.toReal * ((E / (∫ x, ψ x ^ 2)) ^ (p.toReal / 2) *
          (L n) ^ (1 - p.toReal / 2) * ∫ x, |ψ x| ^ p.toReal)) := by
  filter_upwards [(tendsto_atTop.1 ht) (ℓ - Real.log U)] with n hn
  have hMp : 0 ≤ ∫ x, |ψ x| ^ p.toReal :=
    integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hbase : 0 ≤ b ^ p.toReal * ((E / (∫ x, ψ x ^ 2)) ^ (p.toReal / 2) *
      (L n) ^ (1 - p.toReal / 2) * ∫ x, |ψ x| ^ p.toReal) :=
    mul_nonneg (Real.rpow_nonneg hb _) (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (div_nonneg hE hM.le) _) (Real.rpow_nonneg (hL n).le _)) hMp)
  rw [(normalizedIncoming_lp_on hp hpfin hb hcrit hE (hL n) hU ψ hM hi hs ℓ (t n) hn).2,
    Real.rpow_inv_rpow hbase (ENNReal.toReal_ne_zero.mpr ⟨hp, hpfin⟩)]

-- All shape and moment premises are discharged for the displayed bump at every finite p>=4.
example {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    {E L U n : ℝ} (hE : 0 < E) (hL : 0 < L) (hU : 0 < U) (hn : 1 ≤ n)
    (ℓ : ℝ) (hstart : ℓ - Real.log U ≤ L) :
    let f := fun j => logarithmicIncoming (1 - 1 / p.toReal) ℓ
      (fun x => Real.sqrt (E / ((∫ z, unitPacketBump z ^ 2) * (j * L))) *
        unitPacketBump ((x - j * L) / (j * L)))
    (eLpNorm (f n) p (volume.restrict (Icc 0 U))).toReal /
      (eLpNorm (f 1) p (volume.restrict (Icc 0 U))).toReal = n ^ (1 / p.toReal - 1 / 2) := by
  obtain ⟨hc, hk, hpos, hs, _, hM⟩ := unitPacketBump_properties
  let ψ : ℝ →ᵇ ℝ := (⟨⟨unitPacketBump, hc.continuous⟩, hk⟩ :
    CompactlySupportedContinuousMap ℝ ℝ).toBoundedContinuousFunction
  have hp0 : p ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 4).trans_le hp)
  have hpR : 4 ≤ p.toReal := by simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hpfin hp
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpfin
  have hb : 0 < 1 - 1 / p.toReal := sub_pos.2 ((div_lt_one hq).2 (by linarith only [hpR]))
  have hcrit : (1 - 1 / p.toReal - 1) * p.toReal = -1 := by field_simp; ring
  have hpc : Continuous (fun x => |unitPacketBump x| ^ p.toReal) :=
    hc.continuous.abs.rpow_const (fun _ => Or.inr hq.le)
  have hpk : HasCompactSupport (fun x => |unitPacketBump x| ^ p.toReal) :=
    hk.comp_left (g := fun x : ℝ => |x| ^ p.toReal) (by rw [abs_zero, Real.zero_rpow hq.ne'])
  have hi : Integrable (fun x => |unitPacketBump x| ^ p.toReal) :=
    hpc.integrable_of_hasCompactSupport hpk
  have hpM : 0 < ∫ x, |unitPacketBump x| ^ p.toReal :=
    hpc.integral_pos_of_hasCompactSupport_nonneg_nonzero hpk
      (fun x => Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_pos_of_pos (abs_pos.mpr (hpos (1 / 2) (by constructor <;> norm_num)).ne') _).ne'
  have hP (t w : ℝ) : (normalizedPacket E ψ t w : ℝ → ℝ) =
      fun x => Real.sqrt (E / ((∫ z, unitPacketBump z ^ 2) * w)) *
        unitPacketBump ((x - t) / w) := by
    funext x
    rfl
  simpa only [hP, one_mul] using
    normalizedIncoming_lp_ratio hp0 hpfin hb hcrit hE hL hU hn ψ hM hi hpM hs ℓ hstart

-- The concrete shape's reflection symmetry is an exact identity, including its zero extension.
example (x : ℝ) : unitPacketBump (1 - x) = unitPacketBump x := by
  unfold unitPacketBump
  congr 2
  ring

-- The first half-response time keeps the width term and a common error bound on all rays.
example {K : Type*} [TopologicalSpace K] {a T : ℝ} {t L : ℕ → ℝ}
    {M : ℕ → ℝ → C(K, ℝ)} {Mh : ℕ → C(K, ℝ)}
    (hq : HasMassQuantileAsymptotics unitPacketBump a t L M Mh T) :
    packetCumulative unitPacketBump (1 / 2) = 1 / 2 ∧
      ∀ d > (0 : ℝ), ∀ᶠ n in atTop, ∀ u,
        |firstCrossing (fun v => (M n v - M 0 v) u) T ((1 / 2 : ℝ) * (Mh n - Mh 0) u) -
          (t n + L n / 2) / a| < d * L n := by
  obtain ⟨_, _, _, hs, hi, hM⟩ := unitPacketBump_properties
  apply hq.symmetric_median hi hM hs
  intro x
  unfold unitPacketBump
  congr 2
  ring

end CauchyHorizon.Tests
