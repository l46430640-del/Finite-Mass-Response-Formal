import CauchyHorizon.Characteristic.PacketMass
import CauchyHorizon.Characteristic.PairPacketMass

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace CauchyHorizon.Tests

-- The mass transformation includes its moving lower integration endpoint.
example (M S v : ℝ) (h : ℝ → ℝ) :
    horizonMass M (fun w => h (w - S)) v = horizonMass M h (v - S) := by
  simpa only [sub_eq_add_neg] using horizonMass_translate M h (-S) v

-- The extension outside the physical half-line cannot change the translated mass.
example (B : Background) {s l T v : ℝ} (D : AdmissibleOutgoingData B s l) (h : ℝ → ℝ)
    (heq : ∀ w ∈ Ici (0 : ℝ), D.tail w = h (w + T)) (hv : 0 ≤ v) :
    horizonMass B.mass D.tail v = horizonMass B.mass h (v + T) := by
  rw [← horizonMass_translate]
  exact horizonMass_congr_future heq hv B.mass

-- The retained decay supplies the terminal boundary condition, with no separate limit premise.
example (B : Background) {s l : ℝ} (D : AdmissibleOutgoingData B s l) :
    Tendsto D.radius atTop (𝓝 B.event) := by
  have hexp : Tendsto (fun v : ℝ => Real.exp (-(2 * s) * v)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith [D.rate_pos]))
  have hzero : Tendsto (fun v => D.radius v - B.event) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [mul_zero] using hexp.const_mul D.deviation)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    exact D.radius_decay v hv
  simpa only [sub_add_cancel, zero_add] using hzero.add_const B.event

-- A continuous tail with a cusp supplies the terminal radius and both translated constants.
example (B : Background) {s : ℝ} (hs : 0 < s) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ D : AdmissibleOutgoingData B s s,
      (∀ v ∈ Ici (0 : ℝ), D.tail v =
        Real.exp (-s * (v + T)) * (1 + min |v + T - 1| 1)) ∧
      D.upper = 2 * Real.exp (-s * T) ∧ D.lower = Real.exp (-s * T) ∧
      B.inner < D.radius 0 := by
  let h := fun v : ℝ => Real.exp (-s * v) * (1 + min |v - 1| 1)
  have hc : Continuous h := by fun_prop
  have hm (v : ℝ) : 0 ≤ min |v - 1| 1 := le_min (abs_nonneg _) (by norm_num)
  have hb (v : ℝ) (_hv : v ∈ Ici (0 : ℝ)) : ‖h v‖ ≤ 2 * Real.exp (-s * v) := by
    have hp := Real.exp_pos (-s * v)
    have hu := min_le_right |v - 1| (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [h]; positivity)]
    dsimp only [h]
    nlinarith only [hp, hu]
  have hlo (v : ℝ) (_hv : v ∈ Ici (0 : ℝ)) : 1 * Real.exp (-s * v) ≤ h v := by
    dsimp only [h]
    nlinarith only [Real.exp_pos (-s * v), hm v]
  obtain ⟨T, hT, D, heq, hupper, hlower⟩ :=
    B.exists_admissible_late_data hs (by norm_num) (by norm_num) hc.continuousOn hb hlo
  exact ⟨T, hT, D, heq, hupper, by simpa only [one_mul] using hlower, D.radius_initial⟩

-- At p=4 the complete mass/continuation conclusion starts from the original half-line tail alone.
example (B : Background) {s l H Hlo : ℝ} {h : ℝ → ℝ}
    (hcrit : B.innerRate = (3 / 4) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hc : ContinuousOn h (Ici 0)) (hb : ∀ v ∈ Ici (0 : ℝ), ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop)
    (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ D : AdmissibleOutgoingData B s l,
      (∀ v ∈ Ici (0 : ℝ), D.tail v = h (v + T)) ∧
      D.upper = H * Real.exp (-s * T) ∧ D.lower = Hlo * Real.exp (-l * T) ∧
      B.PacketMassResponse D (p := 4) le_rfl ψ E t L ℓ Ucap := by
  apply B.exists_late_packet_mass_response le_rfl (by norm_num) ?_ hks hl hH hHlo
    hc hb hlo hψ hcomp hpos hsupp hE t L hL htop hLtop ℓ Ucap hUcap
  norm_num only [ENNReal.toReal_ofNat] at *
  convert hcrit using 1

-- All signed coefficients are allowed; the complete finite-sum conclusion uses only the original tail.
example (B : Background) {s l H Hlo : ℝ} {h : ℝ → ℝ}
    (hcrit : B.innerRate = (3 / 4) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hc : ContinuousOn h (Ici 0)) (hb : ∀ v ∈ Ici (0 : ℝ), ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (c E : ι → ℝ) (hE : ∀ i, 0 < E i) (t L : ι → ℕ → ℝ)
    (hL : ∀ i n, 0 < L i n) (htop : ∀ i, Tendsto (t i) atTop atTop)
    (hLtop : ∀ i, Tendsto (L i) atTop atTop) (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ D : AdmissibleOutgoingData B s l,
      (∀ v ∈ Ici (0 : ℝ), D.tail v = h (v + T)) ∧
      D.upper = H * Real.exp (-s * T) ∧ D.lower = Hlo * Real.exp (-l * T) ∧
      B.FinitePacketMassResponse D (p := 4) le_rfl ψ c E t L ℓ Ucap := by
  apply B.exists_late_finite_packet_mass_response le_rfl (by norm_num) ?_ hks hl hH hHlo
    hc hb hlo hψ hcomp hpos hsupp c E hE t L hL htop hLtop ℓ Ucap hUcap
  norm_num
  exact hcrit

-- Nonnegative separation needs no relation between the independently diverging location and width.
example (B : Background) {s l H Hlo : ℝ} {h : ℝ → ℝ}
    (hcrit : B.innerRate = (3 / 4) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hc : ContinuousOn h (Ici 0)) (hb : ∀ v ∈ Ici (0 : ℝ), ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop)
    (δ σ : ℝ) (hδ : 0 ≤ δ) (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ D : AdmissibleOutgoingData B s l,
      (∀ v ∈ Ici (0 : ℝ), D.tail v = h (v + T)) ∧
      D.upper = H * Real.exp (-s * T) ∧ D.lower = Hlo * Real.exp (-l * T) ∧
      B.PairPacketMassResponse D (p := 4) le_rfl ψ E t L δ σ ℓ Ucap := by
  have htop₂ : Tendsto (fun n => t n + δ * L n) atTop atTop := by
    apply tendsto_atTop.2
    intro R
    filter_upwards [(tendsto_atTop.1 htop) R] with n hn
    exact hn.trans (le_add_of_nonneg_right (mul_nonneg hδ (hL n).le))
  apply B.exists_late_pair_packet_mass_response le_rfl (by norm_num) ?_ hks hl hH hHlo
    hc hb hlo hψ hcomp hpos hsupp hE t L hL htop hLtop δ σ htop₂ ℓ Ucap hUcap
  norm_num
  exact hcrit

end CauchyHorizon.Tests
