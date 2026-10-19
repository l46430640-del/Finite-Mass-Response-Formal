import CauchyHorizon.Analysis.PacketBump
import CauchyHorizon.Analysis.PacketInterference
import CauchyHorizon.Analysis.PacketDensity
import CauchyHorizon.Characteristic.PacketMass

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace CauchyHorizon.Tests

-- This is exactly the zero-extended expression evaluated by the plotting script.
example (y : ℝ) : unitPacketBump y =
    if 0 < y ∧ y < 1 then Real.exp (4 - 1 / (y * (1 - y))) else 0 :=
  unitPacketBump_eq y

example : unitPacketBump 0 = 0 ∧ unitPacketBump 1 = 0 ∧ unitPacketBump (1 / 2) = 1 := by
  norm_num [unitPacketBump_eq]

-- The full nonlinear result now has a concrete shape, with no smoothness or support premises.
example (B : Background) {s l H Hlo : ℝ} {h : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    (hcrit : B.innerRate = (1 - 1 / p.toReal) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hc : ContinuousOn h (Ici 0)) (hb : ∀ v ∈ Ici (0 : ℝ), ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop)
    (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ D : AdmissibleOutgoingData B s l,
      (∀ v ∈ Ici (0 : ℝ), D.tail v = h (v + T)) ∧
      D.upper = H * Real.exp (-s * T) ∧ D.lower = Hlo * Real.exp (-l * T) ∧
      B.PacketMassResponse D hp unitPacketBump E t L ℓ Ucap := by
  obtain ⟨hψ, hcomp, hpos, hsupp, _, _⟩ := unitPacketBump_properties
  exact B.exists_late_packet_mass_response hp hpfin hcrit hks hl hH hHlo hc hb hlo
    hψ hcomp hpos hsupp hE t L hL htop hLtop ℓ Ucap hUcap

-- The separated pair has the fixed component normalization, including both plateau endpoints.
example {y : ℝ} (hy : y ∈ Icc (1 : ℝ) (5 / 4)) :
    packetPairCumulative unitPacketBump (5 / 4) 1 y = 1 / 2 ∧
      packetPairTotal unitPacketBump (5 / 4) 1 = 1 := by
  obtain ⟨hc, hk, _, hs, _, hM⟩ := unitPacketBump_properties
  refine ⟨packetPairCumulative_plateau hM hs hy.1 hy.2 1, ?_⟩
  norm_num [packetPairTotal_separated hc.continuous hk hM hs (by norm_num : (1 : ℝ) ≤ 5 / 4) 1]

-- The two overlapping curves in the same plot retain their distinct terminal energies.
example : 1 < packetPairTotal unitPacketBump (1 / 4) 1 ∧
    0 ≤ packetPairTotal unitPacketBump (1 / 4) (-1) ∧
      packetPairTotal unitPacketBump (1 / 4) (-1) < 1 := by
  obtain ⟨hc, hk, hp, hs, _, _⟩ := unitPacketBump_properties
  exact packetPairTotal_strict_overlap hc.continuous hk hp hs (by norm_num) (by norm_num)

-- The plotted density has unit area and the exact plotted cumulative curve for every n>0.
example {n : ℝ} (hn : 0 < n) (y : ℝ) :
    (∫ x, unitPacketBump ((x - n) / n) ^ 2 / ((∫ z, unitPacketBump z ^ 2) * n)) = 1 ∧
      (∫ x in Iic y, unitPacketBump ((x - n) / n) ^ 2 /
        ((∫ z, unitPacketBump z ^ 2) * n)) = packetCumulative unitPacketBump ((y - n) / n) :=
  packet_density_integrals unitPacketBump_properties.2.2.2.2.2 hn n y

-- The change to x=t/L_* keeps the density's Jacobian, independently of E and L_*.
example {n E L : ℝ} (hn : 0 < n) (hE : 0 < E) (hL : 0 < L) (x : ℝ) :
    (L / E) * (Real.sqrt (E / ((∫ z, unitPacketBump z ^ 2) * (n * L))) *
      unitPacketBump ((x * L - n * L) / (n * L))) ^ 2 =
        unitPacketBump ((x - n) / n) ^ 2 / ((∫ z, unitPacketBump z ^ 2) * n) := by
  have hM := unitPacketBump_properties.2.2.2.2.2
  rw [show (x * L - n * L) / (n * L) = (x - n) / n by field_simp,
    mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

-- For n>=3 the entire fixed window [0,3] precedes the packet; the eventual level is one.
example {n x : ℝ} (hn : 3 ≤ n) (hx : x ∈ Icc (0 : ℝ) 3) :
    packetCumulative unitPacketBump ((x - n) / n) = 0 ∧
      packetCumulative unitPacketBump ((2 * n - n) / n) = 1 := by
  obtain ⟨_, _, _, hs, _, hM⟩ := unitPacketBump_properties
  have hn0 : 0 < n := by linarith only [hn]
  refine ⟨(packetCumulative_exterior hM hs _).1 ?_, (packetCumulative_exterior hM hs _).2 ?_⟩
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hx.2.trans hn)) hn0.le
  · have he : (2 * n - n) / n = 1 := by field_simp; ring
    rw [he]

end CauchyHorizon.Tests
