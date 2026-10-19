import CauchyHorizon.Analysis.PacketCumulative
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue

/-! The packet cumulative distribution is an order isomorphism of the unit interval. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem packetCumulative_monotone {ψ : ℝ → ℝ}
    (hi : Integrable (fun x => ψ x ^ 2)) (hM : 0 < ∫ x, ψ x ^ 2) :
    Monotone (packetCumulative ψ) := by
  intro x y hxy
  apply (div_le_div_iff_of_pos_right hM).2
  rw [← sub_nonneg, intervalIntegral.integral_Iic_sub_Iic
    hi.integrableOn hi.integrableOn]
  exact intervalIntegral.integral_nonneg hxy (fun _ _ => sq_nonneg _)

theorem packetCumulative_strictMonoOn {ψ : ℝ → ℝ}
    (hi : Integrable (fun x => ψ x ^ 2)) (hM : 0 < ∫ x, ψ x ^ 2)
    (hp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x) :
    StrictMonoOn (packetCumulative ψ) (Icc 0 1) := by
  intro x hx y hy hxy
  apply (div_lt_div_iff_of_pos_right hM).2
  rw [← sub_pos, intervalIntegral.integral_Iic_sub_Iic
    hi.integrableOn hi.integrableOn]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on hi.intervalIntegrable
    (fun z hz => sq_pos_of_pos (hp z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩)) hxy

theorem packetCumulative_endpoints {ψ : ℝ → ℝ} (hM : 0 < ∫ x, ψ x ^ 2)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) :
    packetCumulative ψ 0 = 0 ∧ packetCumulative ψ 1 = 1 := by
  constructor
  · have hz : (∫ x in Iic (0 : ℝ), ψ x ^ 2) = 0 := by
      calc
        _ = ∫ _x in Iic (0 : ℝ), (0 : ℝ) :=
          setIntegral_congr_fun measurableSet_Iic (fun x hx => by
            rw [hs x (fun h => (not_lt_of_ge hx) h.1), zero_pow (by decide)])
        _ = 0 := by simp
    simp only [packetCumulative, hz, zero_div]
  · have he : (∫ x in Iic (1 : ℝ), ψ x ^ 2) = ∫ x, ψ x ^ 2 :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hs x (fun h => hx h.2.le), zero_pow (by decide)])
    simp only [packetCumulative, he, div_self hM.ne']

theorem packetCumulative_continuous {ψ : ℝ → ℝ}
    (hi : Integrable (fun x => ψ x ^ 2)) (hM : 0 < ∫ x, ψ x ^ 2)
    {R : ℝ} (hb : ∀ x, |ψ x| ≤ R) : Continuous (packetCumulative ψ) := by
  have hl : LipschitzWith ⟨R ^ 2 / (∫ x, ψ x ^ 2), div_nonneg (sq_nonneg _) hM.le⟩
      (packetCumulative ψ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |packetCumulative ψ x - packetCumulative ψ y| ≤
      (R ^ 2 / (∫ z, ψ z ^ 2)) * |x - y|
    exact packetCumulative_sub_le hi hM hb y x
  exact hl.continuous

theorem exists_packetCumulative_orderIso {ψ : ℝ → ℝ}
    (hi : Integrable (fun x => ψ x ^ 2)) (hM : 0 < ∫ x, ψ x ^ 2)
    {R : ℝ} (hb : ∀ x, |ψ x| ≤ R)
    (hp : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hs : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) :
    ∃ Q : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
      ∀ x, (Q x : ℝ) = packetCumulative ψ x := by
  obtain ⟨h0, h1⟩ := packetCumulative_endpoints hM hs
  have hm := packetCumulative_monotone hi hM
  let f : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun x =>
    ⟨packetCumulative ψ x, by
      constructor
      · simpa only [h0] using hm x.property.1
      · simpa only [h1] using hm x.property.2⟩
  have hf : StrictMono f := fun x y hxy =>
    packetCumulative_strictMonoOn hi hM hp x.property y.property hxy
  have hsur : Function.Surjective f := by
    intro y
    have hy : (y : ℝ) ∈ Icc (packetCumulative ψ 0) (packetCumulative ψ 1) := by
      simpa only [h0, h1] using y.property
    obtain ⟨x, hx, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      (packetCumulative_continuous hi hM hb).continuousOn hy
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  exact ⟨hf.orderIsoOfSurjective f hsur, fun _ => rfl⟩

end CauchyHorizon
