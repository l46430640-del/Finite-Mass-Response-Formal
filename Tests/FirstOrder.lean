import CauchyHorizon.Characteristic.ContinuousFirstOrder

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon.Tests

-- The actual L4 development supplies the signs and mass flux without separate first-order hypotheses.
example (B : Background) {s l U V : ℝ} (D : AdmissibleOutgoingData B s l)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < D.radius 0)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_rfl hf (horizonPhi D.tail D.radius 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V D.tail_continuous
        (horizon_mass_integrable D.rate_pos D.upper_nonneg D.tail_continuous D.tail_bound)
        D.radius_continuous (fun v => ((sub_pos.2 D.deviation_lt).trans_le (D.radius_lower v)).ne'))
      (incomingWaveVelocity hUR le_rfl hf) x) :
    ∃ hr : ∀ u v, x.1 u v 0 ≠ 0,
      let N := radialNuField hV B.charge B.cosmological
        (incomingWaveCurve hU hUR le_rfl hf (horizonPhi D.tail D.radius 0)) x.1 hr
      let m := massField B.charge B.cosmological x.1 x.2.1 N hr
      let κ := fun u v => -Real.exp (x.1 u v 2) / (4 * N u v)
      ∀ u v, 0 < x.1 u v 0 ∧ N u v < 0 ∧ 0 < κ u v ∧
        x.2.1 u v 0 = κ u v * horizonFunction (x.1 u v 0) (m u v) B.charge B.cosmological ∧
        HasDerivWithinAt (intervalExtension hV (m u))
          ((x.1 u v 0 * x.2.1 u v 1) ^ 2 / (2 * κ u v)) (Icc 0 V) v := by
  obtain ⟨hr, hall, _hae, _hκ⟩ := hx.first_order_equations B D hU hV hUR le_rfl hf
  refine ⟨hr, fun u v => ?_⟩
  have hh := hall u v
  simp only [intervalExtension_apply, projIcc_of_mem hU u.property] at hh
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.2.2.1, hh.2.2.2.2.2.2.2.2⟩

-- One full-measure incoming set works for both scalar transports and the mass flux at every v.
example {U V e Λ : ℝ} (hU : 0 < U) (hV : 0 < V)
    {zIn : C(Icc 0 U, WaveVector)} {x : WaveState U V}
    (hx : HasFirstOrderEquations hU.le hV.le e Λ zIn x) :
    ∃ hr : ∀ u v, x.1 u v 0 ≠ 0,
      let N := radialNuField hV.le e Λ zIn x.1 hr
      let m := massField e Λ x.1 x.2.1 N hr
      let θ := fun u (v : Icc 0 V) => intervalExtension hU.le x.1 u v 0 *
        intervalExtension hU.le x.2.1 u v 1
      let ζ := fun u (v : Icc 0 V) => intervalExtension hU.le x.1 u v 0 * x.2.2 u v 1
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        derivWithin (fun t => θ t v) (Icc 0 U) u =
          -intervalExtension hU.le x.2.1 u v 0 * ζ u v / intervalExtension hU.le x.1 u v 0 ∧
        derivWithin (fun t => ζ u (projIcc 0 V hV.le t)) (Icc 0 V) v =
          -intervalExtension hU.le N u v * θ u v / intervalExtension hU.le x.1 u v 0 ∧
        derivWithin (fun t => intervalExtension hU.le m t v) (Icc 0 U) u =
          horizonFunction (intervalExtension hU.le x.1 u v 0) (intervalExtension hU.le m u v) e Λ *
            ζ u v ^ 2 / (2 * intervalExtension hU.le N u v) := by
  obtain ⟨hr, _hall, hae, _hκ⟩ := hx
  refine ⟨hr, ?_⟩
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with u hu humem
  intro v
  exact ⟨(hu.2 v).1.derivWithin (uniqueDiffOn_Icc hU u humem),
    (hu.2 v).2.1.derivWithin (uniqueDiffOn_Icc hV v v.property),
    (hu.2 v).2.2.derivWithin (uniqueDiffOn_Icc hU u humem)⟩

-- The lapse constraint includes absolute continuity, with its own a.e. derivative for each v.
example {U V e Λ : ℝ} (hU : 0 < U) (hV : 0 ≤ V)
    {zIn : C(Icc 0 U, WaveVector)} {x : WaveState U V}
    (hx : HasFirstOrderEquations hU.le hV e Λ zIn x) :
    ∃ hr : ∀ u v, x.1 u v 0 ≠ 0,
      let N := radialNuField hV e Λ zIn x.1 hr
      let κ := fun u (v : Icc 0 V) => -Real.exp (intervalExtension hU.le x.1 u v 2) /
        (4 * intervalExtension hU.le N u v)
      let ζ := fun u (v : Icc 0 V) => intervalExtension hU.le x.1 u v 0 * x.2.2 u v 1
      ∀ v : Icc 0 V, AbsolutelyContinuousOnInterval (fun u => κ u v) 0 U ∧
        ∀ᵐ u ∂volume.restrict (Icc 0 U), derivWithin (fun t => κ t v) (Icc 0 U) u =
          κ u v * ζ u v ^ 2 / (intervalExtension hU.le x.1 u v 0 * intervalExtension hU.le N u v) := by
  obtain ⟨hr, _hall, _hae, hκ⟩ := hx
  refine ⟨hr, fun v => ⟨(hκ v).1, ?_⟩⟩
  filter_upwards [(hκ v).2, ae_restrict_mem measurableSet_Icc] with u hu humem
  exact hu.derivWithin (uniqueDiffOn_Icc hU u humem)

-- A density continuous only on the positive half-line gives the one-sided derivative at U.
example {U : ℝ} (hU : 0 < U) {F G : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F 0 U) (hG : ContinuousOn G (Ioi 0))
    (hd : ∀ᵐ t ∂volume.restrict (Icc 0 U), HasDerivWithinAt F (G t) (Icc 0 U) t) :
    derivWithin F (Icc 0 U) U = G U :=
  (absolutelyContinuous_hasDerivWithinAt_of_continuous hU.le hF hG hd ⟨hU, le_rfl⟩).derivWithin
    (uniqueDiffOn_Icc hU U ⟨hU.le, le_rfl⟩)

-- The continuous representative is the actual scalar derivative and satisfies every pointwise flux.
example {U V e Λ : ℝ} (hU : 0 < U) (hV : 0 < V)
    {zIn : C(Icc 0 U, WaveVector)} {x : WaveState U V}
    (hx : HasContinuousFirstOrderEquations hU.le hV.le e Λ zIn x) :
    HasFirstOrderEquations hU.le hV.le e Λ zIn x ∧
    ∃ hr : ∀ u v, x.1 u v 0 ≠ 0,
      let N := radialNuField hV.le e Λ zIn x.1 hr
      let m := massField e Λ x.1 x.2.1 N hr
      let κ := fun u (v : Icc 0 V) => -Real.exp (intervalExtension hU.le x.1 u v 2) /
        (4 * intervalExtension hU.le N u v)
      let θ := fun u (v : Icc 0 V) => intervalExtension hU.le x.1 u v 0 *
        intervalExtension hU.le x.2.1 u v 1
      ∃ ζ : ℝ → C(Icc 0 V, ℝ), ContinuousOn ζ (Ioi 0) ∧
        ∀ u ∈ Ioc 0 U, ∀ v : Icc 0 V,
          ζ u v = intervalExtension hU.le x.1 u v 0 *
            derivWithin (fun t => intervalExtension hU.le x.1 t v 1) (Icc 0 U) u ∧
          derivWithin (fun t => θ t v) (Icc 0 U) u =
            -intervalExtension hU.le x.2.1 u v 0 * ζ u v / intervalExtension hU.le x.1 u v 0 ∧
          derivWithin (intervalExtension hV.le (ζ u)) (Icc 0 V) v =
            -intervalExtension hU.le N u v * θ u v / intervalExtension hU.le x.1 u v 0 ∧
          derivWithin (fun t => intervalExtension hU.le m t v) (Icc 0 U) u =
            horizonFunction (intervalExtension hU.le x.1 u v 0) (intervalExtension hU.le m u v) e Λ *
              ζ u v ^ 2 / (2 * intervalExtension hU.le N u v) ∧
          derivWithin (fun t => κ t v) (Icc 0 U) u =
            κ u v * ζ u v ^ 2 / (intervalExtension hU.le x.1 u v 0 * intervalExtension hU.le N u v) := by
  obtain ⟨hrough, hr, ζ, hζc, _hζae, hpoint⟩ := hx
  refine ⟨hrough, hr, ζ, hζc, fun u hu v => ?_⟩
  have hud := uniqueDiffOn_Icc hU u ⟨hu.1.le, hu.2⟩
  obtain ⟨hφ, hθ, hζ, hm, hκ⟩ := hpoint u hu v
  refine ⟨?_, hθ.derivWithin hud, hζ.derivWithin (uniqueDiffOn_Icc hV v v.property),
    hm.derivWithin hud, hκ.derivWithin hud⟩
  rw [hφ.derivWithin hud]
  simp only [intervalExtension_apply]
  field_simp [hr (projIcc 0 U hU.le u) v]

end CauchyHorizon.Tests
