import CauchyHorizon.Characteristic.OpticalIdentities

open MeasureTheory Set

namespace CauchyHorizon.Tests

-- The flux is positive exactly when lambda is negative; there is no global trapping assumption.
example {U V : ℝ} (x : WaveState U V) (u : Icc 0 U) (v : Icc 0 V) :
    0 < opticalField x u v ↔ x.2.1 u v 0 < 0 := by
  change 0 < -x.2.1 u v 0 / Real.exp (x.1 u v 2) ↔ _
  rw [div_pos_iff_of_pos_right (Real.exp_pos _), neg_pos]

-- On a nondegenerate time interval the flux identities give the actual one-sided derivatives.
example {U V e Λ : ℝ} (hV : 0 < V) {zIn : C(Icc 0 U, WaveVector)} {x : WaveState U V}
    (hx : HasOpticalFluxEquations hV.le e Λ zIn x) :
    ∃ hr : ∀ u v, x.1 u v 0 ≠ 0,
      let N := radialNuField hV.le e Λ zIn x.1 hr
      let m := massField e Λ x.1 x.2.1 N hr
      let O := opticalField x
      ∀ (u : Icc 0 U) (v : Icc 0 V),
        derivWithin (intervalExtension hV.le (O u)) (Icc 0 V) v =
          (x.1 u v 0 * x.2.1 u v 1) ^ 2 / (x.1 u v 0 * Real.exp (x.1 u v 2)) ∧
        derivWithin (intervalExtension hV.le (m u)) (Icc 0 V) v =
          -2 * x.1 u v 0 * N u v * derivWithin (intervalExtension hV.le (O u)) (Icc 0 V) v ∧
        derivWithin (fun t => intervalExtension hV.le (x.1 u) t 0 * intervalExtension hV.le (N u) t)
          (Icc 0 V) v = x.1 u v 0 * Real.exp (x.1 u v 2) * radialPotential (x.1 u v 0) e Λ ∧
        m u v = x.1 u v 0 / 2 *
          (1 + e ^ 2 / (x.1 u v 0) ^ 2 - Λ * (x.1 u v 0) ^ 2 / 3 - 4 * N u v * O u v) ∧
        (x.2.1 u v 0 < 0 → 0 < O u v ∧ 0 < (4 * O u v)⁻¹ ∧
          (4 * O u v)⁻¹ = N u v / horizonFunction (x.1 u v 0) (m u v) e Λ) := by
  obtain ⟨hr, hpoint⟩ := hx
  refine ⟨hr, fun u v => ?_⟩
  obtain ⟨hF, hO, hm, hR, hq⟩ := hpoint u v
  have hd := uniqueDiffOn_Icc hV v v.property
  refine ⟨hO.derivWithin hd, ?_, hR.derivWithin hd, mass_from_flux (hr u v) hF, hq⟩
  rw [hO.derivWithin hd]
  exact hm.derivWithin hd

end CauchyHorizon.Tests
