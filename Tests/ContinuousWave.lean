import CauchyHorizon.Characteristic.ContinuousWave

open MeasureTheory Set

namespace CauchyHorizon.Tests

-- The vector order is radius, scalar, log-lapse; these are exactly the three displayed sources.
example (r φ ell ν lam φu φv ellu ellv e Λ : ℝ) :
    waveSource e Λ ![r, φ, ell] ![ν, φu, ellu] ![lam, φv, ellv] =
      ![Real.exp ell * (-1 / (4 * r) + e ^ 2 / (4 * r ^ 3) + Λ * r / 4) - ν * lam / r,
        -(ν * φv + lam * φu) / r,
        -2 * φu * φv + Real.exp ell * (1 / (2 * r ^ 2) - e ^ 2 / r ^ 4) + 2 * ν * lam / r ^ 2] := by
  rfl

-- All actual one-sided derivatives, both mixed orders and both constraints use the same D.
example {U V e Λ : ℝ} (hU : 0 < U) (hV : 0 < V)
    {zIn : C(Icc 0 U, WaveVector)} {x : WaveState U V}
    (hx : HasContinuousWaveSystem hU.le hV.le e Λ zIn x) :
    ∃ hr : ∀ u v, x.1 u v 0 ≠ 0, ∃ D : ℝ → C(Icc 0 V, WaveVector),
      let N := radialNuField hV.le e Λ zIn x.1 hr
      ContinuousOn D (Ioi 0) ∧ x.2.2 =ᵐ[volume.restrict (Icc 0 U)] D ∧
        ∀ u ∈ Ioc 0 U, ∀ v : Icc 0 V,
          let z := intervalExtension hU.le x.1 u v
          let q := intervalExtension hU.le x.2.1 u v
          D u v 0 = intervalExtension hU.le N u v ∧
          (derivWithin (intervalExtension hU.le x.1) (Icc 0 U) u) v = D u v ∧
          derivWithin (intervalExtension hV.le (x.1 (projIcc 0 U hU.le u))) (Icc 0 V) v = q ∧
          derivWithin (intervalExtension hV.le (D u)) (Icc 0 V) v = waveSource e Λ z (D u v) q ∧
          derivWithin (fun t => intervalExtension hU.le x.2.1 t v) (Icc 0 U) u =
            waveSource e Λ z (D u v) q ∧
          derivWithin (fun t => intervalExtension hU.le N t v) (Icc 0 U) u -
            D u v 2 * intervalExtension hU.le N u v = -z 0 * D u v 1 ^ 2 ∧
          derivWithin (fun t => intervalExtension hV.le (x.2.1 (projIcc 0 U hU.le u)) t 0)
            (Icc 0 V) v - q 2 * q 0 = -z 0 * q 1 ^ 2 := by
  obtain ⟨hr, D, hc, hae, hlong, hpoint⟩ := hx
  refine ⟨hr, D, hc, hae, fun u hu v => ?_⟩
  obtain ⟨hz, hrest⟩ := hpoint u hu
  obtain ⟨hN, hduv, hdvu, hnu⟩ := hrest v
  have hu' := uniqueDiffOn_Icc hU u ⟨hu.1.le, hu.2⟩
  have hv' := uniqueDiffOn_Icc hV v v.property
  obtain ⟨hzdv, hLam⟩ := hlong (projIcc 0 U hU.le u) v
  refine ⟨hN, congrArg (fun f : C(Icc 0 V, WaveVector) => f v) (hz.derivWithin hu'),
    hzdv.derivWithin hv', hduv.derivWithin hv', hdvu.derivWithin hu', ?_, ?_⟩
  · rw [hnu.derivWithin hu']
    ring
  · rw [hLam.derivWithin hv']
    simp only [intervalExtension_apply]
    ring

end CauchyHorizon.Tests
