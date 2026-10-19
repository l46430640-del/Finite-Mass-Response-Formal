import CauchyHorizon.Characteristic.IncomingConvergence
import CauchyHorizon.Characteristic.UniformMassBound

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Tests

-- The null metric coefficient is exp(ell), while the angular coefficient is the unchanged r^2.
example {U R : ℝ} (hU : 0 ≤ U) (hU1 : U ≤ 1) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, MemLp (f n) p (volume.restrict (Icc 0 U))) (hzero : f 0 = 0)
    (hlim : Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 U))).toReal)
      atTop (𝓝 0)) (φ₀ : ℝ) :
    TendstoUniformly (fun n (u : Icc 0 U) => Real.exp (incomingLogOmega R (f n) u))
      (fun u => Real.exp (incomingLogOmega R (f 0) u)) atTop ∧
    ∀ n, waveRadius (incomingWaveCurve hU hUR hp (hf n) φ₀) ^ 2 =
      waveRadius (incomingWaveCurve hU hUR hp (hf 0) φ₀) ^ 2 := by
  have hi := incoming_data_convergence hU hU1 hUR hp f hf hzero hlim φ₀
  constructor
  · have hh := ContinuousMap.tendsto_iff_tendstoUniformly.1 hi.2.2.2.1
    change TendstoUniformly
      (fun n u => Real.exp (incomingWaveCurve hU hUR hp (hf n) φ₀ u 2))
      (fun u => Real.exp (incomingWaveCurve hU hUR hp (hf 0) φ₀ u 2)) atTop at hh
    simpa [incomingWaveCurve_apply] using hh
  · intro n
    ext u
    change (incomingWaveCurve hU hUR hp (hf n) φ₀ u 0) ^ 2 =
      (incomingWaveCurve hU hUR hp (hf 0) φ₀ u 0) ^ 2
    simp only [incomingWaveCurve_apply, Matrix.cons_val_zero]

-- The bound is chosen before the interval, sequence index, finite time and actual endpoint limits.
example {U e Λ : ℝ} {zIn : ℕ → C(Icc 0 U, WaveVector)}
    {X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V}
    (h : HasUniformMassBound e Λ zIn X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 ≤ ε),
      ∀ hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0,
        let ν := fun n (V : Ici (0 : ℝ)) => radialNuField V.property e Λ (zIn n) (X n V).1 (hr n V)
        (∀ n t, ‖massRow hε e Λ (X n) (ν n) (hr n) t‖ ≤ C) ∧
        ∀ Mh : ℕ → C(Icc ε U, ℝ),
          (∀ n, Tendsto (massRow hε e Λ (X n) (ν n) (hr n)) atTop (𝓝 (Mh n))) →
          ∀ n, ‖Mh n‖ ≤ C := h.rows_and_limits

end CauchyHorizon.Tests
