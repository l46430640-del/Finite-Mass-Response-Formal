import CauchyHorizon.Geometry.NullMetric
import CauchyHorizon.Geometry.Christoffel
import CauchyHorizon.Geometry.DistributionRicci

/-! The null Ricci contractions cancel the unprescribed pure log-lapse second derivatives. -/

namespace CauchyHorizon

noncomputable def nullMetricChristoffel (H r s c qr pr qell pell : ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel (nullMetricInverse H (r ^ 2) (s ^ 2))
    ![nullMetricMatrix (H * qell) (2 * r * qr) (s ^ 2),
      nullMetricMatrix (H * pell) (2 * r * pr) (s ^ 2),
      Matrix.diagonal ![0, 0, 0, r ^ 2 * (2 * s * c)], 0]

set_option maxHeartbeats 1500000 in
theorem null_connection_contractions {H r s c qr pr qell pell : ℝ}
    (hH : H ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    let Γ := nullMetricChristoffel H r s c qr pr qell pell
    ∀ i : Fin 2,
      let j : Fin 4 := i.castAdd 2
      let a := ![qr / r, pr / r] i
      let b := ![qell, pell] i
      (∀ k, Γ k j j = if k = j then b else 0) ∧
      ricciTrace Γ j = b + 2 * a ∧
      ricciQuadratic Γ j j = 2 * b * a - 2 * a ^ 2 ∧ Γ 2 j 2 = a := by
  dsimp only
  intro i
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (try (intro k; fin_cases k)) <;>
    norm_num [nullMetricChristoffel, ricciTrace, ricciQuadratic, christoffel, Fin.sum_univ_succ,
      nullMetricInverse, nullMetricMatrix, Matrix.diagonal, Fin.castAdd, Fin.castLE,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, hH, hr, hs] <;>
      field_simp <;> ring

end CauchyHorizon
