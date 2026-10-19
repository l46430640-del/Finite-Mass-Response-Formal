import CauchyHorizon.Geometry.NullRicci

/-! Mixed null contractions retain only the two radial velocities. -/

namespace CauchyHorizon

set_option maxHeartbeats 1500000 in
theorem mixed_connection_contractions {H r s c qr pr qell pell : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) :
    let Γ := nullMetricChristoffel H r s c qr pr qell pell
    ∀ i : Fin 2,
      (∀ k, Γ k (i.castAdd 2) (i.rev.castAdd 2) = 0) ∧
      ricciQuadratic Γ (i.castAdd 2) (i.rev.castAdd 2) = -2 * qr * pr / r ^ 2 := by
  dsimp only
  intro i
  fin_cases i <;> refine ⟨?_, ?_⟩ <;>
    (try (intro k; fin_cases k)) <;>
    norm_num [nullMetricChristoffel, ricciQuadratic, christoffel, Fin.sum_univ_succ,
      nullMetricInverse, nullMetricMatrix, Matrix.diagonal, Fin.castAdd, Fin.castLE, Fin.rev,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, hr, hs] <;>
      field_simp <;> ring

end CauchyHorizon
