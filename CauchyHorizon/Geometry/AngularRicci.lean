import CauchyHorizon.Geometry.NullRicci

/-! Angular Ricci contractions retain both the radial and intrinsic spherical terms. -/

namespace CauchyHorizon

set_option maxHeartbeats 2000000 in
theorem angular_connection_contractions {H r s c qr pr qell pell : ℝ}
    (hH : H ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    let Γ := nullMetricChristoffel H r s c qr pr qell pell
    let B := 2 * r * (pr * qell + qr * pell) / H
    (∀ k, Γ k 2 2 = ![2 * r * pr / H, 2 * r * qr / H, 0, 0] k) ∧
    (∀ k, Γ k 3 3 = ![2 * r * pr / H * s ^ 2, 2 * r * qr / H * s ^ 2, -s * c, 0] k) ∧
    ricciTrace Γ 2 = c / s ∧ ricciTrace Γ 3 = 0 ∧
    ricciQuadratic Γ 2 2 = B - (c / s) ^ 2 ∧
    ricciQuadratic Γ 3 3 = B * s ^ 2 + c ^ 2 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try (intro k; fin_cases k)) <;>
    norm_num [nullMetricChristoffel, ricciTrace, ricciQuadratic, christoffel, Fin.sum_univ_succ,
      nullMetricInverse, nullMetricMatrix, Matrix.diagonal, Fin.castAdd, Fin.castLE,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, hH, hr, hs] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num [Fin.val_succ, Fin.val_ofNat] <;> field_simp <;> ring

end CauchyHorizon
