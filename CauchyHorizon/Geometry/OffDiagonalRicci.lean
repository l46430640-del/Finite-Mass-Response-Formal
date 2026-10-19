import CauchyHorizon.Geometry.NullRicci

/-! The remaining Ricci contractions vanish without using field equations. -/

namespace CauchyHorizon

set_option maxHeartbeats 3000000 in
theorem null_angular_connection_contractions {H r s c qr pr qell pell : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) :
    let Γ := nullMetricChristoffel H r s c qr pr qell pell
    ∀ i j : Fin 2,
      let n := i.castAdd 2
      let a := j.natAdd 2
      (∀ k, Γ k n a = if k = a then ![qr / r, pr / r] i else 0) ∧
      (∀ k, Γ k a n = if k = a then ![qr / r, pr / r] i else 0) ∧
      ricciQuadratic Γ n a = 0 ∧ ricciQuadratic Γ a n = 0 := by
  dsimp only
  intro i j
  fin_cases i <;> fin_cases j <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (try (intro k; fin_cases k)) <;>
    dsimp only [Fin.natAdd, Fin.addNat] <;>
    norm_num [nullMetricChristoffel, ricciQuadratic, christoffel, Fin.sum_univ_succ,
      nullMetricInverse, nullMetricMatrix, Matrix.diagonal, Fin.castAdd, Fin.castLE,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, hr, hs] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num [Fin.val_succ, Fin.val_ofNat] <;> field_simp <;> ring

set_option maxHeartbeats 1500000 in
theorem angular_off_diagonal_contractions {H r s c qr pr qell pell : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) :
    let Γ := nullMetricChristoffel H r s c qr pr qell pell
    (∀ k, Γ k 2 3 = if k = 3 then c / s else 0) ∧
    (∀ k, Γ k 3 2 = if k = 3 then c / s else 0) ∧
    ricciQuadratic Γ 2 3 = 0 ∧ ricciQuadratic Γ 3 2 = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (try (intro k; fin_cases k)) <;>
    norm_num [nullMetricChristoffel, ricciQuadratic, christoffel, Fin.sum_univ_succ,
      nullMetricInverse, nullMetricMatrix, Matrix.diagonal,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, hr, hs] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num [Fin.val_succ, Fin.val_ofNat] <;> field_simp

end CauchyHorizon
