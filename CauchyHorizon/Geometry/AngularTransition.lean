import CauchyHorizon.Geometry.MetricTransition
import CauchyHorizon.Geometry.ConnectionChange

/-! Matrices of the actual angular Jacobian and its second derivative. -/

open scoped Matrix

namespace CauchyHorizon

noncomputable def angularJacobian (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => angularVectorChange L (Pi.single j 1) i

noncomputable def angularJacobianDerivative
    (Q : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun k j => angularVectorVariation
    (Q ((Pi.single i 1 : Fin 4 → ℝ) 2, (Pi.single i 1 : Fin 4 → ℝ) 3)) (Pi.single j 1) k

theorem angularJacobian_mulVec (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (a : Fin 4 → ℝ) :
    angularJacobian L *ᵥ a = angularVectorChange L a := by
  have he : L (a 2, a 3) = a 2 • L (1, 0) + a 3 • L (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have h0 : L (0, 0) = 0 := map_zero L
  ext i
  fin_cases i <;>
    simp [angularJacobian, angularVectorChange, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Pi.single_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, he, h0] <;> ring

theorem angularJacobian_mul_eq_one {L K : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (h : L.comp K = ContinuousLinearMap.id ℝ (ℝ × ℝ)) :
    angularJacobian L * angularJacobian K = 1 := by
  apply Matrix.ext_iff_mulVec.2
  intro a
  rw [← Matrix.mulVec_mulVec, angularJacobian_mulVec, angularJacobian_mulVec, Matrix.one_mulVec]
  have he := congrArg (fun T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => T (a 2, a 3)) h
  change L (K (a 2, a 3)) = (a 2, a 3) at he
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem angularJacobianDerivative_symmetric
    {Q : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hQ : ∀ a b, Q a b = Q b a) (i k j : Fin 4) :
    angularJacobianDerivative Q i k j = angularJacobianDerivative Q j k i := by
  have h := hQ ((Pi.single i 1 : Fin 4 → ℝ) 2, (Pi.single i 1 : Fin 4 → ℝ) 3)
    ((Pi.single j 1 : Fin 4 → ℝ) 2, (Pi.single j 1 : Fin 4 → ℝ) 3)
  fin_cases k
  · rfl
  · rfl
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem matrix_pullback_apply {ι : Type*} [Fintype ι]
    (g M N : Matrix ι ι ℝ) (i j : ι) :
    (Mᵀ * g * N) i j = ∑ a, ∑ b, g a b * M a i * N b j := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem metricChangeDerivative_apply {ι : Type*} [Fintype ι]
    (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (J : Matrix ι ι ℝ)
    (dJ : ι → Matrix ι ι ℝ) (i j k : ι) :
    metricChangeDerivative g dg J dJ i j k =
      (∑ a, J a i * ∑ b, ∑ c, dg a b c * J b j * J c k) +
      (∑ a, ∑ b, g a b * dJ i a j * J b k) +
      (∑ a, ∑ b, g a b * J a j * dJ i b k) := by
  simp only [metricChangeDerivative, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    matrix_pullback_apply]
  ac_rfl

end CauchyHorizon
