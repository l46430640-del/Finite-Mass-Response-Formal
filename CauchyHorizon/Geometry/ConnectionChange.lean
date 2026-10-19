import CauchyHorizon.Geometry.Christoffel
import Mathlib.Tactic.NoncommRing

/-! Connection changes use first metric derivatives and the second derivative of the chart. -/

open scoped Matrix
open MeasureTheory

namespace CauchyHorizon

-- J is the old-coordinate Jacobian, K its inverse, and dJ i the derivative in direction i.
noncomputable def connectionChange {ι : Type*} [Fintype ι]
    (Γ : ι → ι → ι → ℝ) (J K : Matrix ι ι ℝ) (dJ : ι → Matrix ι ι ℝ)
    (k i j : ι) : ℝ :=
  (K * ((∑ a, J a i • Matrix.of (fun l m => Γ l a m)) * J + dJ i)) k j

noncomputable def metricChangeDerivative {ι : Type*} [Fintype ι]
    (g : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (J : Matrix ι ι ℝ)
    (dJ : ι → Matrix ι ι ℝ) (i : ι) : Matrix ι ι ℝ :=
  (dJ i)ᵀ * g * J + Jᵀ * (∑ a, J a i • dg a) * J + Jᵀ * g * dJ i

theorem IsMetricConnection.change {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : Matrix ι ι ℝ} {dg : ι → Matrix ι ι ℝ} {Γ : ι → ι → ι → ℝ}
    (hΓ : IsMetricConnection g dg Γ)
    {J K : Matrix ι ι ℝ} (hJK : J * K = 1) {dJ : ι → Matrix ι ι ℝ}
    (hdJ : ∀ i k j, dJ i k j = dJ j k i) :
    IsMetricConnection (Jᵀ * g * J) (metricChangeDerivative g dg J dJ)
      (connectionChange Γ J K dJ) := by
  let C (i : ι) : Matrix ι ι ℝ := ∑ a, J a i • Matrix.of (fun l m => Γ l a m)
  let E (i : ι) : Matrix ι ι ℝ := C i * J + dJ i
  have hsym (i l j : ι) : E i l j = E j l i := by
    dsimp only [E]
    simp only [Matrix.add_apply, C, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, Finset.sum_mul]
    rw [hdJ i l j, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hΓ.1 l a b]
    ring
  have hd (i : ι) : dg i = (Matrix.of (fun l m => Γ l i m))ᵀ * g +
      g * Matrix.of (fun l m => Γ l i m) := by
    ext j k
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      mul_comm] using hΓ.2 i j k
  have hC (i : ι) : (∑ a, J a i • dg a) = (C i)ᵀ * g + g * C i := by
    simp only [C, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.sum_mul, Matrix.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [hd a, smul_add, Matrix.smul_mul, Matrix.mul_smul]
  have hcompat (i : ι) : metricChangeDerivative g dg J dJ i =
      (K * E i)ᵀ * (Jᵀ * g * J) + (Jᵀ * g * J) * (K * E i) := by
    have hT : Kᵀ * Jᵀ = 1 := by rw [← Matrix.transpose_mul, hJK, Matrix.transpose_one]
    simp only [Matrix.transpose_mul]
    calc
      metricChangeDerivative g dg J dJ i = (E i)ᵀ * g * J + Jᵀ * g * E i := by
        simp only [metricChangeDerivative, hC, E, Matrix.transpose_add, Matrix.transpose_mul]
        noncomm_ring
      _ = (E i)ᵀ * (Kᵀ * Jᵀ) * g * J + Jᵀ * g * (J * K) * E i := by
        simp only [hT, hJK, Matrix.mul_one]
      _ = _ := by noncomm_ring
  constructor
  · intro k i j
    change (K * E i) k j = (K * E j) k i
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => congrArg (K k l * ·) (hsym i l j)
  · intro i j k
    change metricChangeDerivative g dg J dJ i j k =
      (∑ l, (Jᵀ * g * J) l k * (K * E i) l j) + ∑ l, (Jᵀ * g * J) j l * (K * E i) l k
    have h := congrFun (congrFun (hcompat i) j) k
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_comm] using h

theorem IsMetricConnection.change_eq_christoffel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g gInv : Matrix ι ι ℝ} {dg : ι → Matrix ι ι ℝ} {Γ : ι → ι → ι → ℝ}
    (hΓ : IsMetricConnection g dg Γ) (hg : gᵀ = g) (hInv : gInv * g = 1)
    {J K : Matrix ι ι ℝ} (hJK : J * K = 1) (hKJ : K * J = 1)
    {dJ : ι → Matrix ι ι ℝ} (hdJ : ∀ i k j, dJ i k j = dJ j k i) :
    connectionChange Γ J K dJ =
      christoffel (K * gInv * Kᵀ) (metricChangeDerivative g dg J dJ) := by
  apply (hΓ.change hJK hdJ).eq_christoffel
  · have hs : (Jᵀ * g * J)ᵀ = Jᵀ * g * J := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hg, Matrix.mul_assoc]
    intro i j
    exact congrFun (congrFun hs j) i
  · have hT : Kᵀ * Jᵀ = 1 := by rw [← Matrix.transpose_mul, hJK, Matrix.transpose_one]
    calc
      K * gInv * Kᵀ * (Jᵀ * g * J) = K * gInv * (Kᵀ * Jᵀ) * g * J := by noncomm_ring
      _ = K * (gInv * g) * J := by simp only [hT, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hInv, Matrix.mul_one, hKJ]

theorem connectionChange_memLp {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} {Γ : α → ι → ι → ι → ℝ} {J K : α → Matrix ι ι ℝ}
    {dJ : α → ι → Matrix ι ι ℝ}
    (hΓ : ∀ k i j, MemLp (fun w => Γ w k i j) 2 μ)
    (hJ : ∀ i j, MemLp (fun w => J w i j) ⊤ μ)
    (hK : ∀ i j, MemLp (fun w => K w i j) ⊤ μ)
    (hdJ : ∀ i k j, MemLp (fun w => dJ w i k j) 2 μ) (k i j : ι) :
    MemLp (fun w => connectionChange (Γ w) (J w) (K w) (dJ w) k i j) 2 μ := by
  simpa only [connectionChange, Matrix.mul_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Pi.add_apply, mul_comm] using
    (memLp_finsetSum Finset.univ fun l _ =>
      ((memLp_finsetSum Finset.univ fun m _ =>
        (memLp_finsetSum Finset.univ fun a _ =>
          (hΓ l a m).mul' (r := 2) (hJ a i)).mul' (r := 2) (hJ m j)).add
            (hdJ i l j)).mul' (r := 2) (hK k l))

end CauchyHorizon
