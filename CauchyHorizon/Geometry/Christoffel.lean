import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Coordinate Christoffel coefficients from a metric inverse and its weak derivatives. -/

open MeasureTheory
open scoped Matrix

namespace CauchyHorizon

noncomputable def christoffel {ι : Type*} [Fintype ι]
    (gInv : Matrix ι ι ℝ) (dg : ι → Matrix ι ι ℝ) (k i j : ι) : ℝ :=
  (∑ l, gInv k l * (dg i j l + dg j i l - dg l i j)) / 2

def IsMetricConnection {ι : Type*} [Fintype ι] (g : Matrix ι ι ℝ)
    (dg : ι → Matrix ι ι ℝ) (Γ : ι → ι → ι → ℝ) : Prop :=
  (∀ k i j, Γ k i j = Γ k j i) ∧
    ∀ i j k, dg i j k = (∑ l, g l k * Γ l i j) + ∑ l, g j l * Γ l i k

theorem christoffel_identities {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g gInv : Matrix ι ι ℝ} {dg : ι → Matrix ι ι ℝ}
    (hg : ∀ i j, g i j = g j i) (hInv : g * gInv = 1)
    (hdg : ∀ k i j, dg k i j = dg k j i) :
    IsMetricConnection g dg (christoffel gInv dg) := by
  have hlower (m i j : ι) :
      (∑ k, g m k * christoffel gInv dg k i j) = (dg i j m + dg j i m - dg m i j) / 2 := by
    simp only [christoffel, ← mul_div_assoc, ← Finset.sum_div]
    congr 1
    change (g *ᵥ (gInv *ᵥ (fun l => dg i j l + dg j i l - dg l i j))) m = _
    rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
  constructor
  · intro k i j
    apply congrArg (fun t : ℝ => t / 2)
    apply Finset.sum_congr rfl
    intro l _
    rw [hdg l i j]
    ring
  · intro i j k
    have hs : (∑ l, g l k * christoffel gInv dg l i j) =
        ∑ l, g k l * christoffel gInv dg l i j :=
      Finset.sum_congr rfl fun l _ => by rw [hg l k]
    rw [hs, hlower, hlower, hdg i k j]
    ring

theorem christoffel_memLp {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} {gInv : α → Matrix ι ι ℝ} {dg : α → ι → Matrix ι ι ℝ}
    (hInv : ∀ k l, MemLp (fun w => gInv w k l) ⊤ μ)
    (hdg : ∀ i j k, MemLp (fun w => dg w i j k) 2 μ) (k i j : ι) :
    MemLp (fun w => christoffel (gInv w) (dg w) k i j) 2 μ := by
  simpa only [christoffel, div_eq_mul_inv, Pi.add_apply, Pi.sub_apply] using
    (memLp_finsetSum Finset.univ fun l _ =>
      (((hdg i j l).add (hdg j i l)).sub (hdg l i j)).mul' (r := 2) (hInv k l)).mul_const (2 : ℝ)⁻¹

theorem IsMetricConnection.eq_christoffel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g gInv : Matrix ι ι ℝ} {dg : ι → Matrix ι ι ℝ} {Γ : ι → ι → ι → ℝ}
    (hΓ : IsMetricConnection g dg Γ) (hg : ∀ i j, g i j = g j i)
    (hInv : gInv * g = 1) : Γ = christoffel gInv dg := by
  have hlower (m i j : ι) :
      (∑ k, g m k * Γ k i j) = (dg i j m + dg j i m - dg m i j) / 2 := by
    have h₁ := hΓ.2 i j m
    have h₂ := hΓ.2 j i m
    have h₃ := hΓ.2 m i j
    simp_rw [hg _ m, hΓ.1 _ j i, hΓ.1 _ m i, hΓ.1 _ m j, hg _ j] at h₁ h₂ h₃
    linarith
  funext k i j
  have h := congrFun (congrArg (fun v => gInv *ᵥ v) (funext fun m => hlower m i j)) k
  change (gInv *ᵥ (g *ᵥ (fun l => Γ l i j))) k = _ at h
  rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec] at h
  simpa only [christoffel, Matrix.mulVec, dotProduct, mul_div_assoc, Finset.sum_div] using h

end CauchyHorizon
