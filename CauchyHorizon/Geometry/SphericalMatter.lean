import CauchyHorizon.Geometry.SphericalChart
import CauchyHorizon.Geometry.ElectricField
import Mathlib.LinearAlgebra.Alternating.Basic

/-! The scalar covector and electric two-form on the actual product tangent spaces. -/

open scoped Manifold

namespace CauchyHorizon

noncomputable def sphereNullCovector (pV pu : ℝ) (p : UnitSphere) :
    ((ℝ × ℝ) × TangentSpace (𝓡 2) p) →ₗ[ℝ] ℝ where
  toFun a := pV * a.1.1 + pu * a.1.2
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' t a := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

noncomputable def sphereElectricForm (f : ℝ) (p : UnitSphere) :
    AlternatingMap ℝ ((ℝ × ℝ) × TangentSpace (𝓡 2) p) ℝ (Fin 2) where
  toFun a := f * ((a 0).1.2 * (a 1).1.1 - (a 0).1.1 * (a 1).1.2)
  map_update_add' a i b c := by fin_cases i <;> simp [Function.update] <;> ring
  map_update_smul' a i t b := by fin_cases i <;> simp [Function.update] <;> ring
  map_eq_zero_of_eq' a i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change a 0 = a 1 at h
      rw [h]; ring
    · change a 1 = a 0 at h
      rw [h]; ring
    · exact (hij rfl).elim

theorem sphereNullCovector_apply (pV pu : ℝ) (p : UnitSphere)
    (a : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphereNullCovector pV pu p a = pV * a.1.1 + pu * a.1.2 := rfl

theorem sphereElectricForm_apply (f : ℝ) (p : UnitSphere)
    (a b : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphereElectricForm f p ![a, b] = f * (a.1.2 * b.1.1 - a.1.1 * b.1.2) := rfl

theorem sphereElectricForm_chart_pullback (f : ℝ)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (y : ℝ × ℝ) (a b : Fin 4 → ℝ) :
    sphereElectricForm f (c.symm y)
      ![sphericalChartDifferential c y a, sphericalChartDifferential c y b] =
        ∑ i, ∑ j, electricTwoForm f i j * a i * b j := by
  norm_num [sphereElectricForm_apply, sphericalChartDifferential, electricTwoForm,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  ring

end CauchyHorizon
