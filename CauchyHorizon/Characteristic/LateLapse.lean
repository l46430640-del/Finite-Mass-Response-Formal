import CauchyHorizon.Reduced.IntegralRegularity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Direct lapse damping preserves an integrable part of the incoming power. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem IsWaveIntegral.late_lapse_bound {U V e Λ aRate D N d η q : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V} {zIn : C(Icc 0 U, WaveVector)}
    {vOut : C(Icc 0 V, WaveVector)} {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))}
    {x : WaveState U V} (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (u : Icc 0 U) (hu : 0 < (u : ℝ)) (a b : Icc 0 V) (hab : a ≤ b)
    (haRate : 0 < aRate) (hN : 0 ≤ N) (hη : 0 ≤ η) (hηq : η ≤ q)
    (hscale : (u : ℝ) * Real.exp (aRate * a) ≤ D)
    (hentry : Real.exp (x.1 u a 2) ≤ N * (u : ℝ) ^ (d - 1))
    (hell : ∀ t ∈ Icc a b, x.2.1 u t 2 ≤ -q) :
    Real.exp (x.1 u b 2) ≤
      N * D ^ (η / aRate) * (u : ℝ) ^ (d - 1 - η / aRate) * Real.exp (-η * b) := by
  let F := fun t => intervalExtension hV (x.1 u) t 2
  have hFc : Continuous F := by fun_prop
  have hd (t : ℝ) (ht : t ∈ Ioo (a : ℝ) b) :
      HasDerivAt F (x.2.1 u ⟨t, a.property.1.trans ht.1.le, ht.2.le.trans b.property.2⟩ 2) t := by
    have hh := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      t (hx.longitudinal_derivative u ⟨a.property.1.trans ht.1.le, ht.2.le.trans b.property.2⟩)
    exact hh.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2))
  have hdiff := (convex_Icc (a : ℝ) b).image_sub_le_mul_sub_of_deriv_le hFc.continuousOn
    (fun t ht => (hd t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      have htm : t ∈ Ioo (a : ℝ) b := by simpa only [interior_Icc] using ht
      rw [(hd t htm).deriv]
      exact hell _ ⟨htm.1.le, htm.2.le⟩)
    a (left_mem_Icc.2 hab) b (right_mem_Icc.2 hab) hab
  simp only [F, intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property] at hdiff
  have he : Real.exp (x.1 u b 2) ≤ Real.exp (x.1 u a 2) * Real.exp (-η * ((b : ℝ) - a)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith only [hdiff, mul_nonneg (sub_nonneg.2 hηq) (sub_nonneg.2 hab)]
  have hD : 0 < D := (mul_pos hu (Real.exp_pos _)).trans_le hscale
  have hplus : Real.exp (η * a) ≤ D ^ (η / aRate) * (u : ℝ) ^ (-(η / aRate)) := by
    have hs : Real.exp (aRate * a) ≤ D / u :=
      (le_div_iff₀ hu).2 (by simpa only [mul_comm] using hscale)
    have hh := Real.rpow_le_rpow (Real.exp_pos _).le hs (div_nonneg hη haRate.le)
    rw [← Real.exp_mul, Real.div_rpow hD.le hu.le] at hh
    have hid : aRate * (a : ℝ) * (η / aRate) = η * a := by field_simp
    rw [hid] at hh
    simpa only [Real.rpow_neg hu.le, div_eq_mul_inv] using hh
  have hsplit : Real.exp (-η * ((b : ℝ) - a)) = Real.exp (η * a) * Real.exp (-η * b) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (N * (u : ℝ) ^ (d - 1)) * Real.exp (-η * ((b : ℝ) - a)) :=
      he.trans (mul_le_mul_of_nonneg_right hentry (Real.exp_pos _).le)
    _ = (N * (u : ℝ) ^ (d - 1)) * (Real.exp (η * a) * Real.exp (-η * b)) := by rw [hsplit]
    _ ≤ (N * (u : ℝ) ^ (d - 1)) *
        ((D ^ (η / aRate) * (u : ℝ) ^ (-(η / aRate))) * Real.exp (-η * b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hplus (Real.exp_pos _).le) (by positivity)
    _ = _ := by rw [sub_eq_add_neg (d - 1), Real.rpow_add hu]; ring

end CauchyHorizon
