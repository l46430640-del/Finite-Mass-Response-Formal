import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Compatible incoming data with rough scalar derivative, at the actual L4 threshold. -/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace CauchyHorizon

noncomputable def incomingRadius (R u : ℝ) : ℝ := R - u

noncomputable def incomingPhi (φ₀ : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  φ₀ + ∫ x in 0..u, f x

noncomputable def incomingLogOmega (R : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.log 4 - ∫ x in 0..u, (R - x) * f x ^ 2

theorem incoming_corner (R φ₀ : ℝ) (f : ℝ → ℝ) :
    incomingRadius R 0 = R ∧ incomingPhi φ₀ f 0 = φ₀ ∧
      Real.exp (incomingLogOmega R f 0) = 4 := by
  simp [incomingRadius, incomingPhi, incomingLogOmega, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

theorem incoming_radius_positive {R U u : ℝ} (hUR : U < R) (hu : u ∈ Icc 0 U) :
    0 < incomingRadius R u := sub_pos.2 (hu.2.trans_lt hUR)

theorem incoming_memLp_sources {R U : ℝ} (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    MemLp f 4 (volume.restrict (Icc 0 U)) ∧
    MemLp (fun u => -(R - u) * f u ^ 2) 2 (volume.restrict (Icc 0 U)) := by
  have hf4 : MemLp f 4 (volume.restrict (Icc 0 U)) := hf.mono_exponent hp
  have hs : MemLp (fun u => f u ^ 2) 2 (volume.restrict (Icc 0 U)) := by
    let : ENNReal.HolderTriple 4 4 2 := ⟨by
      rw [show (4 : ℝ≥0∞) = (↑(4 : ℝ≥0)) by norm_cast,
        ← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_add, ← ENNReal.coe_inv_two]
      norm_num⟩
    simpa only [pow_two] using hf4.mul' hf4
  have hr : MemLp (fun u => -(R - u)) ∞ (volume.restrict (Icc 0 U)) := by
    apply memLp_top_of_bound (by fun_prop) R
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (sub_pos.2 (hu.2.trans_lt hUR))]
    linarith [hu.1]
  exact ⟨hf4, hs.mul' hr⟩

theorem incoming_integrable_sources {R U : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    IntervalIntegrable f volume 0 U ∧
      IntervalIntegrable (fun u => (R - u) * f u ^ 2) volume 0 U := by
  have hs := incoming_memLp_sources hUR hp hf
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    exact hs.1.integrable (by norm_num)
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    have hneg := (hs.2.integrable (by norm_num)).neg
    change Integrable (fun u => -(-(R - u) * f u ^ 2)) _ at hneg
    simpa only [IntegrableOn, neg_mul, neg_neg] using! hneg

theorem incoming_absolutelyContinuous {R U φ₀ : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 U)
    (hs : IntervalIntegrable (fun u => (R - u) * f u ^ 2) volume 0 U) :
    AbsolutelyContinuousOnInterval (incomingPhi φ₀ f) 0 U ∧
      AbsolutelyContinuousOnInterval (incomingLogOmega R f) 0 U := by
  have hc (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ => c) 0 U := by
    simp only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero]
    exact tendsto_const_nhds
  exact ⟨(hc φ₀).add (hf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc),
    (hc (Real.log 4)).sub (hs.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)⟩

theorem incoming_continuous {R U φ₀ : ℝ} (hU : 0 ≤ U) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 U)
    (hs : IntervalIntegrable (fun u => (R - u) * f u ^ 2) volume 0 U) :
    ContinuousOn (incomingPhi φ₀ f) (Icc 0 U) ∧
      ContinuousOn (incomingLogOmega R f) (Icc 0 U) := by
  rw [← uIcc_of_le hU]
  have h := incoming_absolutelyContinuous (φ₀ := φ₀) hf hs
  exact ⟨h.1.continuousOn, h.2.continuousOn⟩

theorem incoming_ae_hasDerivAt {R U φ₀ : ℝ} (hU : 0 ≤ U) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 U)
    (hs : IntervalIntegrable (fun u => (R - u) * f u ^ 2) volume 0 U) :
    ∀ᵐ u, u ∈ Icc 0 U →
      HasDerivAt (incomingPhi φ₀ f) (f u) u ∧
      HasDerivAt (incomingLogOmega R f) (-(R - u) * f u ^ 2) u := by
  filter_upwards [hf.ae_hasDerivAt_integral, hs.ae_hasDerivAt_integral] with u hφ hℓ hu
  have hu' : u ∈ uIcc 0 U := by simpa only [uIcc_of_le hU] using hu
  refine ⟨(hφ hu' 0 left_mem_uIcc).const_add φ₀, ?_⟩
  simpa only [incomingLogOmega, neg_mul] using! (hℓ hu' 0 left_mem_uIcc).const_sub (Real.log 4)

theorem incoming_constraint {R U φ₀ : ℝ} (hU : 0 ≤ U) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 U)
    (hs : IntervalIntegrable (fun u => (R - u) * f u ^ 2) volume 0 U) :
    ∀ᵐ u, u ∈ Icc 0 U →
      deriv (deriv (incomingRadius R)) u - deriv (incomingLogOmega R f) u *
        deriv (incomingRadius R) u = -incomingRadius R u * (deriv (incomingPhi φ₀ f) u) ^ 2 := by
  have hdr : ∀ u, HasDerivAt (incomingRadius R) (-1) u :=
    fun u => (hasDerivAt_id u).const_sub R
  have hr' : deriv (incomingRadius R) = fun _ => -1 := funext (fun u => (hdr u).deriv)
  filter_upwards [incoming_ae_hasDerivAt (φ₀ := φ₀) hU hf hs] with u hu hmem
  rw [hr', deriv_const, (hu hmem).1.deriv, (hu hmem).2.deriv]
  simp [incomingRadius]

theorem incoming_deriv_memLp {R U φ₀ : ℝ} (hU : 0 ≤ U) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) :
    MemLp (deriv (incomingPhi φ₀ f)) 4 (volume.restrict (Icc 0 U)) ∧
      MemLp (deriv (incomingLogOmega R f)) 2 (volume.restrict (Icc 0 U)) := by
  have hi := incoming_integrable_sources hU hUR hp hf
  have hd := (ae_restrict_iff' measurableSet_Icc).2
    (incoming_ae_hasDerivAt (φ₀ := φ₀) hU hi.1 hi.2)
  have heφ : deriv (incomingPhi φ₀ f) =ᵐ[volume.restrict (Icc 0 U)] f :=
    hd.mono (fun _ hu => hu.1.deriv)
  have heℓ : deriv (incomingLogOmega R f) =ᵐ[volume.restrict (Icc 0 U)]
      (fun u => -(R - u) * f u ^ 2) := hd.mono (fun _ hu => hu.2.deriv)
  have hm := incoming_memLp_sources hUR hp hf
  exact ⟨(memLp_congr_ae heφ).2 hm.1, (memLp_congr_ae heℓ).2 hm.2⟩

end CauchyHorizon
