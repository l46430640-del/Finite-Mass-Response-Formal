import CauchyHorizon.Reduced.IntegralRegularity

/-! Horizontal integration bounds differences of the actual longitudinal velocity. -/

open Set MeasureTheory

namespace CauchyHorizon

theorem IsWaveIntegral.longitudinal_difference_bound {U V ε e Λ C : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (v : Icc 0 V) (i : Fin 3)
    (hb : ∀ᵐ s ∂volume.restrict (Icc 0 U), s ∈ Icc ε U →
      |waveSource e Λ (x.1 (projIcc 0 U hU s) v) (x.2.2 s v)
        (x.2.1 (projIcc 0 U hU s) v) i| ≤ C) (u : Icc ε U) :
    |x.2.1 ⟨u, hε.trans u.property.1, u.property.2⟩ v i - x.2.1 ⟨U, hU, le_rfl⟩ v i| ≤
      (U - ε) * C := by
  let F := rectangleSource hU e Λ x hx.choose
  let A : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousMap.evalCLM ℝ v)
  let Q := A.compLpL 2 (volume.restrict (Icc 0 U)) F
  have hi : IntervalIntegrable Q volume 0 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2 ((Lp.memLp Q).integrable (by norm_num))
  have he (w : Icc 0 U) : x.2.1 w v i = vOut v i + ∫ s in (0 : ℝ)..w, Q s := by
    have hh := congrArg (fun y : WaveState U V => A (y.2.1 w)) hx.choose_spec
    have hp := congrArg (fun q : C(Icc 0 U, ℝ) => q w) (horizontalPrimitive_compLp hU A F)
    change (∫ s in (0 : ℝ)..w, Q s) = A (horizontalPrimitive hU F w) at hp
    change A (vOut + horizontalPrimitive hU F w) = x.2.1 w v i at hh
    rw [map_add, ← hp] at hh
    exact hh.symm
  have hui : IntervalIntegrable Q volume 0 u := hi.mono_set (by
    rw [uIcc_of_le hU, uIcc_of_le (hε.trans u.property.1)]
    exact Icc_subset_Icc le_rfl u.property.2)
  have hiu : IntervalIntegrable Q volume u U := hi.mono_set (by
    rw [uIcc_of_le hU, uIcc_of_le u.property.2]
    exact Icc_subset_Icc (hε.trans u.property.1) le_rfl)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hui hiu
  have hqb : ∀ᵐ s ∂volume.restrict (Icc 0 U), s ∈ Icc ε U → |Q s| ≤ C := by
    filter_upwards [A.coeFn_compLpL F, rectangleSource_ae hU e Λ x hx.choose, hb] with s hs hsrc hb
    intro hm
    change Q s = A (F s) at hs
    rw [hs]
    change |F s v i| ≤ C
    rw [hsrc v]
    exact hb hm
  have hbInt := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := (u : ℝ)) (b := U)
    (f := Q) (C := C) (by
      filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hqb] with s hs
      intro hm
      rw [uIoc_of_le u.property.2] at hm
      exact hs ⟨(hε.trans u.property.1).trans hm.1.le, hm.2⟩
        ⟨u.property.1.trans hm.1.le, hm.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 u.property.2)] at hbInt
  have hd : x.2.1 ⟨U, hU, le_rfl⟩ v i - x.2.1 ⟨u, hε.trans u.property.1, u.property.2⟩ v i =
      ∫ s in (u : ℝ)..U, Q s := by rw [he, he]; linarith only [hsum]
  rw [abs_sub_comm, hd]
  exact hbInt.trans (by nlinarith only [mul_le_mul_of_nonneg_left u.property.1 hC])

end CauchyHorizon
