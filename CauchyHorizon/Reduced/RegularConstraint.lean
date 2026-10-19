import CauchyHorizon.Reduced.ConstraintIntegral
import CauchyHorizon.Reduced.RegularBoundary

/-! The spatial Raychaudhuri constraint on continuous positive-radius sections. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.continuous_transverse_constraint {U V ε e Λ : ℝ}
    (hU : 0 < U) (hε : 0 ≤ ε) (hεU : ε ≤ U) {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU.le hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU.le uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU.le u) 0 * (uIn u 1) ^ 2)
    (v : Icc 0 V) (D : C(Icc ε U, WaveVector))
    (hD : ∀ u : Icc ε U, HasDerivWithinAt (fun t => intervalExtension hU.le x.1 t v)
      (D u) (Icc 0 U) u) (u : Icc ε U) :
    HasDerivWithinAt (fun t => intervalExtension hεU D t 0)
      (D u 2 * D u 0 - x.1 ⟨u, hε.trans u.property.1, u.property.2⟩ v 0 * (D u 1) ^ 2)
      (Icc ε U) u := by
  let J : Icc ε U → Icc 0 U := fun s => ⟨s, hε.trans s.property.1, s.property.2⟩
  let N := radialNuField hV e Λ zIn x.1 hx.choose
  let G := fun t => intervalExtension hU.le x.1 t v 0 *
    Real.exp (-intervalExtension hU.le x.1 t v 2) * (x.2.2 t v 1) ^ 2
  let R : C(Icc ε U, ℝ) := ⟨fun s => x.1 (J s) v 0 *
    Real.exp (-x.1 (J s) v 2) * (D s 1) ^ 2, by fun_prop⟩
  let q := fun s : Icc ε U => D s 0 * Real.exp (-x.1 (J s) v 2)
  have hn (s : Icc ε U) : N (J s) v = D s 0 := by
    have hd := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
      (s : ℝ) (hD s)
    exact ((hx.radial_hasDerivWithinAt hx.choose hzin hinu v (J s).property).derivWithin
      (uniqueDiffOn_Icc hU s (J s).property)).symm.trans
        (hd.derivWithin (uniqueDiffOn_Icc hU s (J s).property))
  have hae : G =ᵐ[volume.restrict (Icc ε U)] intervalExtension hεU R := by
    have hd := ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hε le_rfl)
      (hx.horizontal_derivative hzin)
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with t ht hm
    let s : Icc ε U := ⟨t, hm⟩
    have hdv := (ContinuousMap.evalCLM ℝ v : C(Icc 0 V, WaveVector) →L[ℝ] WaveVector).hasFDerivAt.comp_hasDerivWithinAt t ht
    have he := (hdv.derivWithin (uniqueDiffOn_Icc hU t (J s).property)).symm.trans
      ((hD s).derivWithin (uniqueDiffOn_Icc hU t (J s).property))
    change x.2.2 t v = D s at he
    simp only [G, intervalExtension_apply,
      projIcc_of_mem hU.le (show t ∈ Icc 0 U from ⟨hε.trans hm.1, hm.2⟩),
      projIcc_of_mem hεU hm, he]
    rfl
  obtain ⟨hi, he⟩ := hx.transverse_constraint_integral hx.choose hzin hinu hinell v
  have hprim (s : Icc ε U) : q s = q ⟨ε, le_rfl, hεU⟩ - continuousPrimitive hεU R s := by
    have hi₀ : IntervalIntegrable G volume 0 ε := hi.mono_set (by
      rw [uIcc_of_le hε, uIcc_of_le hU.le]
      exact Icc_subset_Icc le_rfl hεU)
    have his : IntervalIntegrable G volume ε s := hi.mono_set (by
      rw [uIcc_of_le s.property.1, uIcc_of_le hU.le]
      exact Icc_subset_Icc hε s.property.2)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hi₀ his
    have hIg : (∫ t in ε..(s : ℝ), G t) = continuousPrimitive hεU R s := by
      change (∫ t in ε..(s : ℝ), G t) = ∫ t in ε..(s : ℝ), intervalExtension hεU R t
      simp only [intervalIntegral.integral_of_le s.property.1]
      exact integral_congr_ae (ae_mono (Measure.restrict_mono
        (show Ioc ε s ⊆ Icc ε U from fun _ ht => ⟨ht.1.le, ht.2.trans s.property.2⟩) le_rfl) hae)
    have hs := he (J s)
    have hε₀ := he (J ⟨ε, le_rfl, hεU⟩)
    rw [hn] at hs hε₀
    change q s = _ - ∫ t in (0 : ℝ)..(s : ℝ), G t at hs
    change q ⟨ε, le_rfl, hεU⟩ = _ - ∫ t in (0 : ℝ)..ε, G t at hε₀
    linarith only [hs, hε₀, hsplit, hIg]
  have hq : HasDerivWithinAt (fun t => q (projIcc ε U hεU t)) (-R u) (Icc ε U) u := by
    apply ((continuousPrimitive_hasDerivWithinAt hεU R u.property).const_sub
      (q ⟨ε, le_rfl, hεU⟩)).congr_of_mem _ u.property
    intro t ht
    simp only [intervalExtension_apply, projIcc_of_mem hεU ht]
    exact hprim ⟨t, ht⟩
  have hl := ((ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
    (u : ℝ) (hD u)).mono (Icc_subset_Icc hε le_rfl)
  have hh := hq.mul (Real.hasDerivAt_exp _ |>.comp_hasDerivWithinAt (u : ℝ) hl)
  have hout := hh.congr_of_mem (f₁ := fun t => intervalExtension hεU D t 0) (fun t ht => ?_) u.property
  · apply hout.congr_deriv
    simp only [Function.comp_apply, ContinuousLinearMap.proj_apply, intervalExtension_apply,
      projIcc_of_mem hεU u.property,
      projIcc_of_mem hU.le (show (u : ℝ) ∈ Icc 0 U from ⟨hε.trans u.property.1, u.property.2⟩)]
    change -(x.1 (J u) v 0 * Real.exp (-x.1 (J u) v 2) * (D u 1) ^ 2) *
        Real.exp (x.1 (J u) v 2) + (D u 0 * Real.exp (-x.1 (J u) v 2)) *
        (Real.exp (x.1 (J u) v 2) * D u 2) = _
    rw [Real.exp_neg]
    field_simp
    ring
  · simp only [Pi.mul_apply, Function.comp_apply, ContinuousLinearMap.proj_apply,
      intervalExtension_apply, projIcc_of_mem hεU ht,
      projIcc_of_mem hU.le (show t ∈ Icc 0 U from ⟨hε.trans ht.1, ht.2⟩)]
    change D ⟨t, ht⟩ 0 = (D ⟨t, ht⟩ 0 * Real.exp (-x.1 (J ⟨t, ht⟩) v 2)) *
      Real.exp (x.1 (J ⟨t, ht⟩) v 2)
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

def IsRegularSpatialConstraint {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector))
    (Dh : C(Icc ε U, WaveVector)) : Prop :=
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let W := compactifiedTransverseRow χ D Dh
  ∀ w ∈ Ioo (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0, ∀ u : Icc ε U,
    HasDerivWithinAt (fun s => intervalExtension hεU (W w) s 0)
      (W w u 2 * W w u 0 - Ψ w u 0 * (W w u 1) ^ 2) (Icc ε U) u

theorem regular_spatial_constraint {U ε e Λ : ℝ}
    (hU : 0 < U) (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (zIn : C(Icc 0 U, WaveVector))
    (vOut : (T : Ici (0 : ℝ)) → C(Icc 0 (T : ℝ), WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ T, IsWaveIntegral hU.le T.property e Λ zIn (vOut T) uIn (X T))
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU.le uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU.le u) 0 * (uIn u 1) ^ 2)
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse hU.le X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hB : IsTransverseWaveBoundary hU.le hεU X χ Z D Dh)
    (hregular : IsRegularWaveBoundary hε hεU X χ Z D Dh) :
    IsRegularSpatialConstraint hε hεU X χ Z D Dh := by
  intro w hw u
  obtain ⟨ht, he, _hdχ⟩ := hχ.2.2.2.2.2.2.2.2.2.2.1 w hw
  let T : Ici (0 : ℝ) := ⟨χ w, ht.le⟩
  have hW : compactifiedTransverseRow χ D Dh w = D (χ w) := by
    exact Function.update_of_ne hw.2.ne _ _
  have hz := congrArg (fun z : WaveVector => z 0) (hregular.1 T (χ w) ht le_rfl u)
  rw [he] at hz
  simp only [Pi.sub_apply, if_neg (by decide : (0 : Fin 3) ≠ 2), sub_zero] at hz
  change compactifiedWaveRow hε hεU X χ Z w u 0 =
    (X T).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨χ w, ht.le, le_rfl⟩ 0 at hz
  change HasDerivWithinAt _ (_ - compactifiedWaveRow hε hεU X χ Z w u 0 * _) _ _
  rw [hW, hz]
  exact (hX T).continuous_transverse_constraint hU hε hεU hzin hinu hinell
    ⟨χ w, ht.le, le_rfl⟩ (D (χ w)) (hB.1 T (χ w) ht.le le_rfl) u

end CauchyHorizon
