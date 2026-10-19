import CauchyHorizon.Reduced.ConstraintIntegral
import CauchyHorizon.Reduced.ScalarBoundary
import CauchyHorizon.Reduced.AmplitudeTrace

/-! The transverse constraint on positive compact intervals and at the horizon. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

def BoundaryTransverseConstraint {d U : ℝ} (hdU : d ≤ U)
    (Z : C(Icc d U, WaveVector)) (N S : C(Icc d U, ℝ)) : Prop :=
  ∀ u : Icc d U, N u * Real.exp (-Z u 2) =
    N ⟨d, le_rfl, hdU⟩ * Real.exp (-Z ⟨d, le_rfl, hdU⟩ 2) -
      ∫ t in d..(u : ℝ), S (projIcc d U hdU t) ^ 2 *
        Real.exp (-Z (projIcc d U hdU t) 2) / Z (projIcc d U hdU t) 0

def TransverseBoundaryGeometry {d U : ℝ} (hd : 0 ≤ d) (hdU : d ≤ U) (k : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (N : (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ))) : Prop :=
  ∃ Z : C(Icc d U, WaveVector), ∃ Nh Sh : C(Icc d U, ℝ),
    Tendsto (renormalizedWaveRow hd k X) atTop (𝓝 Z) ∧
    Tendsto (scalarBoundaryRow hd N) atTop (𝓝 Nh) ∧
    Tendsto (scalarBoundaryRow hd (fun T => scalarTransportCorrection T.property (N T) (X T).2.1))
      atTop (𝓝 Sh) ∧
    (∀ u, 0 < Z u 0 ∧ Nh u ≤ 0) ∧ BoundaryTransverseConstraint hdU Z Nh Sh

theorem IsWaveIntegral.zero_scalar_constraint_segment {U V e Λ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V} {zIn : C(Icc 0 U, WaveVector)}
    {vOut : C(Icc 0 V, WaveVector)} {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))}
    {x : WaveState U V} (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2)
    (hinzero : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 1 = 0)
    (v : Icc 0 V) (d u : Icc 0 U) (hdu : d ≤ u) :
    let N := radialNuField hV e Λ zIn x.1 hr
    let S := scalarTransportCorrection hV N x.2.1
    N u v * Real.exp (-x.1 u v 2) = N d v * Real.exp (-x.1 d v 2) -
      ∫ t in (d : ℝ)..(u : ℝ), S (projIcc 0 U hU t) v ^ 2 *
        Real.exp (-x.1 (projIcc 0 U hU t) v 2) / x.1 (projIcc 0 U hU t) v 0 := by
  intro N S
  let F := fun t : ℝ => intervalExtension hU x.1 t v 0 *
    Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2
  let G := fun t : ℝ => S (projIcc 0 U hU t) v ^ 2 *
    Real.exp (-x.1 (projIcc 0 U hU t) v 2) / x.1 (projIcc 0 U hU t) v 0
  obtain ⟨hi, he⟩ := hx.transverse_constraint_integral hr hzin hinu hinell v
  have hFG : F =ᵐ[volume.restrict (Icc 0 U)] G := by
    filter_upwards [hx.zeta_transport hr hinu, hinzero] with t ht hz
    have hs := ht v
    rw [hz, mul_zero, zero_add] at hs
    change x.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1 = S (projIcc 0 U hU t) v at hs
    dsimp only [F, G, intervalExtension_apply]
    rw [← hs]
    field_simp [hr (projIcc 0 U hU t) v]
  have hid : IntervalIntegrable F volume 0 d := hi.mono_set (by
    rw [uIcc_of_le d.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl d.property.2)
  have hdi : IntervalIntegrable F volume d u := hi.mono_set (by
    rw [uIcc_of_le (show (d : ℝ) ≤ u from hdu), uIcc_of_le hU]
    exact Icc_subset_Icc d.property.1 u.property.2)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hid hdi
  have hIg : (∫ t in (d : ℝ)..(u : ℝ), F t) = ∫ t in (d : ℝ)..(u : ℝ), G t := by
    simp only [intervalIntegral.integral_of_le (show (d : ℝ) ≤ u from hdu)]
    exact integral_congr_ae (ae_mono (Measure.restrict_mono
      (show Ioc (d : ℝ) u ⊆ Icc 0 U from fun _ ht =>
        ⟨d.property.1.trans ht.1.le, ht.2.trans u.property.2⟩) le_rfl) hFG)
  have hu := he u
  have hd := he d
  change N u v * Real.exp (-x.1 u v 2) = _ - ∫ t in (0 : ℝ)..(u : ℝ), F t at hu
  change N d v * Real.exp (-x.1 d v 2) = _ - ∫ t in (0 : ℝ)..(d : ℝ), F t at hd
  change _ = _ - ∫ t in (d : ℝ)..(u : ℝ), G t
  linarith only [hu, hd, hsplit, hIg]

theorem zero_scalar_boundary_constraint {U d k e Λ : ℝ}
    (hU : 0 ≤ U) (hd : 0 ≤ d) (hdU : d ≤ U)
    (zIn : C(Icc 0 U, WaveVector))
    (vOut : (T : Ici (0 : ℝ)) → C(Icc 0 (T : ℝ), WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ T, IsWaveIntegral hU T.property e Λ zIn (vOut T) uIn (X T))
    (hr : ∀ (T : Ici (0 : ℝ)) u v, (X T).1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2)
    (hinzero : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 1 = 0)
    (Z : C(Icc d U, WaveVector)) (Nh Sh : C(Icc d U, ℝ))
    (hZ : Tendsto (renormalizedWaveRow hd k X) atTop (𝓝 Z))
    (hN : Tendsto (scalarBoundaryRow hd (fun T => radialNuField T.property e Λ zIn (X T).1 (hr T)))
      atTop (𝓝 Nh))
    (hS : Tendsto (scalarBoundaryRow hd (fun T => scalarTransportCorrection T.property
      (radialNuField T.property e Λ zIn (X T).1 (hr T)) (X T).2.1)) atTop (𝓝 Sh))
    (hR : ∀ u, Z u 0 ≠ 0) : BoundaryTransverseConstraint hdU Z Nh Sh := by
  let N := fun T => radialNuField T.property e Λ zIn (X T).1 (hr T)
  let S := fun T => scalarTransportCorrection T.property (N T) (X T).2.1
  let Zt := renormalizedWaveRow hd k X
  let Nt := scalarBoundaryRow hd N
  let St := scalarBoundaryRow hd S
  let R : C(Icc d U, WaveVector) →L[ℝ] C(Icc d U, ℝ) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc d U) (ContinuousLinearMap.proj (0 : Fin 3))
  let A := fun t => waveAmplitude (-(Zt t))
  let Ah := waveAmplitude (-Z)
  let D := fun t => St t ^ 2 * A t * Ring.inverse (R (Zt t))
  let Dh := Sh ^ 2 * Ah * Ring.inverse (R Z)
  let B := fun t => Nt t * A t
  let Bh := Nh * Ah
  have hA : Tendsto A atTop (𝓝 Ah) := waveAmplitude.continuous.tendsto (-Z) |>.comp hZ.neg
  have hu := ((R Z).isUnit_iff_forall_ne_zero).2 hR
  have hi := (contDiffAt_ringInverse ℝ (n := 1) hu.unit).continuousAt
  rw [hu.unit_spec] at hi
  have hI := hi.tendsto.comp ((R.continuous.tendsto Z).comp hZ)
  have hD : Tendsto D atTop (𝓝 Dh) := ((hS.pow 2).mul hA).mul hI
  have hB : Tendsto B atTop (𝓝 Bh) := hN.mul hA
  let d0 : Icc d U := ⟨d, le_rfl, hdU⟩
  have hfinite (t : ℝ) (u : Icc d U) :
      B t u = B t d0 - continuousPrimitiveL hdU (D t) u := by
    let T : Ici (0 : ℝ) := ⟨max 0 t, le_max_left (0 : ℝ) t⟩
    let v : Icc 0 (T : ℝ) := ⟨T, T.property, le_rfl⟩
    let J : Icc d U → Icc 0 U := fun u => ⟨u, hd.trans u.property.1, u.property.2⟩
    let q := Real.exp (-(2 * k * t))
    have hz (u : Icc d U) (i : Fin 3) : Zt t u i = (X T).1 (J u) v i +
        (if i = 2 then 2 * k * t else 0) := rfl
    have hn (u : Icc d U) : Nt t u = N T (J u) v := rfl
    have hs (u : Icc d U) : St t u = S T (J u) v := rfl
    have hr0 (u : Icc d U) : R (Zt t) u ≠ 0 := by
      change Zt t u 0 ≠ 0
      simpa only [hz u 0, if_neg (by decide : (0 : Fin 3) ≠ 2), add_zero] using hr T (J u) v
    have ha (u : Icc d U) : A t u = q * Real.exp (-(X T).1 (J u) v 2) := by
      change Real.exp (-(Zt t u 2)) = _
      rw [hz u 2]
      simp only [ite_true, neg_add_rev, Real.exp_add, q]
    have hb (u : Icc d U) : B t u = q * (N T (J u) v * Real.exp (-(X T).1 (J u) v 2)) := by
      change Nt t u * A t u = _
      rw [hn, ha]
      ring
    have hdensity (u : Icc d U) : D t u = q *
        (S T (J u) v ^ 2 * Real.exp (-(X T).1 (J u) v 2) / (X T).1 (J u) v 0) := by
      simp only [D, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
        continuousMap_inverse_apply _ hr0, hs, ha]
      change _ * (Zt t u 0)⁻¹ = _
      rw [hz u 0]
      rw [if_neg (by decide : (0 : Fin 3) ≠ 2), add_zero]
      simp only [div_eq_mul_inv]
      ring
    have hp : continuousPrimitiveL hdU (D t) u = q *
        ∫ x in d..(u : ℝ), S T (projIcc 0 U hU x) v ^ 2 *
          Real.exp (-(X T).1 (projIcc 0 U hU x) v 2) / (X T).1 (projIcc 0 U hU x) v 0 := by
      change (∫ x in d..(u : ℝ), intervalExtension hdU (D t) x) = _
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le u.property.1] at hx
      have hxd : x ∈ Icc d U := ⟨hx.1, hx.2.trans u.property.2⟩
      have hxU : x ∈ Icc 0 U := ⟨hd.trans hx.1, hx.2.trans u.property.2⟩
      simp only [intervalExtension_apply, projIcc_of_mem hdU hxd, projIcc_of_mem hU hxU]
      exact hdensity ⟨x, hxd⟩
    rw [hb, hb, hp]
    exact congrArg (fun z : ℝ => q * z)
      ((hX T).zero_scalar_constraint_segment (hr T) hzin hinu hinell hinzero v (J d0) (J u)
        u.property.1) |>.trans (mul_sub _ _ _)
  intro u
  have hl := (continuous_eval_const u).tendsto Bh |>.comp hB
  have hrhs := ((continuous_eval_const d0).tendsto Bh |>.comp hB).sub
    (((continuous_eval_const u).tendsto (continuousPrimitiveL hdU Dh)).comp
      ((continuousPrimitiveL hdU).continuous.tendsto Dh |>.comp hD))
  have he := tendsto_nhds_unique hl (hrhs.congr' (Eventually.of_forall
    (fun t => (hfinite t u).symm)))
  change Nh u * Real.exp (-Z u 2) = Nh d0 * Real.exp (-Z d0 2) - _
  apply he.trans
  congr 1
  change (∫ t in d..(u : ℝ), intervalExtension hdU Dh t) = _
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [intervalExtension_apply, Dh, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
    continuousMap_inverse_apply (R Z) (fun u => hR u)]
  rfl

end CauchyHorizon
