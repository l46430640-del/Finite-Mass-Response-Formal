import CauchyHorizon.Characteristic.TransverseScalarBoundary
import CauchyHorizon.Reduced.ConformalDifference
import CauchyHorizon.Reduced.RegularConformal

/-! Actual compact traces control the horizontal conformal source without another decay bootstrap. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

set_option maxHeartbeats 1600000 in
theorem conformal_difference_of_traces {U ε e Λ k ρ A Ta : ℝ}
    (hU : 0 < U) (hε : 0 < ε) (hεU : ε ≤ U) (hρ : 0 < ρ) (hA : 0 ≤ A)
    (zIn : C(Icc 0 U, WaveVector)) (vOut : (T : Ici (0 : ℝ)) → C(Icc 0 (T : ℝ), WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U)))
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ T, IsWaveIntegral hU.le T.property e Λ zIn (vOut T) uIn (X T))
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU.le uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hr : ∀ (T : Ici (0 : ℝ)) u v, (X T).1 u v 0 ≠ 0)
    (hfloor : ∀ (T : Ici (0 : ℝ)) u v, ρ ≤ (X T).1 u v 0)
    (Z : C(Icc ε U, WaveVector)) (Nh Dh : C(Icc ε U, ℝ))
    (hZ : Tendsto (renormalizedWaveRow hε.le k X) atTop (𝓝 Z))
    (hN : Tendsto (scalarBoundaryRow hε.le (fun T => radialNuField T.property e Λ zIn (X T).1 (hr T)))
      atTop (𝓝 Nh))
    (hD : Tendsto (opticalRow hε.le X) atTop (𝓝 Dh)) (hR : ∀ u, Z u 0 ≠ 0)
    {χ : ℝ → ℝ} {Dφ : ℝ → C(Icc ε U, ℝ)} {Dhφ : C(Icc ε U, ℝ)}
    (hφ : IsTransverseScalarTrace hU.le X χ Dφ Dhφ)
    (hamp : ∀ t, Ta ≤ t → anchoringLapse hU.le X t ≤ A * Real.exp (-(2 * k) * t)) :
    ∃ T₀ B : ℝ, Ta ≤ T₀ ∧ 0 < B ∧ ∀ t (ht : 0 ≤ t), T₀ ≤ t →
      (∀ᵐ s ∂volume.restrict (Icc 0 U), s ∈ Icc ε U →
        |waveSource e Λ ((X ⟨t, ht⟩).1 (projIcc 0 U hU.le s) ⟨t, ht, le_rfl⟩)
          ((X ⟨t, ht⟩).2.2 s ⟨t, ht, le_rfl⟩)
          ((X ⟨t, ht⟩).2.1 (projIcc 0 U hU.le s) ⟨t, ht, le_rfl⟩) 2| ≤
            B * (Real.exp (-k * t) * ‖compactRadiationRow hε.le k X t‖ + Real.exp (-(2 * k) * t))) ∧
      ∀ u : Icc ε U, |(X ⟨t, ht⟩).2.1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht, le_rfl⟩ 2 -
        (X ⟨t, ht⟩).2.1 ⟨U, hU.le, le_rfl⟩ ⟨t, ht, le_rfl⟩ 2| ≤
          B * (Real.exp (-k * t) * ‖compactRadiationRow hε.le k X t‖ + Real.exp (-(2 * k) * t)) := by
  let Nt := scalarBoundaryRow hε.le (fun T => radialNuField T.property e Λ zIn (X T).1 (hr T))
  have hNc (S T : Ici (0 : ℝ)) (hST : S ≤ T) w v :
      radialNuField S.property e Λ zIn (X S).1 (hr S) w v =
        radialNuField T.property e Λ zIn (X T).1 (hr T) w ⟨v, v.property.1, v.property.2.trans hST⟩ := by
    apply radialNuField_prefix_eq S.property T.property hST e Λ _ _ _ (hr T) (hr S) ?_ w v
    intro u v
    have he := congrArg (fun x : WaveState U (S : ℝ) => x.1 u v) (hcompat S T hST)
    change (X T).1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X S).1 u v at he
    simpa only [zero_add] using he.symm
  let Zt := renormalizedWaveRow hε.le k X
  let It := fun t => Ring.inverse (waveRadius (Zt t))
  let Ih := Ring.inverse (waveRadius Z)
  let H := anchoredAmplitude (⟨U, hεU, le_rfl⟩ : Icc ε U)
  let G := fun t => H (Zt t) * ((1 / 2 : ℝ) • (It t) ^ 2 - (e ^ 2) • (It t) ^ 4 -
    (2 : ℝ) • (Nt t * opticalRow hε.le X t * (It t) ^ 2))
  let Gh := H Z * ((1 / 2 : ℝ) • Ih ^ 2 - (e ^ 2) • Ih ^ 4 - (2 : ℝ) • (Nh * Dh * Ih ^ 2))
  have hu := ((waveRadius Z).isUnit_iff_forall_ne_zero).2 hR
  have hi := (contDiffAt_ringInverse ℝ (n := 1) hu.unit).continuousAt
  rw [hu.unit_spec] at hi
  have hI : Tendsto It atTop (𝓝 Ih) := hi.tendsto.comp ((waveRadius.continuous.tendsto Z).comp hZ)
  have hG : Tendsto G atTop (𝓝 Gh) := ((H.continuous.tendsto Z).comp hZ).mul
    ((((hI.pow 2).const_smul (1 / 2 : ℝ)).sub ((hI.pow 4).const_smul (e ^ 2))).sub
      (((hN.mul hD).mul (hI.pow 2)).const_smul (2 : ℝ)))
  obtain ⟨Tg, hTg⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hG 1 (by norm_num))
  let K := ‖Gh‖ + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hGb (t : ℝ) (ht : Tg ≤ t) : ‖G t‖ ≤ K := by
    have hh := (hTg t ht).le
    rw [dist_eq_norm] at hh
    exact (norm_le_norm_sub_add (G t) Gh).trans (by dsimp only [K]; linarith only [hh])
  obtain ⟨Tφ, M, _hTφ, hM, hMb⟩ := hφ.2.2.2
  let C := 2 * M / ρ + A * K
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let T₀ := max Ta (max Tφ Tg)
  let B := (U - ε) * C + C + 1
  have hB : 0 < B := by dsimp only [B]; have := sub_nonneg.2 hεU; positivity
  have hCB : C ≤ B := by
    have hh := mul_nonneg (sub_nonneg.2 hεU) hC
    dsimp only [B]
    linarith only [hh]
  refine ⟨T₀, B, le_max_left _ _, hB, ?_⟩
  intro t ht ht₀
  have hta : Ta ≤ t := (le_max_left _ _).trans ht₀
  have htφ : Tφ ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht₀
  have htg : Tg ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht₀
  let T : Ici (0 : ℝ) := ⟨t, ht⟩
  let v : Icc 0 (T : ℝ) := ⟨t, ht, le_rfl⟩
  let J : Icc ε U → Icc 0 U := fun u => ⟨u, hε.le.trans u.property.1, u.property.2⟩
  let a := anchoringLapse hU.le X t
  have ha : a = Real.exp ((X T).1 ⟨U, hU.le, le_rfl⟩ v 2) := by
    unfold a anchoringLapse
    rw [max_eq_right ht, renormalizedWaveRow_apply hU.le X hcompat T ht le_rfl]
    simp only [ite_true, mul_zero, zero_mul, add_zero]
    rfl
  have hap : 0 < a := Real.exp_pos _
  have hgeom (w : Icc ε U) :
      |Real.exp ((X T).1 (J w) v 2) * conformalPotential ((X T).1 (J w) v 0) e +
        2 * radialNuField T.property e Λ zIn (X T).1 (hr T) (J w) v *
          (X T).2.1 (J w) v 0 / ((X T).1 (J w) v 0) ^ 2| ≤ A * K * Real.exp (-(2 * k) * t) := by
    have hr0 (w : Icc ε U) : waveRadius (Zt t) w ≠ 0 := by
      change renormalizedWaveRow hε.le k X t w 0 ≠ 0
      simpa only [renormalizedWaveRow_apply hε.le X hcompat T ht le_rfl,
        if_neg (by decide : (0 : Fin 3) ≠ 2), add_zero] using hr T (J w) v
    have hNv : Nt t w = radialNuField T.property e Λ zIn (X T).1 (hr T) (J w) v := by
      exact scalarBoundaryRow_apply hε.le _ hNc T ht le_rfl w
    have hZv (w : Icc ε U) (i : Fin 3) : Zt t w i =
        (X T).1 (J w) v i + (if i = 2 then 2 * k * t else 0) :=
      renormalizedWaveRow_apply hε.le X hcompat T ht le_rfl w i
    have hrv : waveRadius (Zt t) w = (X T).1 (J w) v 0 := by
      change Zt t w 0 = _
      simp only [hZv, if_neg (by decide : (0 : Fin 3) ≠ 2), add_zero]
    have he : a * G t w = Real.exp ((X T).1 (J w) v 2) * conformalPotential ((X T).1 (J w) v 0) e +
        2 * radialNuField T.property e Λ zIn (X T).1 (hr T) (J w) v *
          (X T).2.1 (J w) v 0 / ((X T).1 (J w) v 0) ^ 2 := by
      simp only [G, ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.pow_apply, smul_eq_mul, It, continuousMap_inverse_apply _ hr0, hNv, hrv]
      change a * ((Real.exp (-Zt t ⟨U, hεU, le_rfl⟩ 2) * Real.exp (Zt t w 2)) * _) = _
      rw [ha, opticalRow_apply hε.le X hcompat T ht le_rfl w]
      simp only [hZv, ite_true, Real.exp_neg, Real.exp_add, conformalPotential]
      field_simp [hr T (J w) v, Real.exp_ne_zero]
      ring
    rw [← he, abs_mul, abs_of_pos hap]
    have hb := ((G t).norm_coe_le_norm w).trans (hGb t htg)
    calc
      _ ≤ a * K := mul_le_mul_of_nonneg_left hb hap.le
      _ ≤ (A * Real.exp (-(2 * k) * t)) * K := mul_le_mul_of_nonneg_right (hamp t hta) hK.le
      _ = _ := by ring
  have hvScalar (w : Icc ε U) : |(X T).2.1 (J w) v 1| ≤
      Real.exp (-k * t) * ‖compactRadiationRow hε.le k X t‖ / ρ := by
    have hrad := hρ.trans_le (hfloor T (J w) v)
    have he : compactRadiationRow hε.le k X t w =
        Real.exp (k * t) * ((X T).1 (J w) v 0 * (X T).2.1 (J w) v 1) := by
      change radiationRow k X t (J w) = _
      rw [radiationRow_eq (t := t) X hcompat T le_rfl]
      simp only [spatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk, zero_mul, sub_zero,
        projIcc_of_mem T.property (show t ∈ Icc 0 (T : ℝ) from ⟨ht, le_rfl⟩)]
      rfl
    have hh := (compactRadiationRow hε.le k X t).norm_coe_le_norm w
    rw [he, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos hrad] at hh
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-(k * t))).le
    rw [Real.exp_neg] at hm
    have hc : (Real.exp (k * t))⁻¹ * (Real.exp (k * t) *
        ((X T).1 (J w) v 0 * |(X T).2.1 (J w) v 1|)) =
          (X T).1 (J w) v 0 * |(X T).2.1 (J w) v 1| := by field_simp
    rw [hc] at hm
    apply (le_div_iff₀ hρ).2
    calc
      _ ≤ (X T).1 (J w) v 0 * |(X T).2.1 (J w) v 1| := by
        nlinarith only [mul_le_mul_of_nonneg_right (hfloor T (J w) v) (abs_nonneg ((X T).2.1 (J w) v 1))]
      _ ≤ _ := by simpa only [neg_mul, Real.exp_neg] using hm
  let W := Real.exp (-k * t) * ‖compactRadiationRow hε.le k X t‖ + Real.exp (-(2 * k) * t)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hsource : ∀ᵐ s ∂volume.restrict (Icc 0 U), s ∈ Icc ε U →
      |waveSource e Λ ((X T).1 (projIcc 0 U hU.le s) v) ((X T).2.2 s v)
        ((X T).2.1 (projIcc 0 U hU.le s) v) 2| ≤ C * W := by
    filter_upwards [(hX T).horizontal_derivative hzin, (hX T).radialNu_ae (hr T) hinu,
      ae_restrict_mem measurableSet_Icc] with s hs hn hsU
    intro hsε
    let w : Icc ε U := ⟨s, hsε⟩
    let P : C(Icc 0 (T : ℝ), WaveVector) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (1 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
    have hd := P.hasFDerivAt.comp_hasDerivWithinAt s hs
    have hdu := hφ.1 T t ht le_rfl w
    have heq : (X T).2.2 s v 1 = Dφ t w :=
      (hd.derivWithin (uniqueDiffOn_Icc hU s hsU)).symm.trans
        (hdu.derivWithin (uniqueDiffOn_Icc hU s hsU))
    have hφb : |(X T).2.2 s v 1| ≤ M := by
      rw [heq]
      exact ((Dφ t).norm_coe_le_norm w).trans (hMb t htφ)
    simp only [waveSource, Matrix.cons_val, hn v, projIcc_of_mem hU.le hsU]
    change |-2 * (X T).2.2 s v 1 * (X T).2.1 (J w) v 1 +
      Real.exp ((X T).1 (J w) v 2) * conformalPotential ((X T).1 (J w) v 0) e +
      2 * radialNuField T.property e Λ zIn (X T).1 (hr T) (J w) v *
        (X T).2.1 (J w) v 0 / ((X T).1 (J w) v 0) ^ 2| ≤ C * W
    have hs := abs_add_le (-2 * (X T).2.2 s v 1 * (X T).2.1 (J w) v 1)
      (Real.exp ((X T).1 (J w) v 2) * conformalPotential ((X T).1 (J w) v 0) e +
        2 * radialNuField T.property e Λ zIn (X T).1 (hr T) (J w) v *
          (X T).2.1 (J w) v 0 / ((X T).1 (J w) v 0) ^ 2)
    rw [← add_assoc, abs_mul, abs_mul] at hs
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hs
    have hmul := mul_le_mul hφb (hvScalar w) (abs_nonneg _) hM.le
    have hm' : 2 * |(X T).2.2 s v 1| * |(X T).2.1 (J w) v 1| ≤
        (2 * M / ρ) * (Real.exp (-k * t) * ‖compactRadiationRow hε.le k X t‖) := by
      calc
        _ = 2 * (|(X T).2.2 s v 1| * |(X T).2.1 (J w) v 1|) := by ring
        _ ≤ 2 * (M * (Real.exp (-k * t) * ‖compactRadiationRow hε.le k X t‖ / ρ)) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = _ := by ring
    have hc1 : 0 ≤ 2 * M / ρ * Real.exp (-(2 * k) * t) := by positivity
    have hc2 : 0 ≤ A * K * (Real.exp (-k * t) * ‖compactRadiationRow hε.le k X t‖) := by positivity
    dsimp only [C, W]
    nlinarith only [hs, hm', hgeom w, hc1, hc2]
  constructor
  · filter_upwards [hsource] with s hs
    intro hm
    exact (hs hm).trans (mul_le_mul_of_nonneg_right hCB hW)
  · intro u
    have hb := (hX T).longitudinal_difference_bound hε.le (mul_nonneg hC hW) v 2 hsource u
    exact hb.trans (by
      have hh := mul_nonneg hC hW
      dsimp only [B]
      nlinarith only [hW, hh])

end CauchyHorizon
