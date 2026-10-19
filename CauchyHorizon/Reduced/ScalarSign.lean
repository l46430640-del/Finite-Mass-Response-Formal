import CauchyHorizon.Reduced.ScalarIntegral
import CauchyHorizon.Analysis.PrefixBootstrap

/-! Positive reference scalars from control of the positive-lambda correction. -/

open Set MeasureTheory

namespace CauchyHorizon

noncomputable def scalarPositiveLambdaCorrection {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (z w : WaveRectangle U V) (N : C(Icc 0 U, C(Icc 0 V, ℝ)))
    (u : Icc 0 U) (v : Icc 0 V) : ℝ :=
  ∫ t in (0 : ℝ)..(u : ℝ), max (w (projIcc 0 U hU t) v 0) 0 *
    |scalarTransportCorrection hV N w (projIcc 0 U hU t) v| / z (projIcc 0 U hU t) v 0

set_option maxHeartbeats 600000 in
theorem IsWaveIntegral.zero_scalar_positive {U V e Λ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V} {zIn : C(Icc 0 U, WaveVector)}
    {vOut : C(Icc 0 V, WaveVector)} {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))}
    {x : WaveState U V} (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    (hr : ∀ u v, 0 < x.1 u v 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinzero : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 1 = 0)
    (hN : ∀ u v, radialNuField hV e Λ zIn x.1 (fun u v => (hr u v).ne') u v < 0)
    (hbad : ∀ u v, scalarPositiveLambdaCorrection hU hV x.1 x.2.1
      (radialNuField hV e Λ zIn x.1 (fun u v => (hr u v).ne')) u v <
        x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1) :
    (∀ u v, 0 < x.1 u v 0 * x.2.1 u v 1) ∧
    ∀ u (v : Icc 0 V), 0 < (v : ℝ) → 0 < scalarTransportCorrection hV
      (radialNuField hV e Λ zIn x.1 (fun u v => (hr u v).ne')) x.2.1 u v := by
  let N := radialNuField hV e Λ zIn x.1 (fun u v => (hr u v).ne')
  let S := scalarTransportCorrection hV N x.2.1
  let θ : C(Icc 0 U, C(Icc 0 V, ℝ)) := waveCoordinateField 0 x.1 * waveCoordinateField 1 x.2.1
  have hregular : ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v,
      x.2.2 t v 1 = S (projIcc 0 U hU t) v / x.1 (projIcc 0 U hU t) v 0 := by
    filter_upwards [hx.zeta_transport (fun u v => (hr u v).ne') hinu, hinzero] with t ht hz
    intro v
    have hs := ht v
    rw [hz, mul_zero, zero_add] at hs
    exact (eq_div_iff (hr _ _).ne').2 (by simpa only [mul_comm] using hs)
  have hθ (u : Icc 0 U) (v : Icc 0 V) : θ u v = x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1 +
      ∫ t in (0 : ℝ)..(u : ℝ), -x.2.1 (projIcc 0 U hU t) v 0 *
        (S (projIcc 0 U hU t) v / x.1 (projIcc 0 U hU t) v 0) := by
    have he := hx.theta_integral hzin u v
    apply he.trans
    congr 1
    simp only [intervalIntegral.integral_of_le u.property.1]
    apply integral_congr_ae
    filter_upwards [ae_mono (Measure.restrict_mono
      (show Ioc (0 : ℝ) u ⊆ Icc 0 U from fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩)
      le_rfl) hregular] with t ht
    rw [ht v]
  let F := fun p : ℝ × Icc 0 V => -θ (projIcc 0 U hU p.1) p.2
  have hF : Continuous F := (θ.uncurry.continuous.comp
    (((continuous_projIcc (h := hU)).comp continuous_fst).prodMk continuous_snd)).neg
  have hstart (v : Icc 0 V) : F (0, v) < 0 := by
    have hb := hbad ⟨0, le_rfl, hU⟩ v
    simp only [scalarPositiveLambdaCorrection, intervalIntegral.integral_same] at hb
    have he := hθ ⟨0, le_rfl, hU⟩ v
    simp only [intervalIntegral.integral_same, add_zero] at he
    dsimp only [F]
    rw [projIcc_of_mem hU ⟨le_rfl, hU⟩, he]
    exact neg_neg_of_pos hb
  have hpos : ∀ u v, 0 < θ u v := by
    have hh := continuous_prefix_bootstrap (U := U) hF hstart (by
      intro t ht hpre v
      let u : Icc 0 U := ⟨t, ht⟩
      have hS (w : Icc 0 U) (hw : (w : ℝ) ≤ t) : 0 ≤ S w v := by
        change 0 ≤ ∫ s in (0 : ℝ)..(v : ℝ), intervalExtension hV (scalarTransportSource N x.2.1 w) s
        apply intervalIntegral.integral_nonneg v.property.1
        intro s hs
        have hsV : s ∈ Icc 0 V := ⟨hs.1, hs.2.trans v.property.2⟩
        have hp := hpre w ⟨w.property.1, hw⟩ ⟨s, hsV⟩
        simp only [F, projIcc_of_mem hU w.property, neg_nonpos] at hp
        have hvpos : 0 ≤ x.2.1 w ⟨s, hsV⟩ 1 := nonneg_of_mul_nonneg_right hp (hr w ⟨s, hsV⟩)
        simp only [intervalExtension_apply, projIcc_of_mem hV hsV]
        change 0 ≤ -N w ⟨s, hsV⟩ * x.2.1 w ⟨s, hsV⟩ 1
        exact mul_nonneg (neg_pos.2 (hN _ _)).le hvpos
      let G := fun s : ℝ => -x.2.1 (projIcc 0 U hU s) v 0 *
        (S (projIcc 0 U hU s) v / x.1 (projIcc 0 U hU s) v 0)
      let P := fun s : ℝ => max (x.2.1 (projIcc 0 U hU s) v 0) 0 *
        |S (projIcc 0 U hU s) v| / x.1 (projIcc 0 U hU s) v 0
      have hrc : Continuous (fun s => x.1 (projIcc 0 U hU s) v 0) :=
        ((continuous_apply 0).comp ((continuous_eval_const v).comp x.1.continuous)).comp continuous_projIcc
      have hsc : Continuous (fun s => S (projIcc 0 U hU s) v) :=
        ((continuous_eval_const v).comp S.continuous).comp continuous_projIcc
      have hlc : Continuous (fun s => x.2.1 (projIcc 0 U hU s) v 0) :=
        ((continuous_apply 0).comp ((continuous_eval_const v).comp x.2.1.continuous)).comp continuous_projIcc
      have hGc : Continuous G := hlc.neg.mul (hsc.div hrc (fun _ => (hr _ _).ne'))
      have hPc : Continuous P := ((hlc.max continuous_const).mul hsc.abs).div hrc (fun _ => (hr _ _).ne')
      have hb := intervalIntegral.integral_mono_on (μ := volume) ht.1
        (f := fun s => -P s) (g := G)
        (hPc.neg.intervalIntegrable (0 : ℝ) t) (hGc.intervalIntegrable (0 : ℝ) t) (by
          intro s hs
          have hsU : s ∈ Icc 0 U := ⟨hs.1, hs.2.trans ht.2⟩
          have hss := hS ⟨s, hsU⟩ hs.2
          dsimp only [G, P]
          rw [projIcc_of_mem hU hsU, abs_of_nonneg hss]
          have hm := mul_le_mul_of_nonneg_right (le_max_left (x.2.1 ⟨s, hsU⟩ v 0) 0)
            (div_nonneg hss (hr ⟨s, hsU⟩ v).le)
          simpa only [neg_mul, mul_div_assoc] using neg_le_neg hm)
      rw [intervalIntegral.integral_neg] at hb
      have hbad' := hbad u v
      have hid := hθ u v
      change (∫ s in (0 : ℝ)..t, P s) < _ at hbad'
      change θ u v = _ + ∫ s in (0 : ℝ)..t, G s at hid
      dsimp only [F]
      rw [projIcc_of_mem hU ht]
      linarith only [hb, hbad', hid])
    intro u v
    have hu := hh u u.property v
    simpa only [F, projIcc_of_mem hU u.property, neg_neg_iff_pos] using hu
  refine ⟨hpos, ?_⟩
  intro u v hv
  change 0 < ∫ s in (0 : ℝ)..(v : ℝ), intervalExtension hV (scalarTransportSource N x.2.1 u) s
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((intervalExtension hV (scalarTransportSource N x.2.1 u)).continuous.intervalIntegrable _ _) _ hv
  intro s hs
  have hsV : s ∈ Icc 0 V := ⟨hs.1.le, hs.2.le.trans v.property.2⟩
  simp only [intervalExtension_apply, projIcc_of_mem hV hsV]
  change 0 < -N u ⟨s, hsV⟩ * x.2.1 u ⟨s, hsV⟩ 1
  exact mul_pos (neg_pos.2 (hN _ _)) (pos_of_mul_pos_right (hpos u ⟨s, hsV⟩) (hr _ _).le)

end CauchyHorizon
