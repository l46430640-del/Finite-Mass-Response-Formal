import CauchyHorizon.Characteristic.ZeroBandDecay

/-! Exponential decay of the actual zero-incoming bottom flux on a fixed radius band. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 2000000 in
theorem exists_zero_bottom_decay (B : Background) {s H dH : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    (hm : B.criticalExponent < 1) (hks : B.innerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R γ : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧ 0 < γ ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ K T : ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧ 0 ≤ K ∧ 0 < T ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
            ∀ (hfU : MemLp (fun _ : ℝ => (0 : ℝ)) p (volume.restrict (Icc 0 U))) (x : WaveState U V)
              (hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x),
              ∀ (v : Icc 0 V), (v : ℝ) ∈ Ioo 0 V → T ≤ (v : ℝ) →
                ∀ χ : ℝ → ℝ, ContinuousOn χ (Icc 0 (Z - Y)) →
                  (∀ w ∈ Icc 0 (Z - Y), χ w ∈ Ioo 0 U ∧
                    x.1 (projIcc 0 U hU (χ w)) v 0 = Z - w) →
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                  let q := fun w => Real.exp (B.innerRate * v) * χ w *
                    scalarTransportCorrection hV ν x.2.1 (projIcc 0 U hU (χ w)) v /
                      B.criticalWeight (x.1 (projIcc 0 U hU (χ w)) v 0)
                  let F := fun w => (-1 / x.2.1 (projIcc 0 U hU (χ w)) v 0) * q w ^ 2
                  ContinuousOn F (Icc 0 (Z - Y)) ∧
                    0 ≤ ∫ w in 0..(Z - Y), F w ∧
                      (∫ w in 0..(Z - Y), F w) ≤ K * Real.exp (-(2 * γ) * v) ∧
                        ∀ w ∈ Icc 0 (Z - Y), x.2.1 (projIcc 0 U hU (χ w)) v 0 < 0 := by
  intro hi hr0
  obtain ⟨δ, R, γ, hδ, hR, hγ, hband⟩ := B.exists_zero_band_decay
    hs hH hdH hdHR hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, γ, hδ, hR, hγ, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, C, d, T, hU₀, hUδ, _hC, hd, hT, hbound⟩ := hband Y Z hY hYZ hYR hZ
  have hwidth : 0 ≤ Z - Y := sub_nonneg.2 hYZ.le
  refine ⟨U₀, (Z - Y) * (C ^ 2 / d), T, hU₀, hUδ,
    mul_nonneg hwidth (div_nonneg (sq_nonneg C) hd.le), hT, ?_⟩
  intro p hp U V hU hV hUR hUU hfU x hx v hv hTv χ hχc hχ ν q F
  let u := fun w => projIcc 0 U hU (χ w)
  have hu (w : ℝ) (hw : w ∈ Icc 0 (Z - Y)) : ((u w : Icc 0 U) : ℝ) = χ w :=
    congrArg Subtype.val (projIcc_of_mem hU ⟨(hχ w hw).1.1.le, (hχ w hw).1.2.le⟩)
  have hrband (w : ℝ) (hw : w ∈ Icc 0 (Z - Y)) : x.1 (u w) v 0 ∈ Icc Y Z := by
    rw [(hχ w hw).2]
    constructor <;> linarith only [hw.1, hw.2]
  have hpoint (w : ℝ) (hw : w ∈ Icc 0 (Z - Y)) :
      x.2.1 (u w) v 0 ≤ -d ∧ 0 ≤ F w ∧ F w ≤ C ^ 2 / d * Real.exp (-(2 * γ) * v) := by
    have hh := hbound p hp U V hU hV hUR hUU hfU x hx (u w) v
      (by rw [hu w hw]; exact (hχ w hw).1) hv hTv (hrband w hw)
    refine ⟨hh.1, ?_⟩
    simpa only [F, q, hu w hw] using hh.2.2
  have huc : ContinuousOn u (Icc 0 (Z - Y)) := by dsimp only [u]; fun_prop
  have hρc : ContinuousOn (fun w => x.1 (u w) v 0) (Icc 0 (Z - Y)) :=
    ((continuous_apply (0 : Fin 3)).comp x.1.uncurry.continuous).comp_continuousOn
      (huc.prodMk continuousOn_const)
  have hLc : ContinuousOn (fun w => x.2.1 (u w) v 0) (Icc 0 (Z - Y)) :=
    ((continuous_apply (0 : Fin 3)).comp x.2.1.uncurry.continuous).comp_continuousOn
      (huc.prodMk continuousOn_const)
  have hL0 : ∀ w ∈ Icc 0 (Z - Y), x.2.1 (u w) v 0 ≠ 0 :=
    fun w hw => ((hpoint w hw).1.trans_lt (neg_neg_of_pos hd)).ne
  have hrinner (w : ℝ) (hw : w ∈ Icc 0 (Z - Y)) : x.1 (u w) v 0 ∈ Ioo B.inner B.event :=
    ⟨hY.trans_le (hrband w hw).1, (hrband w hw).2.trans_lt hZ⟩
  have hweight := B.criticalWeight_continuousOn.comp hρc hrinner
  have hweight0 : ∀ w ∈ Icc 0 (Z - Y), B.criticalWeight (x.1 (u w) v 0) ≠ 0 :=
    fun w hw => (B.criticalWeight_pos (hrinner w hw)).ne'
  have hζc : ContinuousOn (fun w => scalarTransportCorrection hV ν x.2.1 (u w) v) (Icc 0 (Z - Y)) :=
    (scalarTransportCorrection hV ν x.2.1).uncurry.continuous.comp_continuousOn (huc.prodMk continuousOn_const)
  have hqc : ContinuousOn q (Icc 0 (Z - Y)) :=
    ((continuousOn_const.mul hχc).mul hζc).div hweight hweight0
  have hFc : ContinuousOn F (Icc 0 (Z - Y)) :=
    (continuousOn_const.div hLc hL0).mul (hqc.pow 2)
  refine ⟨hFc, intervalIntegral.integral_nonneg hwidth (fun w hw => (hpoint w hw).2.1), ?_,
    fun w hw => (hpoint w hw).1.trans_lt (neg_neg_of_pos hd)⟩
  have hh := intervalIntegral.integral_mono_on (μ := volume) hwidth
    (hFc.intervalIntegrable_of_Icc hwidth) intervalIntegrable_const (fun w hw => (hpoint w hw).2.2)
  apply hh.trans_eq
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

end CauchyHorizon.Background
