import CauchyHorizon.Characteristic.ZeroBottom
import CauchyHorizon.Characteristic.BottomConvergence
import CauchyHorizon.Characteristic.BandCoordinates

/-! The sequence limit followed by the late-time limit removes the actual bottom inflow. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 3000000 in
theorem exists_bottom_flux_small (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hm : B.criticalExponent < 1) (hks : B.innerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → ∀ hYZ : Y < Z, Y ≤ R → Z < B.event →
        ∃ U₀ : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ,
          0 < U₀ ∧ U₀ ≤ δ ∧ (∀ ε U, 0 < τ ε U) ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℕ → ℝ → ℝ),
            (∀ n, MemLp (f n) p (volume.restrict (Icc 0 δ))) →
            (∀ n, (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal ≤ A) →
            Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u ∈ Icc η δ, f n u = 0) →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : ∀ n, MemLp (f n) p (volume.restrict (Icc 0 U)))
                (x : ℕ → WaveState U V) (y : WaveState U V)
                (hx : ∀ n, IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp (hfU n) (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp (hfU n)) (x n))
                (_hy : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp (f := 0) MemLp.zero (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp (f := 0) MemLp.zero) y),
                ∀ ρ : ℝ, 0 < ρ → (∀ n u v, ρ ≤ (x n).1 u v 0) → (∀ u v, ρ ≤ y.1 u v 0) →
                  ∀ (ε : Ioi (0 : ℝ)) (hUp : 0 < U) (v : Icc 0 V),
                    (v : ℝ) < V → τ ε ⟨U, hUp⟩ ≤ v →
                    ∀ χ : ℕ → C(Icc (0 : ℝ) (Z - Y), Icc (0 : ℝ) U),
                      (∀ n w, (x n).1 (χ n w) v 0 = Z - w) →
                      ∀ (W : C(Icc (0 : ℝ) (Z - Y), ℝ)) (a : ℕ → ℝ), Tendsto a atTop (𝓝 0) →
                        let ν := fun n => radialNuField hV B.charge B.cosmological
                          (incomingWaveCurve hU hUR hp (hfU n) (horizonPhi h r 0)) (x n).1 (hx n).choose
                        let ζ := fun n w => (r 0 - (χ n w : ℝ)) * f n (χ n w) +
                          scalarTransportCorrection hV (ν n) (x n).2.1 (χ n w) v
                        let q := fun n w => Real.exp (B.innerRate * v) * (χ n w : ℝ) * ζ n w /
                          B.criticalWeight (Z - w) - W w * a n
                        let F := fun n w => (-1 / (x n).2.1 (χ n w) v 0) * q n w ^ 2
                        ∀ᶠ n in atTop, |∫ w in (0 : ℝ)..(Z - Y),
                          F n (projIcc 0 (Z - Y) (sub_nonneg.2 hYZ.le) w)| < (ε : ℝ) := by
  classical
  intro hi hr0
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, Rc, hδ, _hδr, hRc, hcoords⟩ := B.exists_band_coordinates
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨_δz, Rz, γ, _hδz, hRz, hγ, hzero⟩ := B.exists_zero_bottom_decay
    hs hH hdH hdHR hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, min Rc Rz, hδ, ⟨lt_min hRc.1 hRz.1, (min_le_left _ _).trans_lt hRc.2⟩, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨Uc, _Tc, _τc, σ, hUc, hUcδ, _hTc, _hτc, _hσ, hchart⟩ :=
    hcoords Y Z hY hYZ (hYR.trans (min_le_left _ _)) hZ
  obtain ⟨Uz, K, Tz, hUz, _hUzδ, _hK, hTz, hbottom⟩ :=
    hzero Y Z hY hYZ (hYR.trans (min_le_right _ _)) hZ
  have hdecay : Tendsto (fun t : ℝ => K * Real.exp (-(2 * γ) * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith only [hγ] : -(2 * γ) < 0))).const_mul K
  have htail (ε : Ioi (0 : ℝ)) : ∃ T : ℝ, ∀ t ≥ T, K * Real.exp (-(2 * γ) * t) < ε :=
    eventually_atTop.1 (hdecay.eventually_lt_const ε.property)
  choose Ttail hTtail using htail
  let τ := fun ε U => max Tz (max (σ U) (Ttail ε))
  refine ⟨min Uc (min Uz 1), τ, lt_min hUc (lt_min hUz zero_lt_one),
    (min_le_left _ _).trans hUcδ, (fun _ _ => hTz.trans_le (le_max_left _ _)), ?_⟩
  intro p hp f hf hfn hlim hsupport U V hU hV hUR hUU hfU x y hx hy ρ hρ hxr hyr ε hUp v hv hτv χ hχ W a ha ν ζ q F
  have hUδ : U ≤ δ := (hUU.trans (min_le_left _ _)).trans hUcδ
  have hU1 : U ≤ 1 := (hUU.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hUzU : U ≤ Uz := (hUU.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hTzv : Tz ≤ (v : ℝ) := (le_max_left _ _).trans hτv
  have hσv : σ ⟨U, hUp⟩ ≤ (v : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hτv
  have htailv : Ttail ε ≤ (v : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hτv
  have hvint : (v : ℝ) ∈ Ioo 0 V := ⟨hTz.trans_le hTzv, hv⟩
  have hnorm (n : ℕ) := scalar_prefix_norm_le hUδ (hf n)
  have hnormlim : Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 U))).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) hnorm hlim
  have hsU : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u ∈ Icc η U, f n u = 0 :=
    fun η hη => (hsupport η hη).mono (fun n hn u hu => hn u ⟨hu.1, hu.2.trans hUδ⟩)
  obtain ⟨ψ, hψc, _hψdc, hψ⟩ := hchart p hp (fun _ => 0) MemLp.zero'
    (by simpa using hA)
    U V hU hV hUR (hUU.trans (min_le_left _ _)) MemLp.zero y hy hUp v v hσv le_rfl hv
  let J := Icc (0 : ℝ) (Z - Y)
  have hw : 0 ≤ Z - Y := sub_nonneg.2 hYZ.le
  have hrw (w : ℝ) (hw : w ∈ Icc 0 (Z - Y)) : Z - w ∈ Icc Y Z := by
    constructor <;> linarith only [hw.1, hw.2]
  have hψhit (w : ℝ) (hw : w ∈ Icc 0 (Z - Y)) : ψ (Z - w, v) ∈ Ioo 0 U ∧
      y.1 (projIcc 0 U hU (ψ (Z - w, v))) v 0 = Z - w := by
    have hh := hψ (Z - w, v) ⟨hrw w hw, ⟨le_rfl, le_rfl⟩⟩
    have hhit := hh.2.1
    simp only [projIcc_of_mem hV v.property] at hhit
    exact ⟨hh.1, hhit⟩
  have hψrow : ContinuousOn (fun w : ℝ => ψ (Z - w, v)) (Icc 0 (Z - Y)) :=
    hψc.comp ((continuous_const.sub continuous_id).prodMk continuous_const).continuousOn
      (fun w hw => ⟨hrw w hw, ⟨le_rfl, le_rfl⟩⟩)
  let χ₀ : C(J, Icc (0 : ℝ) U) := ⟨fun w => projIcc 0 U hU (ψ (Z - w, v)),
    continuous_projIcc.comp hψrow.domRestrict⟩
  have hχ₀val (w : J) : (χ₀ w : ℝ) = ψ (Z - w, v) :=
    congrArg Subtype.val (projIcc_of_mem hU ⟨(hψhit w w.property).1.1.le, (hψhit w w.property).1.2.le⟩)
  have hχ₀hit (w : J) : y.1 (χ₀ w) v 0 = Z - w := (hψhit w w.property).2
  have hχ₀pos (w : J) : 0 < (χ₀ w : ℝ) := by rw [hχ₀val]; exact (hψhit w w.property).1.1
  have hb0 := hbottom p hp U V hU hV hUR hUzU MemLp.zero y hy v hvint hTzv
    (fun w => ψ (Z - w, v)) hψrow hψhit
  have hL₀ (w : J) : y.2.1 (χ₀ w) v 0 ≠ 0 := (hb0.2.2.2 w w.property).ne
  let ν₀ := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp (f := 0) MemLp.zero (horizonPhi h r 0)) y.1 hy.choose
  let q₀ := fun w : J => Real.exp (B.innerRate * v) * (χ₀ w : ℝ) *
    scalarTransportCorrection hV ν₀ y.2.1 (χ₀ w) v / B.criticalWeight (Z - w)
  let F₀ := fun w : J => (-1 / y.2.1 (χ₀ w) v 0) * q₀ w ^ 2
  let I₀ := ∫ w in (0 : ℝ)..(Z - Y), F₀ (projIcc 0 (Z - Y) hw w)
  have hI₀ : 0 ≤ I₀ ∧ I₀ ≤ K * Real.exp (-(2 * γ) * v) := by
    have he : I₀ = ∫ w in (0 : ℝ)..(Z - Y),
        (-1 / y.2.1 (projIcc 0 U hU (ψ (Z - w, v))) v 0) *
          (Real.exp (B.innerRate * v) * ψ (Z - w, v) *
            scalarTransportCorrection hV ν₀ y.2.1 (projIcc 0 U hU (ψ (Z - w, v))) v /
              B.criticalWeight (y.1 (projIcc 0 U hU (ψ (Z - w, v))) v 0)) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro w hw'
      rw [uIcc_of_le hw] at hw'
      have hp : (projIcc 0 U hU (ψ (Z - w, v)) : ℝ) = ψ (Z - w, v) :=
        congrArg Subtype.val (projIcc_of_mem hU ⟨(hψhit w hw').1.1.le, (hψhit w hw').1.2.le⟩)
      simp only [F₀, q₀, projIcc_of_mem hw hw', χ₀, ContinuousMap.coe_mk, (hψhit w hw').2, hp]
    rw [he]
    exact ⟨hb0.2.1, hb0.2.2.1⟩
  have hIlim := (IsWaveIntegral.horizon_bottom_tendsto B hU hU1 hV hUR hc hi hrc hr0 hφ hrd
    hρ hA hp hfU (fun n => (hnorm n).trans (hfn n)) hnormlim hsU hx hy hxr hyr
    hY hYZ hZ v χ χ₀ hχ hχ₀hit hχ₀pos hL₀ W ha).2.2
  have hsmall : I₀ < (ε : ℝ) := hI₀.2.trans_lt (hTtail ε v htailv)
  have hlow : -(ε : ℝ) < I₀ := (neg_neg_of_pos ε.property).trans_le hI₀.1
  filter_upwards [hIlim.eventually_lt_const hsmall, hIlim.eventually_const_lt hlow] with n hn hn'
  exact abs_lt.2 ⟨hn', hn⟩

end CauchyHorizon.Background
