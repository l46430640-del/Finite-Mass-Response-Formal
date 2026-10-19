import CauchyHorizon.Reduced.RegularBoundary
import CauchyHorizon.Reduced.RegularRadius
import CauchyHorizon.Reduced.RegularConformal

/-! The actual normalized vector field has finite mixed energy up to regular time zero. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

theorem waveNormalize_norm_sq_le {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (u₀ : K) (Z : C(K, WaveVector)) :
    ‖waveNormalize u₀ Z‖ ^ 2 ≤
      3 * (‖waveRadius Z‖ ^ 2 + ‖waveScalar Z‖ ^ 2 + ‖waveAnchoredLog u₀ Z‖ ^ 2) := by
  have hn : ‖waveNormalize u₀ Z‖ ≤ ‖waveRadius Z‖ + ‖waveScalar Z‖ + ‖waveAnchoredLog u₀ Z‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro u
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [waveNormalize_apply]
    fin_cases i
    · change ‖Z u 0 - 0‖ ≤ _
      rw [sub_zero]
      exact ((waveRadius Z).norm_coe_le_norm u).trans
        ((le_add_of_nonneg_right (norm_nonneg _)).trans (le_add_of_nonneg_right (norm_nonneg _)))
    · change ‖Z u 1 - 0‖ ≤ _
      rw [sub_zero]
      exact ((waveScalar Z).norm_coe_le_norm u).trans
        ((le_add_of_nonneg_left (norm_nonneg _)).trans (le_add_of_nonneg_right (norm_nonneg _)))
    · change ‖Z u 2 - Z u₀ 2‖ ≤ _
      exact ((waveAnchoredLog u₀ Z).norm_coe_le_norm u).trans
        (le_add_of_nonneg_left (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith only [hs, sq_nonneg (‖waveRadius Z‖ - ‖waveScalar Z‖),
    sq_nonneg (‖waveRadius Z‖ - ‖waveAnchoredLog u₀ Z‖),
    sq_nonneg (‖waveScalar Z‖ - ‖waveAnchoredLog u₀ Z‖)]

def IsRegularWaveEnergy {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (k : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (T₀ C : ℝ) : Prop :=
  let a := anchoringLapse (hε.trans hεU) X
  let F := fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)
  (∀ w ∈ Ioo (regularTime a 0) 0,
    HasDerivAt (compactifiedWaveRow hε hεU X χ Z) (F w) w) ∧
  (∀ T, T₀ ≤ T → MemLp F 2 (volume.restrict (Ioo (regularTime a T) 0)) ∧
    (∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) ≤
      C * ∫ t in Ioi T, (‖compactRadiationRow hε k X t‖ ^ 2 + Real.exp (-(2 * k) * t))) ∧
  Tendsto (fun T => ∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) atTop (𝓝 0)

set_option maxHeartbeats 1000000 in
theorem regular_wave_energy {U ε k A Ta Ts Cs Tc Cc : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (hk : 0 < k) (hA : 0 < A) (hTa : 0 ≤ Ta) (hCs : 0 ≤ Cs) (hCc : 0 ≤ Cc)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) {χ : ℝ → ℝ}
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hvc : ContinuousOn (regularWaveVelocityRow hε hεU X χ)
      (Ioo (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0))
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)}
    {Dh : C(Icc ε U, WaveVector)} {O : C(Icc ε U, ℝ)}
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh)
    (hR : IsRegularRadiusBoundary hε hεU k X χ Z O)
    (hamp : ∀ t, Ta ≤ t → anchoringLapse (hε.trans hεU) X t ≤ A * Real.exp (-(2 * k) * t))
    (hS : IsRegularScalarEnergy hε hεU k X χ Ts Cs)
    (hC : IsRegularConformalEnergy hε hεU k X χ Tc Cc)
    (henergy : MemLp (radiationRow k X) 2 (volume.restrict (Ici 0))) :
    ∃ T₀ C : ℝ, 0 ≤ T₀ ∧ 0 < C ∧ IsRegularWaveEnergy hε hεU k X χ Z T₀ C := by
  let a := anchoringLapse (hε.trans hεU) X
  let N := waveNormalize (⟨U, hεU, le_rfl⟩ : Icc ε U)
  let F := fun w => N (regularWaveVelocityRow hε hεU X χ w)
  let R := compactifiedRadiusRow hε X χ (waveRadius Z)
  let Rv := -(anchoredAmplitude ⟨U, hεU, le_rfl⟩ Z) * O
  let Fr := fun w => waveRadius (regularWaveVelocityRow hε hεU X χ w)
  let Fs := regularScalarVelocityRow hε hεU X χ
  let Fc := regularConformalVelocityRow hε hεU X χ
  have hFc : ContinuousOn F (Ioo (regularTime a 0) 0) := N.continuous.comp_continuousOn hvc
  have hrc : ContinuousOn Fr (Ioo (regularTime a 0) 0) := waveRadius.continuous.comp_continuousOn hvc
  have hproj (w : ℝ) (hw : w ≠ 0) : R w = waveRadius (compactifiedWaveRow hε hεU X χ Z w) := by
    simp only [R, compactifiedRadiusRow, compactifiedWaveRow, Function.update_of_ne hw]
    ext u
    change renormalizedWaveRow hε 0 X (χ w) u 0 =
      waveNormalize ⟨U, hεU, le_rfl⟩ (renormalizedWaveRow hε 0 X (χ w)) u 0
    simp only [waveNormalize_apply, Pi.sub_apply, if_neg (by decide : (0 : Fin 3) ≠ 2), sub_zero]
  have hrd (w : ℝ) (hw : w ∈ Ioo (regularTime a 0) 0) : deriv R w = Fr w := by
    have hd := waveRadius.hasFDerivAt.comp_hasDerivAt w (hB.2.1 w hw)
    have he : R =ᶠ[𝓝 w] fun z => waveRadius (compactifiedWaveRow hε hεU X χ Z z) := by
      filter_upwards [eventually_lt_nhds hw.2] with z hz
      exact hproj z hz.ne
    rw [(hd.congr_of_eventuallyEq he).deriv]
    ext u
    change waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w) u 0 =
      regularWaveVelocityRow hε hεU X χ w u 0
    simp only [waveNormalize_apply, Pi.sub_apply, if_neg (by decide : (0 : Fin 3) ≠ 2), sub_zero]
  have hrlim : Tendsto Fr (𝓝[<] (0 : ℝ)) (𝓝 Rv) := by
    apply hR.2.2.2.2.1.congr'
    filter_upwards [Ioo_mem_nhdsLT (hχ.2.2.2.2.2.1 0)] with w hw
    exact hrd w hw
  have hrtop : Tendsto (fun t => Fr (regularTime a t)) atTop (𝓝 Rv) :=
    hrlim.comp hχ.2.2.2.2.2.2.1
  obtain ⟨Tr, hTr⟩ := eventually_atTop.1 (hrtop.norm.eventually (eventually_lt_nhds (lt_add_one ‖Rv‖)))
  let T₀ := max (max Ta Tr) (max Ts Tc)
  have haT : Ta ≤ T₀ := (le_max_left Ta Tr).trans (le_max_left _ _)
  have hrT : Tr ≤ T₀ := (le_max_right Ta Tr).trans (le_max_left _ _)
  have hsT : Ts ≤ T₀ := (le_max_left Ts Tc).trans (le_max_right _ _)
  have hcT : Tc ≤ T₀ := (le_max_right Ts Tc).trans (le_max_right _ _)
  have hT₀ : 0 ≤ T₀ := hTa.trans haT
  let Cr := A * (‖Rv‖ + 1) ^ 2
  have hCr : 0 < Cr := mul_pos hA (sq_pos_of_pos (by positivity))
  have hiExp : IntegrableOn (fun t => Real.exp (-(2 * k) * t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_mul_Ioi (by linarith only [hk]) 0)
  have hrEnergy := hχ.energy_of_majorant hT₀ hrc (hiExp.const_mul Cr) (by
    intro t ht _htpos
    have hb := (hTr t (hrT.trans ht)).le
    calc
      a t * ‖Fr (regularTime a t)‖ ^ 2 ≤ a t * (‖Rv‖ + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (hχ.2.1 t).le
      _ ≤ (A * Real.exp (-(2 * k) * t)) * (‖Rv‖ + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right (hamp t (haT.trans ht)) (sq_nonneg _)
      _ = Cr * Real.exp (-(2 * k) * t) := by dsimp only [Cr]; ring)
  have hiRad : IntegrableOn (fun t => ‖compactRadiationRow hε k X t‖ ^ 2) (Ici 0) := by
    have hi := (compactRadiationRestriction hε).comp_memLp' henergy
    exact (memLp_two_iff_integrable_sq_norm hi.1).1 hi
  let G := fun t => ‖compactRadiationRow hε k X t‖ ^ 2 + Real.exp (-(2 * k) * t)
  let C := 3 * (Cr + Cs + Cc)
  have hbound (w : ℝ) : ‖F w‖ ^ 2 ≤ 3 * (‖Fr w‖ ^ 2 + ‖Fs w‖ ^ 2 + ‖Fc w‖ ^ 2) :=
    waveNormalize_norm_sq_le _ _
  have htail (T : ℝ) (hT : T₀ ≤ T) :
      MemLp F 2 (volume.restrict (Ioo (regularTime a T) 0)) ∧
        (∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) ≤ C * ∫ t in Ioi T, G t := by
    obtain ⟨hrLp, hrBound⟩ := hrEnergy.1 T hT
    obtain ⟨hsLp, hsBound⟩ := hS.2.1 T (hsT.trans hT)
    obtain ⟨hcLp, hcBound⟩ := hC.2.1 T (hcT.trans hT)
    have hir : IntegrableOn (fun w => ‖Fr w‖ ^ 2) (Ioo (regularTime a T) 0) :=
      (memLp_two_iff_integrable_sq_norm hrLp.1).1 hrLp
    have his : IntegrableOn (fun w => ‖Fs w‖ ^ 2) (Ioo (regularTime a T) 0) :=
      (memLp_two_iff_integrable_sq_norm hsLp.1).1 hsLp
    have hic : IntegrableOn (fun w => ‖Fc w‖ ^ 2) (Ioo (regularTime a T) 0) :=
      (memLp_two_iff_integrable_sq_norm hcLp.1).1 hcLp
    have hiRS : IntegrableOn (fun w => ‖Fr w‖ ^ 2 + ‖Fs w‖ ^ 2) (Ioo (regularTime a T) 0) := hir.add his
    have hiSum : IntegrableOn (fun w => 3 * (‖Fr w‖ ^ 2 + ‖Fs w‖ ^ 2 + ‖Fc w‖ ^ 2))
        (Ioo (regularTime a T) 0) := (hiRS.add hic).const_mul (3 : ℝ)
    have hsub : Ioo (regularTime a T) 0 ⊆ Ioo (regularTime a 0) 0 :=
      fun w hw => ⟨(hχ.2.2.2.1.monotone (hT₀.trans hT)).trans_lt hw.1, hw.2⟩
    have hm := (hFc.mono hsub).aestronglyMeasurable (μ := volume) measurableSet_Ioo
    have hiF : IntegrableOn (fun w => ‖F w‖ ^ 2) (Ioo (regularTime a T) 0) := by
      apply hiSum.mono' (hm.norm.pow 2)
      exact Eventually.of_forall (fun w => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hbound w)
    refine ⟨(memLp_two_iff_integrable_sq_norm hm).2 hiF, ?_⟩
    have hsum : (∫ w in Ioo (regularTime a T) 0, ‖F w‖ ^ 2) ≤
        3 * ((∫ w in Ioo (regularTime a T) 0, ‖Fr w‖ ^ 2) +
          (∫ w in Ioo (regularTime a T) 0, ‖Fs w‖ ^ 2) +
          (∫ w in Ioo (regularTime a T) 0, ‖Fc w‖ ^ 2)) := by
      have hh := integral_mono_ae hiF hiSum (Eventually.of_forall hbound)
      rw [integral_const_mul, integral_add hiRS hic, integral_add hir his] at hh
      exact hh
    have hI : Ioi T ⊆ Ici (0 : ℝ) := fun t ht => (hT₀.trans hT).trans ht.le
    have hsplit : (∫ t in Ioi T, G t) = (∫ t in Ioi T, ‖compactRadiationRow hε k X t‖ ^ 2) +
        ∫ t in Ioi T, Real.exp (-(2 * k) * t) := integral_add (hiRad.mono_set hI) (hiExp.mono_set hI)
    have hRadLe : (∫ t in Ioi T, ‖compactRadiationRow hε k X t‖ ^ 2) ≤ ∫ t in Ioi T, G t := by
      rw [hsplit]
      exact le_add_of_nonneg_right (integral_nonneg (fun t => (Real.exp_pos _).le))
    have hExpLe : (∫ t in Ioi T, Real.exp (-(2 * k) * t)) ≤ ∫ t in Ioi T, G t := by
      rw [hsplit]
      exact le_add_of_nonneg_left (integral_nonneg (fun t => sq_nonneg _))
    rw [integral_const_mul] at hrBound
    calc
      _ ≤ _ := hsum
      _ ≤ 3 * (Cr * (∫ t in Ioi T, G t) + Cs * (∫ t in Ioi T, G t) + Cc * (∫ t in Ioi T, G t)) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add
          (hrBound.trans (mul_le_mul_of_nonneg_left hExpLe hCr.le))
          (hsBound.trans (mul_le_mul_of_nonneg_left hRadLe hCs))) hcBound) (by norm_num)
      _ = _ := by dsimp only [C]; ring
  refine ⟨T₀, C, hT₀, mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg hCr hCs) hCc), hB.2.1, htail, ?_⟩
  apply squeeze_zero' (Eventually.of_forall (fun T => integral_nonneg (fun w => sq_nonneg _)))
    ((eventually_ge_atTop T₀).mono (fun T hT => (htail T hT).2))
  simpa only [mul_zero, id_eq] using (tendsto_integral_Ioi_zero (f := G) (μ := volume) tendsto_id).const_mul C

end CauchyHorizon
