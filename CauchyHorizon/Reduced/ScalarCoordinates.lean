import CauchyHorizon.Reduced.ScalarJoint
import CauchyHorizon.Reduced.ScalarResidual

/-! The actual rescaled scalar equations in the inward radius coordinate. -/

open Set MeasureTheory

namespace CauchyHorizon

set_option maxHeartbeats 1600000 in
theorem IsWaveIntegral.radial_mode_coordinate_transport
    (B : Background) (hb : B.criticalExponent < 1)
    {U V : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F)
    (hfs : ContDiffOn ℝ 1 (fun u => F u 1) (Ioi 0))
    {H : ℝ → ℝ} (hH : ContDiffOn ℝ 1 H (Ioo 0 V))
    {a b l S R : ℝ} {χ : ℝ × ℝ → ℝ}
    (hχc : ContinuousOn χ (Icc a b ×ˢ Icc l S)) :
    let D := Icc a b ×ˢ Icc l S
    let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
    let r := fun z : ℝ × ℝ => x.1 (projIcc 0 U hU z.1) (projIcc 0 V hV z.2) 0
    let n := fun z : ℝ × ℝ => ν (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2)
    let L := fun z : ℝ × ℝ => x.2.1 (projIcc 0 U hU (χ z)) (projIcc 0 V hV z.2) 0
    let J := fun z =>
      -(ContinuousLinearMap.toSpanSingleton ℝ (n z)⁻¹).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
        (ContinuousLinearMap.toSpanSingleton ℝ (L z / n z)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (∀ z ∈ D, χ z ∈ Ioo 0 U ∧ z.2 ∈ Ioo 0 V ∧ r (χ z, z.2) = R - z.1 ∧
      r (χ z, z.2) ∈ Ioo B.inner B.event ∧ n z ≠ 0 ∧ L z ≠ 0 ∧
        HasFDerivWithinAt χ (J z) D z) →
    let C := scalarTransportCorrection hV ν x.2.1
    let ζ := fun z : ℝ × ℝ => zIn (projIcc 0 U hU z.1) 0 * F z.1 1 +
      C (projIcc 0 U hU z.1) (projIcc 0 V hV z.2)
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).1 (B.event - y)
    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).2 (B.event - y)
    let P := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) *
      (r z * x.2.1 (projIcc 0 U hU z.1) (projIcc 0 V hV z.2) 1) - X (r z) * H z.2
    let Q := fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) * z.1 * ζ z /
      B.criticalWeight (r z) - W (r z) * H z.2
    let ρ := fun z : ℝ × ℝ => r (χ z, z.2)
    let p := fun z : ℝ × ℝ => P (χ z, z.2)
    let q := fun z : ℝ × ℝ => Q (χ z, z.2)
    let α := fun z => L z / (ρ z * χ z * n z)
    let β := fun z => χ z * n z / (ρ z * L z)
    let c := fun z => -1 / L z
    let d := fun z => B.innerRate * (c z - -1 / B.F (ρ z))
    let S₁ := fun z => (α z - B.outerRate / ρ z) * B.criticalWeight (ρ z) * W (ρ z) * H z.2
    let S₂ := fun z => ((β z - 1 / (B.outerRate * ρ z)) / B.criticalWeight (ρ z) * X (ρ z) +
      d z * W (ρ z)) * H z.2 - c z * W (ρ z) * deriv H z.2
    ContinuousOn p D ∧ ContinuousOn q D ∧
      ∃ qv : ℝ × ℝ → ℝ, ContinuousOn qv D ∧
        (∀ y ∈ Ioo a b, ∀ t ∈ Icc l S,
          HasDerivAt (fun w => p (w, t))
            (α (y, t) * B.criticalWeight (ρ (y, t)) * q (y, t) + S₁ (y, t)) y ∧
          HasDerivAt (fun w => q (w, t))
            (β (y, t) / B.criticalWeight (ρ (y, t)) * p (y, t) + d (y, t) * q (y, t) +
              S₂ (y, t) - c (y, t) * qv (y, t)) y) ∧
        ∀ y ∈ Icc a b, ∀ t ∈ Icc l S,
          HasDerivWithinAt (fun v => q (y, v)) (qv (y, t)) (Icc l S) t := by
  intro D ν r n L J hχ C ζ X W P Q ρ p q α β c d S₁ S₂
  let O := (Ioo (0 : ℝ) U ×ˢ Ioo (0 : ℝ) V) ∩ r ⁻¹' Ioo B.inner B.event
  have hrc : Continuous r := by fun_prop
  have hOo : IsOpen O := (isOpen_Ioo.prod isOpen_Ioo).inter (isOpen_Ioo.preimage hrc)
  have hreg := hx.scalar_joint_contDiff hzin hinu hF hif hfs
  have hrd : ContDiffOn ℝ 1 r O :=
    ((ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).contDiff.comp_contDiffOn
      hreg.1).mono inter_subset_left
  have hζd : ContDiffOn ℝ 1 ζ O := hreg.2.mono inter_subset_left
  have hXc : Continuous X := (continuous_extendCurve B.radialLength_pos.le _).comp (continuous_const.sub continuous_id)
  have hWc : Continuous W := (continuous_extendCurve B.radialLength_pos.le _).comp (continuous_const.sub continuous_id)
  have hqc := B.criticalWeight_continuousOn
  have hFc : ContinuousOn B.F (Ioo B.inner B.event) := by
    intro y hy
    have hn := (B.inner_pos.trans hy.1).ne'
    have hn2 := pow_ne_zero 2 hn
    apply ContinuousAt.continuousWithinAt
    change ContinuousAt (fun r => horizonFunction r B.mass B.charge B.cosmological) y
    unfold horizonFunction
    fun_prop (disch := assumption)
  have hc1 {g g' : ℝ → ℝ} (hg : ContinuousOn g' (Ioo B.inner B.event))
      (hd : ∀ y ∈ Ioo B.inner B.event, HasDerivAt g (g' y) y) :
      ContDiffOn ℝ 1 g (Ioo B.inner B.event) := by
    apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).2
    exact ⟨fun y hy => (hd y hy).differentiableAt.differentiableWithinAt,
      hg.congr (fun y hy => (hd y hy).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt hy))⟩
  have hweight : ContDiffOn ℝ 1 B.criticalWeight (Ioo B.inner B.event) := hc1
    ((continuousOn_const.div hFc (fun y hy => (B.F_neg hy).ne)).mul hqc)
    (fun _ hy => B.criticalWeight_hasDerivAt hy)
  have hmode : ContDiffOn ℝ 1 W (Ioo B.inner B.event) := hc1
    ((hXc.continuousOn.div ((continuousOn_const.mul continuousOn_id).mul hqc)
      (fun y hy => mul_ne_zero (mul_ne_zero B.outerRate_pos.ne'
        (B.inner_pos.trans hy.1).ne') (B.criticalWeight_pos hy).ne')).neg)
    (fun _ hy => (B.radialMode_radius_hasDerivAt hb hy).2)
  have hHO : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => H z.2) O :=
    hH.comp contDiffOn_snd (fun _ hz => hz.1.2)
  have hQ : ContDiffOn ℝ 1 Q O := by
    apply ContDiffOn.sub
    · apply ContDiffOn.div
      · exact (((contDiffOn_const.mul contDiffOn_snd).exp).mul contDiffOn_fst).mul hζd
      · exact hweight.comp hrd (fun _ hz => hz.2)
      · exact fun z hz => (B.criticalWeight_pos hz.2).ne'
    · exact (hmode.comp hrd (fun _ hz => hz.2)).mul hHO
  let G := fun z : ℝ × ℝ => (χ z, z.2)
  have hGc : ContinuousOn G D := hχc.prodMk continuousOn_snd
  have hmap : MapsTo G D O := fun z hz => ⟨⟨(hχ z hz).1, (hχ z hz).2.1⟩, (hχ z hz).2.2.2.1⟩
  have hPc : ContinuousOn P O := by
    have hθ : Continuous (fun z : ℝ × ℝ => Real.exp (B.innerRate * z.2) *
        (r z * x.2.1 (projIcc 0 U hU z.1) (projIcc 0 V hV z.2) 1)) := by fun_prop
    exact hθ.continuousOn.sub ((hXc.comp hrc).continuousOn.mul hHO.continuousOn)
  have hnc : ContinuousOn n D := by dsimp only [n]; fun_prop
  have hLc : ContinuousOn L D := by dsimp only [L]; fun_prop
  have hn0 : ∀ z ∈ D, n z ≠ 0 := fun z hz => (hχ z hz).2.2.2.2.1
  have hJc : ContinuousOn J D := by
    have hni := hnc.inv₀ hn0
    have hln := hLc.div hnc hn0
    change ContinuousOn (fun z =>
      -(ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ ((n z)⁻¹)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
        (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ (L z / n z)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) D
    fun_prop
  let qv := fun z => fderiv ℝ Q (G z) (J z (0, 1), 1)
  have hQdc : ContinuousOn (fun z => fderiv ℝ Q (G z)) D :=
    (hQ.continuousOn_fderiv_of_isOpen hOo le_rfl).comp hGc hmap
  have hqvc : ContinuousOn qv D := by dsimp only [qv]; fun_prop
  have hQder (z : ℝ × ℝ) (hz : z ∈ D) : HasFDerivAt Q (fderiv ℝ Q (G z)) (G z) :=
    ((hQ (G z) (hmap hz)).contDiffAt (hOo.mem_nhds (hmap hz))).differentiableAt (by norm_num) |>.hasFDerivAt
  have hGder (z : ℝ × ℝ) (hz : z ∈ D) :
      HasFDerivWithinAt G ((J z).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) D z :=
    (hχ z hz).2.2.2.2.2.2.prodMk (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.hasFDerivWithinAt
  have hqder (z : ℝ × ℝ) (hz : z ∈ D) := (hQder z hz).comp_hasFDerivWithinAt z (hGder z hz)
  have hscalar : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 1 = F u 1 := by
    filter_upwards [hif] with u hu
    exact congrFun hu 1
  have hres (z : ℝ × ℝ) (hz : z ∈ D) :
      HasDerivAt (fun u => P (u, z.2))
        (-n z * (α z * B.criticalWeight (ρ z) * q z + S₁ z)) (χ z) ∧
      HasDerivAt (fun t => Q (χ z, t))
        (-L z * (β z / B.criticalWeight (ρ z) * p z + d z * q z + S₂ z)) z.2 := by
    have hu := (hχ z hz).1
    have hv := (hχ z hz).2.1
    have hu' : χ z ∈ Icc 0 U := ⟨hu.1.le, hu.2.le⟩
    have hv' : z.2 ∈ Icc 0 V := ⟨hv.1.le, hv.2.le⟩
    have hHd := ((hH z.2 hv).contDiffAt (isOpen_Ioo.mem_nhds hv)).differentiableAt (by norm_num) |>.hasDerivAt
    have hh := hx.radial_mode_residual B hb hzin hinu hfs.continuousOn hscalar
      ⟨χ z, hu'⟩ ⟨z.2, hv'⟩ hu.1 (by simpa only [r, projIcc_of_mem hU hu', projIcc_of_mem hV hv'] using (hχ z hz).2.2.2.1)
      hHd.hasDerivWithinAt
    have hn : ν ⟨χ z, hu'⟩ ⟨z.2, hv'⟩ ≠ 0 := by simpa only [n, projIcc_of_mem hU hu', projIcc_of_mem hV hv'] using hn0 z hz
    have hl : x.2.1 ⟨χ z, hu'⟩ ⟨z.2, hv'⟩ 0 ≠ 0 := by
      simpa only [L, projIcc_of_mem hU hu', projIcc_of_mem hV hv'] using (hχ z hz).2.2.2.2.2.1
    have hhp := (hh hn hl).2.1.hasDerivAt (Icc_mem_nhds hu.1 hu.2)
    have hhq := (hh hn hl).2.2.hasDerivAt (Icc_mem_nhds hv.1 hv.2)
    simpa only [P, Q, p, q, ζ, r, ρ, α, β, c, d, S₁, S₂, n, L,
      projIcc_of_mem hU hu', projIcc_of_mem hV hv'] using! And.intro hhp hhq
  refine ⟨hPc.comp hGc hmap, hQ.continuousOn.comp hGc hmap, qv, hqvc, ?_, ?_⟩
  · intro y hy t ht
    have hz : (y, t) ∈ D := ⟨⟨hy.1.le, hy.2.le⟩, ht⟩
    have hslice : HasDerivWithinAt (fun w => (w, t)) (1, 0) (Icc a b) y :=
      (hasDerivWithinAt_id y (Icc a b)).prodMk (hasDerivWithinAt_const y (Icc a b) t)
    have hsliceMap : MapsTo (fun w => (w, t)) (Icc a b) D := fun _ hw => ⟨hw, ht⟩
    have hχx := ((hχ (y, t) hz).2.2.2.2.2.2.comp_hasDerivWithinAt y hslice hsliceMap).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    have hp := (hres (y, t) hz).1.comp y hχx
    have hqx := ((hqder (y, t) hz).comp_hasDerivWithinAt y hslice hsliceMap).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
    constructor
    · apply hp.congr_deriv
      change (-n (y, t) * _) * (-(1 * (n (y, t))⁻¹) - 0 * (L (y, t) / n (y, t))) = _
      field_simp [hn0 (y, t) hz]
      ring
    · have hvertical := (hQder (y, t) hz).comp_hasDerivAt t
        ((hasDerivAt_const t (χ (y, t))).prodMk (hasDerivAt_id t))
      have he := hvertical.unique (hres (y, t) hz).2
      change fderiv ℝ Q (G (y, t)) (0, 1) = -L (y, t) * _ at he
      apply hqx.congr_deriv
      change fderiv ℝ Q (G (y, t)) (J (y, t) (1, 0), 0) = _
      have hcanc : (J (y, t) (1, 0), (0 : ℝ)) + c (y, t) • (J (y, t) (0, 1), (1 : ℝ)) =
          c (y, t) • ((0, 1) : ℝ × ℝ) := by
        ext
        · change (-(1 * (n (y, t))⁻¹) - 0 * (L (y, t) / n (y, t))) +
            (-1 / L (y, t)) * (-(0 * (n (y, t))⁻¹) - 1 * (L (y, t) / n (y, t))) = (-1 / L (y, t)) * 0
          field_simp [hn0 (y, t) hz, (hχ (y, t) hz).2.2.2.2.2.1]
          ring
        · change 0 + c (y, t) * 1 = c (y, t) * 1
          ring
      have heq := congrArg (fderiv ℝ Q (G (y, t))) hcanc
      rw [map_add, map_smul, map_smul, he] at heq
      change _ + c (y, t) * qv (y, t) = c (y, t) * (-L (y, t) * _) at heq
      have hcL : c (y, t) * -L (y, t) = 1 := by
        dsimp only [c]
        field_simp [(hχ (y, t) hz).2.2.2.2.2.1]
      rw [← mul_assoc, hcL, one_mul] at heq
      linarith only [heq]
  · intro y hy t ht
    have hslice : HasDerivWithinAt (fun v => (y, v)) (0, 1) (Icc l S) t :=
      (hasDerivWithinAt_const t (Icc l S) y).prodMk (hasDerivWithinAt_id t (Icc l S))
    exact (hqder (y, t) ⟨hy, ht⟩).comp_hasDerivWithinAt t hslice (fun _ hv => ⟨hy, hv⟩)

end CauchyHorizon
