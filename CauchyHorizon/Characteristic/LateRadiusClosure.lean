import CauchyHorizon.Characteristic.LateGeometry
import CauchyHorizon.Analysis.EnteredBootstrap
import CauchyHorizon.Characteristic.BandCrossing

/-! Close the late radius bootstrap from the actual data on a decreasing entry curve. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

set_option maxHeartbeats 600000 in
theorem IsWaveIntegral.late_radius_closed (B : Background) {U V R φ₀ Δ N d : ℝ}
    (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
      (incomingWaveCurve hU.le hUR hp hf φ₀) vOut (incomingWaveVelocity hUR hp hf) x)
    (hΔ : 0 < Δ) (hΔr : Δ ≤ B.inner / 4) (hN : 0 ≤ N) (hd : 0 < d)
    (hpot : ∀ r ∈ Icc (B.inner - Δ) (B.inner + Δ),
      B.innerRate / 4 ≤ radialPotential r B.charge B.cosmological)
    (hsmall : 2 * N * U ^ d / d < Δ / 2)
    {γ : ℝ → ℝ} (hγc : ContinuousOn γ (Ioc 0 U)) (hγa : StrictAntiOn γ (Ioc 0 U))
    (hγl : Tendsto γ (𝓝[>] (0 : ℝ)) atTop) (hγ0 : ∀ w ∈ Ioc 0 U, 0 ≤ γ w)
    (hnu : ∀ w t, radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU.le hUR hp hf φ₀) x.1 hx.choose w t < 0)
    (hdata : ∀ w : Icc 0 U, 0 < (w : ℝ) → γ w ≤ V →
      |x.1 w (projIcc 0 V hV (γ w)) 0 - B.inner| ≤ Δ / 2 ∧
      -radialNuField hV B.charge B.cosmological (incomingWaveCurve hU.le hUR hp hf φ₀)
        x.1 hx.choose w (projIcc 0 V hV (γ w)) ≤ N * (w : ℝ) ^ (-1 + d)) :
    ∀ w : Icc 0 U, 0 < (w : ℝ) → ∀ t : Icc 0 V, γ w ≤ t →
      B.inner - Δ < x.1 w t 0 ∧ x.1 w t 0 ≤ B.inner + Δ / 2 ∧
      -radialNuField hV B.charge B.cosmological (incomingWaveCurve hU.le hUR hp hf φ₀)
        x.1 hx.choose w t ≤ 2 * N * (w : ℝ) ^ (-1 + d) := by
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU.le hUR hp hf φ₀) x.1 hx.choose
  have hanti (t : Icc 0 V) := (hx.radial_strictAnti hx.choose rfl
    (incomingWave_constraint_data hU.le hUR hp hf φ₀).1 t (fun w => hnu w t)).antitone
  have hnear : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 U :=
    (show ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 < u from self_mem_nhdsWithin).and
      ((eventually_lt_nhds hU).filter_mono nhdsWithin_le_nhds)
  obtain ⟨z₀, hz₀, hzV⟩ := (hnear.and (hγl.eventually (eventually_gt_atTop V))).exists
  have hzle (w : Icc 0 U) (hw : 0 < (w : ℝ)) (t : Icc 0 V) (hwt : γ w ≤ t) : z₀ ≤ (w : ℝ) := by
    by_contra hn
    have hh := hγa ⟨hw, w.property.2⟩ ⟨hz₀.1, hz₀.2.le⟩ (not_le.1 hn)
    exact (hzV.trans hh).not_ge (hwt.trans t.property.2)
  have hleft (w : Icc 0 U) (hw : 0 < (w : ℝ)) (t : Icc 0 V) (hwt : γ w ≤ t) :
      ∃ z : Icc 0 U, z₀ ≤ (z : ℝ) ∧ z ≤ w ∧ γ z = t ∧
        |x.1 z t 0 - B.inner| ≤ Δ / 2 := by
    have hsub : Icc z₀ (w : ℝ) ⊆ Ioc 0 U :=
      fun _ ha => ⟨hz₀.1.trans_le ha.1, ha.2.trans w.property.2⟩
    obtain ⟨z, hz, hzt⟩ := intermediate_value_Icc' (hzle w hw t hwt)
      (hγc.mono hsub) (show (t : ℝ) ∈ Icc (γ w) (γ z₀) from ⟨hwt, t.property.2.trans hzV.le⟩)
    let a : Icc 0 U := ⟨z, (hsub hz).1.le, (hsub hz).2⟩
    have hb := (hdata a (hsub hz).1 (hzt.le.trans t.property.2)).1
    have hproj : projIcc 0 V hV (γ a) = t := by
      rw [show γ a = (t : ℝ) from hzt, projIcc_of_mem hV t.property]
    rw [hproj] at hb
    exact ⟨a, hz.1, hz.2, hzt, hb⟩
  have hupper (w : Icc 0 U) (hw : 0 < (w : ℝ)) (t : Icc 0 V) (hwt : γ w ≤ t) :
      x.1 w t 0 ≤ B.inner + Δ / 2 := by
    obtain ⟨z, _hz, hzw, _hzt, hrz⟩ := hleft w hw t hwt
    have hh := hanti t hzw
    have hb := (abs_le.1 hrz).2
    linarith only [hh, hb]
  have himprove (t : Icc 0 V)
      (hpre : ∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ s : Icc 0 V,
        s ≤ t → γ q ≤ s → B.inner - Δ ≤ x.1 q s 0)
      (w : Icc 0 U) (hw : 0 < (w : ℝ)) (hwt : γ w ≤ t) :
      B.inner - Δ < x.1 w t 0 ∧ -ν w t ≤ 2 * N * (w : ℝ) ^ (-1 + d) := by
    obtain ⟨z, hzz, hzw, hzt, hrz⟩ := hleft w hw t hwt
    have hz : 0 < (z : ℝ) := hz₀.1.trans_le hzz
    have hb := hx.late_radius_bound B hU.le hV hUR hp hf hΔ hΔr hN hd hpot z w t hz hzw hrz (by
      intro q hq
      have hq0 := hz.trans_le hq.1
      have hgt : γ q ≤ t :=
        (hγa.antitoneOn ⟨hz, z.property.2⟩ ⟨hq0, q.property.2⟩ hq.1).trans_eq hzt
      have hgm : γ q ∈ Icc 0 V := ⟨hγ0 q ⟨hq0, q.property.2⟩, hgt.trans t.property.2⟩
      have hbd := hdata q hq0 hgm.2
      refine ⟨⟨γ q, hgm⟩, hgt, ?_, ?_, ?_⟩
      · simpa only [projIcc_of_mem hV hgm] using hbd.1
      · simpa only [projIcc_of_mem hV hgm] using hbd.2
      · intro s hs
        exact ⟨hpre q hq0 s hs.2 hs.1,
          (hupper q hq0 s hs.1).trans (by linarith only [hΔ])⟩)
    have hsw : 2 * N * (w : ℝ) ^ d / d < Δ / 2 :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow w.property.1 w.property.2 hd.le)
          (by positivity : 0 ≤ 2 * N)) hd.le).trans_lt hsmall
    exact ⟨hb.2.2 hsw, hb.1 w (right_mem_Icc.2 hzw)⟩
  let embed : Icc z₀ U → Icc 0 U := fun w => ⟨w, hz₀.1.le.trans w.property.1, w.property.2⟩
  have hembed : Continuous embed := continuous_subtype_val.subtype_mk _
  let entry := fun w : Icc z₀ U => γ w
  have hec : Continuous entry := (hγc.mono (show Icc z₀ U ⊆ Ioc 0 U from
    fun _ hw => ⟨hz₀.1.trans_le hw.1, hw.2⟩)).domRestrict
  have he0 (w : Icc z₀ U) : 0 ≤ entry w := hγ0 w ⟨hz₀.1.trans_le w.property.1, w.property.2⟩
  let F := fun q : ℝ × Icc z₀ U => B.inner - Δ - x.1 (embed q.2) (projIcc 0 V hV q.1) 0
  have hRc : Continuous (fun q : Icc 0 U × Icc 0 V => x.1 q.1 q.2 0) :=
    (continuous_apply (0 : Fin 3)).comp x.1.uncurry.continuous
  have hGc : Continuous (fun q : Icc 0 U × Icc 0 V => B.inner - Δ - x.1 q.1 q.2 0) :=
    continuous_const.sub hRc
  have hFc : Continuous F := hGc.comp ((hembed.comp continuous_snd).prodMk
    ((show Continuous (projIcc 0 V hV) from continuous_projIcc).comp continuous_fst))
  have hclosed := continuous_entered_bootstrap hFc hec he0
    (fun w hw => by
      have hh := (hdata (embed w) (hz₀.1.trans_le w.property.1) hw).1
      have hb := (abs_le.1 hh).1
      change B.inner - Δ - x.1 (embed w) (projIcc 0 V hV (entry w)) 0 < 0
      linarith only [hb, hΔ])
    (fun t ht hpre w hwt => by
      have hh := (himprove ⟨t, ht⟩ (by
        intro q hq s hst hqs
        have hqz := hzle q hq s hqs
        have hh := hpre s ⟨s.property.1, hst⟩ ⟨q, hqz, q.property.2⟩ hqs
        simpa only [F, embed, projIcc_of_mem hV s.property, sub_nonpos] using hh)
        (embed w) (hz₀.1.trans_le w.property.1) hwt).1
      simpa only [F, projIcc_of_mem hV ht, sub_neg] using hh)
  have hlo (w : Icc 0 U) (hw : 0 < (w : ℝ)) (t : Icc 0 V) (hwt : γ w ≤ t) :
      B.inner - Δ < x.1 w t 0 := by
    have hh := hclosed t t.property ⟨w, hzle w hw t hwt, w.property.2⟩ hwt
    simpa only [F, embed, projIcc_of_mem hV t.property, sub_neg] using hh
  intro w hw t hwt
  exact ⟨hlo w hw t hwt, hupper w hw t hwt,
    (himprove t (fun q hq s _hstvo hqs => (hlo q hq s hqs).le) w hw hwt).2⟩

end CauchyHorizon
