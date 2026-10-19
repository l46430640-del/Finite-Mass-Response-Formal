import CauchyHorizon.Characteristic.FiniteUniqueness
import CauchyHorizon.Reduced.RadialLevel

/-! First radius contact on an actual physical rectangle. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.exists_first_radius_contact {M e Λ U V Y : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hinit : Y < r 0 - U) (hbad : ∃ u v, x.1 u v 0 ≤ Y) :
    ∃ t : Icc 0 V, 0 < (t : ℝ) ∧ x.1 ⟨U, hU, le_rfl⟩ t 0 = Y ∧
      (∀ u v, v < t → Y < x.1 u v 0) ∧ (∀ u v, v ≤ t → Y ≤ x.1 u v 0) := by
  let uU : Icc 0 U := ⟨U, hU, le_rfl⟩
  have hanti (v : Icc 0 V) : StrictAnti (fun u => x.1 u v 0) := by
    apply hx.radial_strictAnti hx.choose rfl
    · filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
      rw [hu]
      rfl
    · intro u
      exact (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1
  let g : ℝ → ℝ := fun t => intervalExtension hV (x.1 uU) t 0
  have hgc : Continuous g := by fun_prop
  have hg (t : ℝ) (ht : t ∈ Icc 0 V) : g t = x.1 uU ⟨t, ht⟩ 0 := by
    simp only [g, intervalExtension_apply, projIcc_of_mem hV ht]
  have hg0 : Y < g 0 := by
    rw [hg 0 ⟨le_rfl, hV⟩, (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).1 uU]
    exact hinit
  obtain ⟨u, v, hv⟩ := hbad
  have hvY : g v ≤ Y := by
    rw [hg v v.property]
    exact ((hanti v).antitone (show u ≤ uU from u.property.2)).trans hv
  obtain ⟨w, hw, hwY⟩ := intermediate_value_Icc' v.property.1 hgc.continuousOn ⟨hvY, hg0.le⟩
  let S := Icc (0 : ℝ) V ∩ {t | g t = Y}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hgc continuous_const)
  obtain ⟨t, ht, hmin⟩ := hS.exists_isMinOn ⟨w, ⟨⟨hw.1, hw.2.trans v.property.2⟩, hwY⟩⟩
    continuous_id.continuousOn
  have htp : 0 < t := lt_of_le_of_ne ht.1.1 (by intro he; exact hg0.ne' (he ▸ ht.2))
  have hbefore (q : ℝ) (hq : q ∈ Ico 0 t) : Y < g q := by
    by_contra hnot
    obtain ⟨w, hw, hwY⟩ := intermediate_value_Icc' hq.1 hgc.continuousOn ⟨not_lt.1 hnot, hg0.le⟩
    exact (hw.2.trans_lt hq.2).not_ge
      (hmin (show w ∈ S from ⟨⟨hw.1, (hw.2.trans hq.2.le).trans ht.1.2⟩, hwY⟩))
  refine ⟨⟨t, ht.1⟩, htp, (hg t ht.1).symm.trans ht.2, ?_, ?_⟩
  · intro u v hvt
    exact ((hbefore v ⟨v.property.1, hvt⟩).trans_eq (hg v v.property)).trans_le
      ((hanti v).antitone (show u ≤ uU from u.property.2))
  · intro u v hvt
    have hq : Y ≤ g v := by
      rcases lt_or_eq_of_le hvt with hlt | heq
      · exact (hbefore v ⟨v.property.1, hlt⟩).le
      · simpa only [show (v : ℝ) = t from congrArg Subtype.val heq] using ht.2.ge
    exact (hq.trans_eq (hg v v.property)).trans ((hanti v).antitone (show u ≤ uU from u.property.2))

end CauchyHorizon
