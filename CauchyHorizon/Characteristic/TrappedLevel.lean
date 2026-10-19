import CauchyHorizon.Characteristic.PhysicalOverlap
import CauchyHorizon.Characteristic.OutgoingConstraint

/-! Strict radial decrease after trapping and uniqueness of trapped radius levels. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.outgoing_trapped_radius_lt {M e Λ U V : ℝ} {h r : ℝ → ℝ}
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
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a < b) (ha : x.2.1 u a 0 < 0) :
    x.1 u b 0 < x.1 u a 0 := by
  let rad : ℝ → ℝ := fun t => intervalExtension hV (x.1 u) t 0
  have hanti : StrictAntiOn rad (Icc (a : ℝ) b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (by fun_prop)
    intro t ht
    rw [interior_Icc] at ht
    have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.le.trans b.property.2⟩
    have hd := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (hx.longitudinal_derivative u htV)
    change HasDerivWithinAt rad (x.2.1 u ⟨t, htV⟩ 0) (Icc 0 V) t at hd
    rw [(hd.hasDerivAt (Icc_mem_nhds (a.property.1.trans_lt ht.1) (ht.2.trans_le b.property.2))).deriv]
    exact (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a ⟨t, htV⟩ ht.1.le ha).1
  simpa only [rad, intervalExtension_apply, projIcc_of_mem hV a.property, projIcc_of_mem hV b.property] using
    hanti (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab

theorem IsWaveIntegral.trapped_level_time_unique {M e Λ A B U V u t s Y : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hfA : MemLp f p (volume.restrict (Icc 0 A))) (hfU : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState A B} {y : WaveState U V}
    (hx : IsWaveIntegral hA hB e Λ (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ B hc hi hrc hr0) (incomingWaveVelocity hAR hp hfA) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hfU) y)
    (huA : u ∈ Icc 0 A) (huU : u ∈ Icc 0 U) (htB : t ∈ Icc 0 B) (hsV : s ∈ Icc 0 V)
    (hxt : x.1 ⟨u, huA⟩ ⟨t, htB⟩ 0 = Y) (hys : y.1 ⟨u, huU⟩ ⟨s, hsV⟩ 0 = Y)
    (hlt : x.2.1 ⟨u, huA⟩ ⟨t, htB⟩ 0 < 0) (hls : y.2.1 ⟨u, huU⟩ ⟨s, hsV⟩ 0 < 0) : t = s := by
  rcases lt_trichotomy t s with hts | heq | hst
  · have htV : t ∈ Icc 0 V := ⟨htB.1, hts.le.trans hsV.2⟩
    have he := hx.horizon_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy huA huU htB htV
    have hl : y.2.1 ⟨u, huU⟩ ⟨t, htV⟩ 0 < 0 := by rw [← he.2]; exact hlt
    have hh := hy.outgoing_trapped_radius_lt hU hV hUR hc hi hrc hr0 hφ hrd hp hfU
      ⟨u, huU⟩ ⟨t, htV⟩ ⟨s, hsV⟩ hts hl
    rw [hys, ← he.1, hxt] at hh
    exact hh.false.elim
  · exact heq
  · have hsB : s ∈ Icc 0 B := ⟨hsV.1, hst.le.trans htB.2⟩
    have he := hy.horizon_overlap hU hV hUR hA hB hAR hc hi hrc hr0 hp hfU hfA hx huU huA hsV hsB
    have hl : x.2.1 ⟨u, huA⟩ ⟨s, hsB⟩ 0 < 0 := by rw [← he.2]; exact hls
    have hh := hx.outgoing_trapped_radius_lt hA hB hAR hc hi hrc hr0 hφ hrd hp hfA
      ⟨u, huA⟩ ⟨s, hsB⟩ ⟨t, htB⟩ hst hl
    rw [hxt, ← he.1, hys] at hh
    exact hh.false.elim

end CauchyHorizon
