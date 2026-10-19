import CauchyHorizon.Characteristic.BandGeometry

/-! A mass barrier bounds a trapped segment away from a positive-radius level. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.trapped_radius_barrier (B : Background) {U V ρ : ℝ} {h r : ℝ → ℝ}
    (hρ : 0 < ρ) (hF : 0 < B.F ρ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR hp hf) x)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0)
    (hra : ρ ≤ x.1 u a 0) :
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u b ≤ B.mass + ρ * B.F ρ / 4 →
      ρ < x.1 u b 0 := by
  dsimp only
  intro hm
  by_contra hnot
  let rad := fun t => intervalExtension hV (x.1 u) t 0
  have hrb : rad b ≤ ρ := by simpa only [rad, intervalExtension_apply, projIcc_of_mem hV b.property] using not_lt.1 hnot
  have hra' : ρ ≤ rad a := by simpa only [rad, intervalExtension_apply, projIcc_of_mem hV a.property] using hra
  obtain ⟨t, ht, hhit⟩ := intermediate_value_Icc' (show (a : ℝ) ≤ b from hab)
    (show ContinuousOn rad (Icc (a : ℝ) b) by fun_prop) ⟨hrb, hra'⟩
  have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
  let v : Icc 0 V := ⟨t, htV⟩
  have hrhit : x.1 u v 0 = ρ := by simpa only [rad, intervalExtension_apply, projIcc_of_mem hV htV] using hhit
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v
  have hmm : m ≤ B.mass + ρ * B.F ρ / 4 :=
    (hx.mass_monotone hU hV hUR hc hi hrc hr0 hφ hrd hp hf u ht.2).trans hm
  have hpert : 2 * (m - B.mass) / ρ ≤ B.F ρ / 2 := by
    apply (div_le_iff₀ hρ).2
    nlinarith only [hmm]
  have hFm : 0 < horizonFunction ρ m B.charge B.cosmological := by
    rw [horizonFunction_mass_difference ρ m B.mass]
    change 0 < B.F ρ - 2 * (m - B.mass) / ρ
    linarith only [hF, hpert]
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hid := massField_lambda_eq_kappa (e := B.charge) (Λ := B.cosmological)
    x.1 x.2.1 ν hx.choose (fun w s => (hg w s).2.2.1.ne) u v
  rw [hrhit] at hid
  have hlpos : 0 < x.2.1 u v 0 := by rw [hid]; exact mul_pos (hg u v).2.2.2.1 hFm
  exact (not_lt_of_ge hlpos.le) (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a v ht.1 ha).1

end CauchyHorizon
