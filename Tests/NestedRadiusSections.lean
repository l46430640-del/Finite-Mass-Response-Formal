import CauchyHorizon.Characteristic.NestedRadiusSections
import CauchyHorizon.Characteristic.RadiusNormalization
import CauchyHorizon.Characteristic.AuxiliaryRadiusCharts

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Tests

-- The cutoff precedes the profile; an already supplied physical radius point is preserved.
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R L : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧ 0 < L ∧
      ∀ Y Z U : ℝ, B.inner < Y → Y < Z → Z ≤ R → 0 < U →
        ∃ T : ℝ, 0 < T ∧
          ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
            (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Ici T) ∧
              (∀ t ∈ Ici T, t < ψ t ∧ ψ t ≤ (17 / 16) * t) ∧
              ∀ (W V : ℝ) (hW : 0 ≤ W) (hV : 0 ≤ V) (hWR : W < r 0)
                (hfW : MemLp f 4 (volume.restrict (Icc 0 W))) (x : WaveState W V)
                (_hx : IsWaveIntegral hW hV B.charge B.cosmological
                  (incomingWaveCurve hW hWR le_rfl hfW (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hWR le_rfl hfW) x),
                U ≤ W → ∀ t ∈ Ici T, ψ t ≤ V → ∀ u : Icc 0 W,
                  x.1 u (projIcc 0 V hV t) 0 = Z →
                    x.1 u (projIcc 0 V hV (ψ t)) 0 = Y ∧
                    ∀ hr : ∀ q v, x.1 q v 0 ≠ 0,
                      let ν := radialNuField hV B.charge B.cosmological
                        (incomingWaveCurve hW hWR le_rfl hfW (horizonPhi h r 0)) x.1 hr
                      let v := projIcc 0 V hV (ψ t)
                      Real.exp (-1) * (-B.F Y) / B.outerRate ≤ (u : ℝ) * (-ν u v) ∧
                      (u : ℝ) * (-ν u v) ≤ Real.exp 1 * (-B.F Y) / B.outerRate ∧
                      0 < -x.2.1 u v 0 ∧ -x.2.1 u v 0 ≤ L * (Y - B.inner) := by
  obtain ⟨δ, R, L, hδ, _hδr, hR, hL, hsections⟩ := B.exists_nested_radius_sections
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, L, hδ, hR, hL, ?_⟩
  intro Y Z U hY hYZ hZR hU
  obtain ⟨T, hT, hsolve⟩ := hsections Y Z (1 / 16) U hY hYZ hZR (by norm_num) hU
  refine ⟨T, hT, ?_⟩
  intro f hf hfn
  simpa only [show (1 : ℝ) + 1 / 16 = 17 / 16 by norm_num] using hsolve 4 le_rfl f hf hfn

-- Normalization holds at any supplied radius point, also for bounded incoming data.
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R →
        ∃ τ : Ioi (0 : ℝ) → ℝ, (∀ U, 0 < τ U) ∧
          ∀ f : ℝ → ℝ, MemLp f ∞ (volume.restrict (Icc 0 δ)) →
            (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (U : Ioi (0 : ℝ)) (W V : ℝ) (hW : 0 ≤ W) (hV : 0 ≤ V) (hWR : W < r 0),
              U ≤ W → ∀ (hfW : MemLp f ∞ (volume.restrict (Icc 0 W))) (x : WaveState W V)
                (hx : IsWaveIntegral hW hV B.charge B.cosmological
                  (incomingWaveCurve hW hWR le_top hfW (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hWR le_top hfW) x) (u : Icc 0 W) (v : Icc 0 V),
                τ U ≤ v → x.1 u v 0 = Y →
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hW hWR le_top hfW (horizonPhi h r 0)) x.1 hx.choose
                  0 < (u : ℝ) ∧ |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F Y))| < 1 / 2 := by
  obtain ⟨δ, R, hδ, hR, hsolve⟩ := B.exists_physical_radius_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨τ, hτ, hnorm⟩ := hsolve Y hY hYR
  let ε : Ioi (0 : ℝ) := ⟨1 / 2, by norm_num⟩
  exact ⟨τ ε, hτ ε, fun f hf hfn => hnorm ∞ le_top f hf hfn ε⟩

-- The fixed gamma supplies all shorter horizontal charts, including a collapsed interval.
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R L : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧ 0 < L ∧
      ∀ Y Z U T₀ D η : ℝ, B.inner < Y → Y < Z → Z ≤ R → ∀ hU : 0 < U, 0 ≤ T₀ → 0 < η →
        ∃ S : ℝ, 0 < S ∧
          ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
            (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (hUR : U < r 0) (hfU : MemLp f 4 (volume.restrict (Icc 0 U)))
              (X : (V : Ici (0 : ℝ)) → WaveState U V)
              (hX : ∀ V : Ici (0 : ℝ), IsWaveIntegral hU.le V.property B.charge B.cosmological
                (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR le_rfl hfU) (X V)) (g : ℝ → ℝ),
              ContinuousOn g (Ici T₀) → StrictAntiOn g (Ici T₀) → Tendsto g atTop (𝓝 0) → U < g T₀ →
              (∀ t ∈ Ici T₀, 0 < g t ∧ DifferentiableAt ℝ g t ∧ η ≤ -deriv g t / g t ∧
                g t * Real.exp (B.outerRate * t) ≤ D) →
              (∀ (V : Ici (0 : ℝ)) t, T₀ ≤ t → g t ≤ U → t ≤ V →
                (X V).1 (projIcc 0 U hU.le (g t)) (projIcc 0 (V : ℝ) V.property t) 0 = Z) →
              ∀ (V : Ici (0 : ℝ)) (b : Icc 0 (V : ℝ)), S ≤ b →
                g ((b : ℝ) / (17 / 16)) ∈ Ioo 0 U ∧
                let w := projIcc 0 U hU.le (g ((b : ℝ) / (17 / 16)))
                ∃ z : Icc 0 U, 0 < (z : ℝ) ∧ z ≤ w ∧
                  ∀ (u : Icc 0 U) (hzu : z ≤ u), u ≤ w →
                  ∃ Q : C(Icc (z : ℝ) u, Icc 0 (V : ℝ)),
                  let τ := fun t => Q (projIcc (z : ℝ) u hzu t)
                  let ν := radialNuField V.property B.charge B.cosmological
                    (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0)) (X V).1 (hX V).choose
                  τ z = b ∧
                  (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
                    (-ν (projIcc 0 U hU.le t) (τ t) /
                      (X V).2.1 (projIcc 0 U hU.le t) (τ t) 0) t) ∧
                  ∀ t ∈ Icc (z : ℝ) u,
                    let q := projIcc 0 U hU.le t
                    (X V).1 q (τ t) 0 = Y ∧ ν q (τ t) < 0 ∧
                      Real.exp (-1) * (-B.F Y) / B.outerRate ≤ t * (-ν q (τ t)) ∧
                      t * (-ν q (τ t)) ≤ Real.exp 1 * (-B.F Y) / B.outerRate ∧
                      0 < -(X V).2.1 q (τ t) 0 ∧ -(X V).2.1 q (τ t) 0 ≤ L * (Y - B.inner) ∧
                      ∃ a : ℝ, T₀ < a ∧ (b : ℝ) / (17 / 16) ≤ a ∧ g a = t ∧
                        a < τ t ∧ τ t ≤ b ∧ (τ t : ℝ) ≤ (17 / 16) * a := by
  obtain ⟨δ, R, L, hδ, hR, hL, hsolve⟩ := B.exists_auxiliary_radius_charts
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, L, hδ, hR, hL, ?_⟩
  intro Y Z U T₀ D η hY hYZ hZR hU hT₀ hη
  obtain ⟨S, hS, hchart⟩ := hsolve Y Z (1 / 16) U T₀ D hY hYZ hZR (by norm_num) hU hT₀
  refine ⟨S, hS, ?_⟩
  intro f hf hfn hUR hfU X hX g hgc hga hgl hstart hgp hlevel
  have hgp' (t : ℝ) (ht : t ∈ Ici T₀) : 0 < g t ∧ DifferentiableAt ℝ g t ∧ deriv g t < 0 ∧
      g t * Real.exp (B.outerRate * t) ≤ D := by
    have hh := hgp t ht
    have hn := (mul_pos hη hh.1).trans_le ((le_div_iff₀ hh.1).1 hh.2.2.1)
    exact ⟨hh.1, hh.2.1, neg_pos.1 hn, hh.2.2.2⟩
  simpa only [show (1 : ℝ) + 1 / 16 = 17 / 16 by norm_num] using
    hchart 4 le_rfl f hf hfn hUR hfU X hX g hgc hga hgl hstart hgp' hlevel

-- Every observed subsegment gets the small lambda coefficient without a terminal gamma premise.
example (B : Background) {U V T₀ β Y L S : ℝ} (hU : 0 ≤ U)
    (x : WaveState U V) (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (g : ℝ → ℝ)
    (hc : AuxiliaryRadiationCharts B hU x ν g T₀ β Y L S)
    (b : Icc 0 V) (hb : S ≤ b) :
    let w := projIcc 0 U hU (g ((b : ℝ) / (1 + β)))
    ∃ z : Icc 0 U, 0 < (z : ℝ) ∧ z ≤ w ∧
      ∀ (u : Icc 0 U) (hzu : z ≤ u), u ≤ w →
      ∃ Q : C(Icc (z : ℝ) u, Icc 0 V),
        let τ := fun t => Q (projIcc (z : ℝ) u hzu t)
        τ z = b ∧ ∀ t ∈ Icc (z : ℝ) u,
          let q := projIcc 0 U hU t
          x.1 q (τ t) 0 = Y ∧ (b : ℝ) / (1 + β) < τ t ∧
            ∀ v ∈ Icc (τ t) b,
              B.inner / 2 ≤ x.1 q v 0 ∧
              |ν q v| ≤ (2 * Real.exp 2) * (-ν q (τ t)) *
                Real.exp (-2 * B.innerRate * ((v : ℝ) - τ t)) ∧
              |x.2.1 q v 0| ≤ (Real.exp (2 + 1 / 16) * (L * (Y - B.inner))) *
                Real.exp (-2 * B.innerRate * ((v : ℝ) - τ t)) := by
  obtain ⟨_hw, z, hz, hzw, hrow⟩ := hc b hb
  refine ⟨z, hz, hzw, ?_⟩
  intro u hzu huw
  obtain ⟨Q, hQz, _hQd, hQp⟩ := hrow u hzu huw
  refine ⟨Q, hQz, ?_⟩
  intro t ht
  obtain ⟨hr, _hn, _hnl, _hnh, _hl, hL, ⟨a, _ha, hba, _hga, haτ, _hτb, _hτγ⟩, hdec⟩ := hQp t ht
  refine ⟨hr, hba.trans_lt haτ, ?_⟩
  intro v hv
  have hd := hdec _ v le_rfl hv.1 hv.2
  exact ⟨hd.1, hd.2.1, hd.2.2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le) (Real.exp_pos _).le)⟩

end CauchyHorizon.Tests
