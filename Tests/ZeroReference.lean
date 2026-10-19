import CauchyHorizon.Characteristic.ZeroBottom
import CauchyHorizon.Reduced.ScalarBoundary
import CauchyHorizon.Reduced.BoundaryConstraint
import CauchyHorizon.Characteristic.ZeroScalarSign
import CauchyHorizon.Characteristic.ZeroScalarGlobal
import CauchyHorizon.Reduced.BoundarySign
import CauchyHorizon.Characteristic.MassProfile

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Tests

-- At p = 4 the zero source permits 7a/8, beyond the general 3a/4 weight.
example {M e Λ U V a ρ N L H D : ℝ} {h r : ℝ → ℝ}
    (ha : 0 < a) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (hf : MemLp (fun _ : ℝ => (0 : ℝ)) 4 (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0)
    (hν : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hout : ∀ v : Icc 0 V, Real.exp ((7 * a / 8) * v) * |h v| ≤ H)
    (hwidth : U * Real.exp (a * V) ≤ D) :
    let E := H / ρ * Real.exp (L * N * D / (ρ ^ 2 * (a / 8)))
    3 * a / 4 < 7 * a / 8 ∧
      (∀ u v, |x.2.1 u v 1| ≤ E * Real.exp (-(7 * a / 8) * v)) ∧
        ∀ u v, |scalarTransportCorrection hV
          (radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose)
          x.2.1 u v| ≤ N * E / (a / 8) * Real.exp ((a / 8) * v) := by
  intro E
  refine ⟨by linarith only [ha], ?_⟩
  have hh := hx.horizon_zero_weighted_scalar hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
    (c := 7 * a / 8) (by positivity) (by linarith only [ha]) hρ hN hL hH hlo hν hlam hout hwidth
  simpa only [show a - 7 * a / 8 = a / 8 by ring] using hh

-- The actual reference bottom is uniformly small at late times at critical p = 4.
example (B : Background) {s H dH : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    (hbcrit : B.criticalExponent = 3 / 4) (hks : B.innerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ : ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧
          ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp (fun _ : ℝ => (0 : ℝ)) 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl hfU) x),
                ∀ (v : Icc 0 V), (v : ℝ) ∈ Ioo 0 V → T ≤ (v : ℝ) →
                  ∀ χ : ℝ → ℝ, ContinuousOn χ (Icc 0 (Z - Y)) →
                    (∀ w ∈ Icc 0 (Z - Y), χ w ∈ Ioo 0 U ∧
                      x.1 (projIcc 0 U hU (χ w)) v 0 = Z - w) →
                    let ν := radialNuField hV B.charge B.cosmological
                      (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
                    let q := fun w => Real.exp (B.innerRate * v) * χ w *
                      scalarTransportCorrection hV ν x.2.1 (projIcc 0 U hU (χ w)) v /
                        B.criticalWeight (x.1 (projIcc 0 U hU (χ w)) v 0)
                    let F := fun w => (-1 / x.2.1 (projIcc 0 U hU (χ w)) v 0) * q w ^ 2
                    0 ≤ ∫ w in 0..(Z - Y), F w ∧ (∫ w in 0..(Z - Y), F w) < ε := by
  intro hi hr0
  have hm : B.criticalExponent < 1 := by rw [hbcrit]; norm_num
  obtain ⟨δ, R, γ, hδ, hR, hγ, hband⟩ := B.exists_zero_bottom_decay
    hs hH hdH hdHR hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, K, T₀, hU₀, hUδ, _hK, hT₀, hbound⟩ := hband Y Z hY hYZ hYR hZ
  refine ⟨U₀, hU₀, hUδ, ?_⟩
  intro ε hε
  have hzero : Tendsto (fun t : ℝ => K * Real.exp (-(2 * γ) * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith only [hγ] : -(2 * γ) < 0))).const_mul K
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hzero.eventually_lt_const hε)
  refine ⟨max T₀ T, hT₀.trans_le (le_max_left _ _), ?_⟩
  intro U V hU hV hUR hUU hfU x hx v hv hTv χ hχc hχ ν q F
  have hh := hbound 4 le_rfl U V hU hV hUR hUU hfU x hx v hv
    ((le_max_left _ _).trans hTv) χ hχc hχ
  exact ⟨hh.2.1, hh.2.2.1.trans_lt (hT v ((le_max_right _ _).trans hTv))⟩

-- A zero vertical source has exactly zero increments, including a degenerate interval.
example {U V : ℝ} (hV : 0 ≤ V) (N : C(Icc 0 U, C(Icc 0 V, ℝ)))
    (w : WaveRectangle U V) (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b)
    (hzero : ∀ t ∈ Icc a b, N u t * w u t 1 = 0) :
    scalarTransportCorrection hV N w u b = scalarTransportCorrection hV N w u a := by
  have hh := scalarTransportCorrection_tail_bound hV N w u a b hab
    (C := 0) (η := 1) le_rfl (by norm_num) (by intro t ht; simp only [hzero t ht, abs_zero, zero_mul, le_refl])
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm
    (by simpa only [zero_div, zero_mul] using hh) (abs_nonneg _)))

-- For the zero incoming reference the correction is the actual transverse scalar.
example {U V R e Λ φ₀ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    (hf : MemLp (fun _ : ℝ => (0 : ℝ)) 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      x.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1 = scalarTransportCorrection hV
        (radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) x.1 hx.choose)
        x.2.1 (projIcc 0 U hU t) v := by
  filter_upwards [hx.zeta_transport hx.choose
    (incomingWave_constraint_data hU hUR le_rfl hf φ₀).1,
    incomingWaveVelocity_ae hUR le_rfl hf] with t ht hi
  intro v
  have hs : incomingWaveVelocity hUR le_rfl hf t 1 = 0 := by rw [hi]; rfl
  simpa only [hs, mul_zero, zero_add] using ht v

-- The boundary identity retains precisely the physical density zeta^2/(r*A).
example {d U : ℝ} (hdU : d ≤ U) (Z : C(Icc d U, WaveVector)) (N S : C(Icc d U, ℝ))
    (h : BoundaryTransverseConstraint hdU Z N S) (u : Icc d U) :
    N u / waveAmplitude Z u = N ⟨d, le_rfl, hdU⟩ / waveAmplitude Z ⟨d, le_rfl, hdU⟩ -
      ∫ t in d..(u : ℝ), S (projIcc d U hdU t) ^ 2 /
        (Z (projIcc d U hdU t) 0 * waveAmplitude Z (projIcc d U hdU t)) := by
  have ha (x : Icc d U) : Real.exp (-Z x 2) = (waveAmplitude Z x)⁻¹ := Real.exp_neg _
  simpa only [ha, div_eq_mul_inv, mul_inv_rev, mul_assoc] using h u

-- A vanishing transverse scalar leaves the weighted radial trace constant.
example {d U : ℝ} (hdU : d ≤ U) (Z : C(Icc d U, WaveVector)) (N : C(Icc d U, ℝ))
    (h : BoundaryTransverseConstraint hdU Z N 0) (u : Icc d U) :
    N u * Real.exp (-Z u 2) = N ⟨d, le_rfl, hdU⟩ * Real.exp (-Z ⟨d, le_rfl, hdU⟩ 2) := by
  simpa only [ContinuousMap.zero_apply, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
    zero_div, intervalIntegral.integral_zero, sub_zero] using h u

-- The lower outgoing tail supplies the actual outer sign at p=4 without a sign assumption on theta.
example (B : Background) {s l c H Hlo dH : ℝ} {h r : ℝ → ℝ}
    (hs : 0 < s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s)
    (hl : l < 2 * s + c) (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hlo : ∀ t ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * t) ≤ h t)
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ W : ℝ, 0 < δ ∧ 0 < W ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (hf : MemLp (fun _ : ℝ => (0 : ℝ)) 4 (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_rfl hf) x),
        U ≤ W → U * Real.exp (B.outerRate * V) ≤ δ →
          (∀ u v, scalarPositiveLambdaCorrection hU hV x.1 x.2.1
            (radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose) u v < h v) ∧
          (∀ u v, 0 < x.1 u v 0 * x.2.1 u v 1) ∧
          ∀ u (v : Icc 0 V), 0 < (v : ℝ) → 0 < scalarTransportCorrection hV
            (radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose) x.2.1 u v := by
  obtain ⟨δ, W, hδ, hW, hpos⟩ := B.exists_zero_outer_scalar_positive hs hc0 hca hcs hl hH hHlo
    hdH hdHR hc hb hlo hrc hrb hrd hrdec hOut
  exact ⟨δ, W, hδ, hW, fun U V hU hV hUR hf x hx hUW hw =>
    hpos U V hU hV hUR 4 le_rfl hf x hx hUW hw⟩

-- With nonpositive lambda the adverse correction vanishes exactly.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, 0 < x.1 u v 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinzero : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 1 = 0)
    (hN : ∀ u v, radialNuField hV e Λ zIn x.1 (fun u v => (hr u v).ne') u v < 0)
    (hlam : ∀ u v, x.2.1 u v 0 ≤ 0)
    (haxis : ∀ v, 0 < x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1) :
    ∀ u v, 0 < x.1 u v 0 * x.2.1 u v 1 := by
  apply (hx.zero_scalar_positive hr hzin hinu hinzero hN ?_).1
  intro u v
  simpa only [scalarPositiveLambdaCorrection, max_eq_right (hlam _ _), zero_mul, zero_div,
    intervalIntegral.integral_zero] using haxis v

-- The global p=4 reference sign persists in its actual horizon traces.
example (B : Background) {s l c H Hlo dH : ℝ} {h r : ℝ → ℝ}
    (hs : 0 < s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s)
    (hl : l < 2 * s + c) (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hlo : ∀ t ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * t) ≤ h t)
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ W : ℝ, 0 < W ∧ ∀ (U : ℝ) (hU : 0 ≤ U) (hUR : U < r 0), U ≤ W →
      ∀ (hf : MemLp (fun _ : ℝ => (0 : ℝ)) 4 (volume.restrict (Icc 0 U)))
        (X : (T : Ici (0 : ℝ)) → WaveState U T)
        (hX : ∀ (T : Ici (0 : ℝ)), IsWaveIntegral hU T.property B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
          (incomingWaveVelocity hUR le_rfl hf) (X T)),
        let N := fun T : Ici (0 : ℝ) => radialNuField T.property B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) (X T).1 (hX T).choose
        let S := fun T => scalarTransportCorrection T.property (N T) (X T).2.1
        ∀ (d k : ℝ) (hd : 0 ≤ d) (hdU : d ≤ U),
          TransverseBoundaryGeometry hd hdU k X N →
          ∃ Nh Sh : C(Icc d U, ℝ),
            Tendsto (scalarBoundaryRow hd N) atTop (𝓝 Nh) ∧
            Tendsto (scalarBoundaryRow hd S) atTop (𝓝 Sh) ∧
            (∀ u, 0 < Sh u) ∧ ∀ u : Icc d U, d < (u : ℝ) → Nh u < 0 := by
  intro hi hr0
  obtain ⟨W, hW, hpositive⟩ := B.exists_zero_scalar_positive
    hs hc0 hca hcs hl hH hHlo hdH hdHR hc hb hlo hrc hrb hrd hrdec hOut
  refine ⟨W, hW, ?_⟩
  intro U hU hUR hUW hf X hX N S d k hd hdU hgeo
  have hp (T : Ici (0 : ℝ)) := hpositive U T hU T.property hUR 4 le_rfl hf (X T) (hX T) hUW
  obtain ⟨Z, Nh, Sh, _, hNlim, hSlim, hsign, hcon⟩ := hgeo
  have hcompat (T V : Ici (0 : ℝ)) (hTV : T ≤ V) u v :
      S T u v = S V u ⟨v, v.property.1, v.property.2.trans hTV⟩ := by
    have hh := (hX T).horizon_overlap_zeta hU T.property hUR hU V.property hUR
      hc hi hrc hr0 (p := 4) le_rfl hf hf (hX V) u.property u.property v.property
      ⟨v.property.1, v.property.2.trans hTV⟩
    simpa only [mul_zero, zero_add] using hh
  have hSh := scalarBoundaryRow_pos_of_monotone hd S hcompat
    (fun T u => (hp T).2.2 u)
    (fun u => (hp ⟨1, (show (0 : ℝ) ≤ 1 from zero_le_one)⟩).2.1 u
      ⟨1, zero_le_one, le_rfl⟩ zero_lt_one) Sh hSlim
  exact ⟨Nh, Sh, hNlim, hSlim, hSh,
    hcon.strict_negative (fun u => (hsign u).1) (fun u => (hsign u).2) hSh⟩

-- The mass profile keeps a strictly positive coefficient even at the compact interval's left endpoint.
example {U ε k a c e Λ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T)
    (N : (n : ℕ) → (T : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)))
    (hr : ∀ n (T : Ici (0 : ℝ)) u v, (X n T).1 u v 0 ≠ 0)
    (ℓ : ℕ → ℝ) (P : ℕ → ℝ → ℝ)
    (hprofile : RadiationMassProfile hε k a c e Λ X N hr ℓ P) :
    ∃ Γ : C(Icc ε U, ℝ), 0 < Γ ⟨ε, le_rfl, hεU⟩ ∧
      MassProfileLimit (fun n => massRow hε e Λ (X n) (N n) (hr n)) Γ a ℓ P := by
  obtain ⟨_, _, Γ, _, _, hsign, hlimit⟩ := hprofile
  exact ⟨Γ, (hsign ⟨ε, le_rfl, hεU⟩).2.2.2.2, hlimit⟩

end CauchyHorizon.Tests
