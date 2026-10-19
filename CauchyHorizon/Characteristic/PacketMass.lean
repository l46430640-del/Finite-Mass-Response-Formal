import CauchyHorizon.Characteristic.ProfileMass
import CauchyHorizon.Characteristic.PacketProfile
import CauchyHorizon.Reduced.MassContinuity
import CauchyHorizon.Characteristic.PacketQuantiles
import CauchyHorizon.Characteristic.ContinuousFirstOrder
import CauchyHorizon.Characteristic.OpticalIdentities
import CauchyHorizon.Characteristic.ContinuousWave
import CauchyHorizon.Characteristic.RadiationPhase

/-! Actual nonlinear developments of the explicit packets have a finite positive terminal response. -/

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology ENNReal ContDiff

namespace CauchyHorizon.Background

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 4096 in
def PacketMassResponse (B : Background) {s l : ℝ} (D : AdmissibleOutgoingData B s l)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (ψ : ℝ → ℝ) (E : ℝ) (t L : ℕ → ℝ) (ℓ Ucap : ℝ) : Prop :=
    let h := D.tail
    let r := D.radius
    let hc := D.tail_continuous
    let hrc := D.radius_continuous
    let hi := horizon_mass_integrable D.rate_pos D.upper_nonneg hc D.tail_bound
    let hr0 := fun v => ((sub_pos.2 D.deviation_lt).trans_le (D.radius_lower v)).ne'
    let cν := Real.exp (∫ v in Ioi 0,
      2 * horizonK (r v) (horizonMass B.mass h v) B.charge B.cosmological - B.outerRate)
    let Ch := r 0 / (B.event * cν ^ B.criticalExponent)
    ∃ P : ℕ → ℝ →ᵇ ℝ, P 0 = 0 ∧
      (∀ n, n ≠ 0 → ∀ x, P n x = Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) *
        ψ ((x - t n) / L n)) ∧
      (∀ U₀ : ℝ, 0 < U₀ →
        (∀ n, 0 ≤ primitiveEnergy (1 - 1 / p.toReal)
          (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U₀ ∧
          primitiveEnergy (1 - 1 / p.toReal) (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U₀ ≤ E) ∧
        Tendsto (fun n => primitiveEnergy (1 - 1 / p.toReal)
          (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U₀) atTop (𝓝 E)) ∧
      ∃ U : ℝ, ∃ hU : 0 < U, ∃ hUR : U < r 0, U ≤ Ucap ∧
        ∃ hf : ∀ n, MemLp (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p
            (volume.restrict (Icc 0 U)),
        ∃ hm : B.criticalExponent < 1,
        ∃ X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V,
          (∀ n (V : Ici (0 : ℝ)), IsWaveIntegral hU.le V.property B.charge B.cosmological
            (incomingWaveCurve hU.le hUR hp (hf n) (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp (hf n)) (X n V)) ∧
          (∀ n (V : Ici (0 : ℝ)), HasContinuousFirstOrderEquations hU.le V.property B.charge B.cosmological
            (incomingWaveCurve hU.le hUR hp (hf n) (horizonPhi h r 0)) (X n V)) ∧
          (∀ n (V : Ici (0 : ℝ)), HasOpticalFluxEquations V.property B.charge B.cosmological
            (incomingWaveCurve hU.le hUR hp (hf n) (horizonPhi h r 0)) (X n V)) ∧
          (∀ n (V : Ici (0 : ℝ)), HasContinuousWaveSystem hU.le V.property B.charge B.cosmological
            (incomingWaveCurve hU.le hUR hp (hf n) (horizonPhi h r 0)) (X n V)) ∧
          (∀ n V u v, 3 * B.inner / 4 ≤ (X n V).1 u v 0) ∧
          (∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T),
            waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
              le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X n T) = X n S) ∧
          (∀ V : Ici (0 : ℝ), Tendsto (fun n => X n V) atTop (𝓝 (X 0 V))) ∧
          HasConvergentIncomingData hU.le hUR hp
            (fun n => logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) hf (horizonPhi h r 0) ∧
          HasUniformMassBound B.charge B.cosmological
            (fun n => incomingWaveCurve hU.le hUR hp (hf n) (horizonPhi h r 0)) X ∧
          ∃ χ : ℕ → ℝ → ℝ,
          (∀ n, IsRegularTimeCoordinate (anchoringLapse hU.le (X n)) 0 (χ n)) ∧
          ∀ ε (hε : 0 < ε) (hεU : ε ≤ U),
            (∀ d : ℝ,
              let F := radiationComparisonRow hε.le B.innerRate (B.transmission hm * Ch)
                X (fun n v => P n (B.outerRate * v + d))
              (∀ n, MemLp (F n) 2 (volume.restrict (Ici 0))) ∧
                Tendsto (fun n => ∫ v in Ici (0 : ℝ), ‖F n v‖ ^ 2) atTop (𝓝 0)) ∧
            (∃ Td Cd d : ℝ, 0 ≤ Td ∧ 0 < Cd ∧ 0 < d ∧ ∃ Dh : ℕ → C(Icc ε U, ℝ),
              ∃ Zg : ℕ → C(Icc ε U, WaveVector),
              (∀ n, Tendsto (renormalizedWaveRow hε.le B.innerRate (X n)) atTop (𝓝 (Zg n))) ∧
              (∀ n, Tendsto (opticalRow hε.le (X n)) atTop (𝓝 (Dh n))) ∧
              (∀ n v, Td ≤ v → ‖opticalRow hε.le (X n) v - Dh n‖ ≤
                Cd * ∫ w in Ioi v, ‖radiationRow B.innerRate (X n) w‖ ^ 2) ∧
              (∀ n u, d ≤ Dh n u) ∧
              (∀ n v, 0 ≤ v → ∀ u, opticalRow hε.le (X n) v u ≤ Dh n u) ∧
              (∀ n, Tendsto (lapseNormalizedRadialRow hε.le hεU B.innerRate (X n)) atTop
                (𝓝 (-(anchoredAmplitude ⟨U, hεU, le_rfl⟩ (Zg n)) * Dh n))) ∧
              (∀ n, Tendsto (fun w => lapseNormalizedRadialRow hε.le hεU B.innerRate (X n) (χ n w))
                (𝓝[<] (0 : ℝ)) (𝓝 (-(anchoredAmplitude ⟨U, hεU, le_rfl⟩ (Zg n)) * Dh n))) ∧
              (∀ n u, (-(anchoredAmplitude ⟨U, hεU, le_rfl⟩ (Zg n)) * Dh n) u < 0) ∧
              (∀ n, IsRegularRadiusBoundary hε.le hεU B.innerRate (X n) (χ n) (Zg n) (Dh n)) ∧
              (ε < U → ∀ n, ∃ Du : ℝ → C(Icc ε U, WaveVector), ∃ Duh : C(Icc ε U, WaveVector),
                IsTransverseWaveBoundary hU.le hεU (X n) (χ n) (Zg n) Du Duh ∧
                IsRegularWaveBoundary hε.le hεU (X n) (χ n) (Zg n) Du Duh ∧
                IsRegularWaveEvolution hε.le hεU B.charge B.cosmological (X n) (χ n) (Zg n) Du Duh ∧
                ∃ Tw Cw : ℝ, 0 ≤ Tw ∧ 0 < Cw ∧
                  IsRegularWaveEnergy hε.le hεU B.innerRate (X n) (χ n) (Zg n) Tw Cw ∧
                  HasBoundedRegularContinuationData hε.le hεU (X n) (χ n) (Zg n) (Dh n)
                    Du Duh (3 * B.inner / 4) Tw ∧
                  ∀ u₀ ∈ Ioo ε U, HasRegularCrossingSolution hε.le hεU B.charge B.cosmological
                    (X n) (χ n) (Zg n) (Dh n) Du Duh Tw u₀ ∧
                    HasLocalSphericalWeakExtension hε.le hεU B.charge B.cosmological (X n) (χ n) Tw u₀)) ∧
            (∃ Ts Cs : ℝ, 0 ≤ Ts ∧ 0 < Cs ∧
              ∀ n, IsRegularScalarEnergy hε.le hεU B.innerRate (X n) (χ n) Ts Cs) ∧
            (∃ Dφ : ℕ → ℝ → C(Icc ε U, ℝ), ∃ Dhφ : ℕ → C(Icc ε U, ℝ),
              ∀ n, IsTransverseScalarTrace hU.le (X n) (χ n) (Dφ n) (Dhφ n)) ∧
            (∀ n, ∃ Tc Cc : ℝ, 0 ≤ Tc ∧ 0 < Cc ∧
              IsRegularConformalEnergy hε.le hεU B.innerRate (X n) (χ n) Tc Cc) ∧
            (ε < U → ∀ n, ∃ Dℓ : ℝ → C(Icc ε U, ℝ), ∃ Dhℓ : C(Icc ε U, ℝ),
              IsTransverseConformalTrace hU.le (X n) (χ n) Dℓ Dhℓ) ∧
            ∃ hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0,
              let ν := fun n (V : Ici (0 : ℝ)) => radialNuField V.property B.charge B.cosmological
                (incomingWaveCurve hU.le hUR hp (hf n) (horizonPhi h r 0)) (X n V).1 (hr n V)
              HasCompactifiedGeometry hε.le B.innerRate X ν ∧
              ∃ Z : C(Icc ε U, WaveVector), ∃ Nh Γ : C(Icc ε U, ℝ),
                Tendsto (renormalizedWaveRow hε.le B.innerRate (X 0)) atTop (𝓝 Z) ∧
                Tendsto (scalarBoundaryRow hε.le (ν 0)) atTop (𝓝 Nh) ∧
                (∀ u, 0 < Z u 0 ∧ 0 < waveAmplitude Z u ∧ Nh u < 0 ∧
                  Γ u = (-2 * Nh u / (B.outerRate * waveAmplitude Z u)) *
                    (B.transmission hm * Ch) ^ 2 ∧ 0 < Γ u) ∧
                MassProfileLimit (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n))
                  Γ B.outerRate (fun _ => ℓ) (fun n => P n) ∧
                ∃ Mh : ℕ → C(Icc ε U, ℝ),
                  (∀ n, Tendsto (massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n))
                    atTop (𝓝 (Mh n))) ∧
                  (∀ v, 0 ≤ v →
                    Tendsto (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) v -
                      massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v) atTop (𝓝 0)) ∧
                  Tendsto (fun n => Mh n - Mh 0) atTop (𝓝 (E • Γ)) ∧
                  (∀ u, 0 < (E • Γ) u) ∧
                  ∃ T : ℝ, 0 ≤ T ∧
                    HasMassFirstCrossings
                      (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n)) Mh T ∧
                    HasMassQuantileAsymptotics ψ B.outerRate t L
                      (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n)) Mh T ∧
                    ∀ d > (0 : ℝ), ∀ᶠ n in atTop,
                    (∀ v, T ≤ v →
                      ‖massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) v -
                        massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v -
                        packetCumulative ψ ((B.outerRate * v - t n) / L n) • (E • Γ)‖ < d) ∧
                    ‖Mh n - Mh 0 - E • Γ‖ < d

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 4096 in
theorem exists_packet_mass_response (B : Background) {s l H Hlo dH : ℝ} {h r : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    (hcrit : B.innerRate = (1 - 1 / p.toReal) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    (hc : Continuous h) (hb : ∀ v, ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v)
    (hrc : Continuous r) (hrb : ∀ v, B.event - dH ≤ r v) (hrinit : B.inner < r 0)
    (hrd : ∀ v ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological) (Ici 0) v)
    (hrdec : ∀ v ∈ Ici (0 : ℝ), ‖r v - B.event‖ ≤ dH * Real.exp (-(2 * s) * v))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop)
    (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    B.PacketMassResponse {
      tail := h, radius := r, upper := H, lower := Hlo, deviation := dH,
      rate_pos := B.innerRate_pos.trans hks, upper_nonneg := hH, lower_pos := hHlo,
      deviation_nonneg := hdH, deviation_lt := hdHR, tail_continuous := hc,
      tail_bound := hb, tail_lower := hlo, radius_continuous := hrc, radius_lower := hrb,
      radius_initial := hrinit, radius_derivative := hrd, radius_decay := hrdec }
      hp ψ E t L ℓ Ucap := by
  obtain ⟨A, Apt, hA, hApt, P, Q, hP0, _hQ0, hPformula, hd, hPC,
    hPi, hPE, hQi, hQlim, hsuppP, hfront, hprimitive, hdata⟩ :=
    smooth_packet_incoming_data hp hpfin hψ hcomp hpos hsupp hE t L hL htop hLtop ℓ
  obtain ⟨U, hU, hUR, hcap, hfU, hm, X, hX, hfloor, hcompat, hfinite, hInitial, hbounded,
    χ, hχ, hresponse⟩ :=
    B.exists_profile_mass_response hp hpfin hcrit hks hl hH hHlo hdH hdHR
      hc hb hlo hrc hrb hrinit hrd hrdec hA.le hApt.le hE.le P Q hP0 hd hPC hPi hQi hQlim
      t ℓ hsuppP hfront hdata Ucap hUcap
  let D : AdmissibleOutgoingData B s l := {
      tail := h, radius := r, upper := H, lower := Hlo, deviation := dH,
      rate_pos := B.innerRate_pos.trans hks, upper_nonneg := hH, lower_pos := hHlo,
      deviation_nonneg := hdH, deviation_lt := hdHR, tail_continuous := hc,
      tail_bound := hb, tail_lower := hlo, radius_continuous := hrc, radius_lower := hrb,
      radius_initial := hrinit, radius_derivative := hrd, radius_decay := hrdec }
  have hfirst (n : ℕ) (V : Ici (0 : ℝ)) := (hX n V).continuous_first_order_equations B D
      hU.le V.property hUR hp (hfU n)
      (logarithmicIncoming_contDiff (hPC n) (1 - 1 / p.toReal) ℓ).continuousOn
  have hflux (n : ℕ) (V : Ici (0 : ℝ)) :=
    (hX n V).optical_flux_equations B D hU.le V.property hUR hp (hfU n)
  have hwave (n : ℕ) (V : Ici (0 : ℝ)) := (hX n V).continuous_wave_system B D
      hU.le V.property hUR hp (hfU n)
      (logarithmicIncoming_contDiff (hPC n) (1 - 1 / p.toReal) ℓ).continuousOn
  refine ⟨P, hP0, hPformula, hprimitive, U, hU, hUR, hcap, hfU, hm, X, hX, hfirst, hflux, hwave, hfloor, hcompat,
    hfinite, hInitial, hbounded, χ, hχ, ?_⟩
  intro ε hε hεU
  have : Nonempty (Icc ε U) := ⟨⟨U, hεU, le_rfl⟩⟩
  obtain ⟨hF, hOptical, hScalar, hTrace, hConf, hConfTrace, hr, hcompact, hmassFinite,
    Z, Nh, Γ, hZ, hNh, hsign, hmass⟩ := hresponse ε hε hεU
  let ν := fun n (T : Ici (0 : ℝ)) => radialNuField T.property B.charge B.cosmological
    (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hr n T)
  have hνcompat n (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v :
      ν n S u v = ν n T u ⟨v, v.property.1, v.property.2.trans hST⟩ := by
    apply radialNuField_prefix_eq S.property T.property hST B.charge B.cosmological
      _ _ _ (hr n T) (hr n S) ?_ u v
    intro w v
    have he := congrArg (fun x : WaveState U (S : ℝ) => x.1 w v) (hcompat n S T hST)
    change (X n T).1 ⟨0 + (w : ℝ), by simpa using w.property.1, by simpa using w.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X n S).1 w v at he
    simpa only [zero_add] using he.symm
  obtain ⟨Φ, Φ', hΦ, _hΦ', _hdΦ, hiΦ, _hiΦ', hMΦ⟩ :=
    smooth_packet_shape hψ hcomp (hpos (1 / 2) (by constructor <;> norm_num)).ne'
  have hiψ : Integrable (fun x => ψ x ^ 2) := by simpa only [hΦ] using hiΦ
  have hMψ : 0 < ∫ x, ψ x ^ 2 := by simpa only [hΦ] using hMΦ
  have hbound (x : ℝ) : |ψ x| ≤ ‖Φ‖ := by
    rw [← hΦ x, ← Real.norm_eq_abs]
    exact Φ.norm_coe_le_norm x
  obtain ⟨Tc, hTc, hcurve⟩ := hmass.packet_cumulative hE.le hiψ hMψ hbound hL hLtop hPformula
  refine ⟨radiation_comparison_phase hε.le B.outerRate_pos X P Q hd hQi hQlim hF,
    hOptical, hScalar, hTrace, hConf, hConfTrace,
    hr, hcompact, Z, Nh, Γ, hZ, hNh, hsign, hmass, ?_⟩
  obtain ⟨T, hT, Mh, hMh, herr⟩ := hmass
  have hterminal : Tendsto (fun n => Mh n - Mh 0) atTop (𝓝 (E • Γ)) := by
    apply Metric.tendsto_nhds.2
    intro d hdpos
    filter_upwards [herr d hdpos, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    simpa only [dist_eq_norm, hPE n hnpos.ne'] using hn.2
  have hfixed (v : ℝ) (hv : 0 ≤ v) :
      Tendsto (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) v -
        massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v) atTop (𝓝 0) := by
    simpa only [ν, sub_self] using (hmassFinite v hv).sub_const
      (massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v)
  have hpositive : ∀ u, 0 < (E • Γ) u := fun u => mul_pos hE (hsign u).2.2.2.2
  let Tq := max T Tc
  have hMc (n : ℕ) : ContinuousOn
      (massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n)) (Ici Tq) :=
    (continuousOn_massRow hε.le (X n) (ν n) (hr n) (hcompat n) (hνcompat n)).mono
      (fun _ hv => hT.trans ((le_max_left _ _).trans hv))
  have hfirst := mass_first_crossings hMc hMh (hfixed Tq (hT.trans (le_max_left _ _))) hterminal hpositive
  have herrors (d : ℝ) (hd : 0 < d) : ∀ᶠ n in atTop,
      (∀ v, Tq ≤ v →
        ‖massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) v -
          massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v -
          packetCumulative ψ ((B.outerRate * v - t n) / L n) • (E • Γ)‖ < d) ∧
      ‖Mh n - Mh 0 - E • Γ‖ < d := by
    filter_upwards [hcurve d hd, Metric.tendsto_nhds.1 hterminal d hd] with n hn hnh
    exact ⟨fun v hv => hn v ((le_max_right _ _).trans hv), by simpa only [dist_eq_norm] using hnh⟩
  have hquantile := mass_quantile_asymptotics hiψ hMψ hbound hpos hsupp
    B.outerRate_pos hL hpositive hfirst herrors
  exact ⟨Mh, hMh, hfixed, hterminal, hpositive, Tq,
    hT.trans (le_max_left _ _), hfirst, hquantile, herrors⟩

theorem exists_late_packet_mass_response (B : Background) {s l H Hlo : ℝ} {h : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    (hcrit : B.innerRate = (1 - 1 / p.toReal) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hc : ContinuousOn h (Ici 0)) (hb : ∀ v ∈ Ici (0 : ℝ), ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop)
    (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ D : AdmissibleOutgoingData B s l,
      (∀ v ∈ Ici (0 : ℝ), D.tail v = h (v + T)) ∧
      D.upper = H * Real.exp (-s * T) ∧ D.lower = Hlo * Real.exp (-l * T) ∧
      B.PacketMassResponse D hp ψ E t L ℓ Ucap := by
  obtain ⟨T, hT, D, heq, hupper, hlower⟩ :=
    B.exists_admissible_late_data (B.innerRate_pos.trans hks) hH hHlo hc hb hlo
  refine ⟨T, hT, D, heq, hupper, hlower, ?_⟩
  exact B.exists_packet_mass_response hp hpfin hcrit hks hl D.upper_nonneg D.lower_pos
    D.deviation_nonneg D.deviation_lt D.tail_continuous D.tail_bound D.tail_lower
    D.radius_continuous D.radius_lower D.radius_initial D.radius_derivative D.radius_decay
    hψ hcomp hpos hsupp hE t L hL htop hLtop ℓ Ucap hUcap

end CauchyHorizon.Background
