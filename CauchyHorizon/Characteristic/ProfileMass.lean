import CauchyHorizon.Characteristic.CriticalLate
import CauchyHorizon.Analysis.PacketData
import CauchyHorizon.Reduced.OpticalBoundary
import CauchyHorizon.Reduced.RegularTime
import CauchyHorizon.Reduced.RegularRadius
import CauchyHorizon.Reduced.RegularScalar
import CauchyHorizon.Characteristic.TransverseScalarBoundary
import CauchyHorizon.Characteristic.ConformalBoundary
import CauchyHorizon.Reduced.TransverseConformalBoundary
import CauchyHorizon.Reduced.LocalWeakExtension
import CauchyHorizon.Reduced.RegularEvolution
import CauchyHorizon.Reduced.CompactifiedGeometry
import CauchyHorizon.Characteristic.IncomingConvergence
import CauchyHorizon.Characteristic.UniformMassBound

/-! One nonlinear family carries the mass law and weak extensions for all admissible profiles. -/

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology ENNReal ContDiff

namespace CauchyHorizon.Background

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 4096 in
theorem exists_profile_mass_response (B : Background) {s l H Hlo dH : ℝ} {h r : ℝ → ℝ}
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
    {A Apt E : ℝ} (hA : 0 ≤ A) (hApt : 0 ≤ Apt) (hE : 0 ≤ E)
    (P Q : ℕ → ℝ →ᵇ ℝ) (hP0 : P 0 = 0)
    (hd : ∀ n x, HasDerivAt (P n) (Q n x) x) (hPC : ∀ n, ContDiff ℝ 1 (P n))
    (hPi : ∀ n, Integrable (fun x => P n x ^ 2) ∧ (∫ x, P n x ^ 2) ≤ E)
    (hQi : ∀ n, Integrable (fun x => Q n x ^ 2))
    (hQlim : Tendsto (fun n => ∫ x, Q n x ^ 2) atTop (𝓝 0))
    (m : ℕ → ℝ) (ℓ : ℝ) (hsuppP : ∀ n x, x ≤ m n → P n x = 0)
    (hfront : Tendsto (fun n => m n - ℓ) atTop atTop)
    (hdata : ∀ δ : ℝ,
      (∀ n, MemLp (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p (volume.restrict (Icc 0 δ))) ∧
      (∀ n, (eLpNorm (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p
        (volume.restrict (Icc 0 δ))).toReal ≤ A) ∧
      (∀ n, ∀ᵐ u ∂volume.restrict (Icc 0 δ),
        |logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n) u| ≤ Apt * u ^ (-1 / p.toReal)) ∧
      Tendsto (fun n => (eLpNorm (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p
        (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0))
    (Ucap : ℝ) (hUcap : 0 < Ucap) :
    let hi := horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb
    let hr0 := fun v => ((sub_pos.2 hdHR).trans_le (hrb v)).ne'
    let cν := Real.exp (∫ v in Ioi 0,
      2 * horizonK (r v) (horizonMass B.mass h v) B.charge B.cosmological - B.outerRate)
    let Ch := r 0 / (B.event * cν ^ B.criticalExponent)
    ∃ U : ℝ, ∃ hU : 0 < U, ∃ hUR : U < r 0, U ≤ Ucap ∧
        ∃ hf : ∀ n, MemLp (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p
            (volume.restrict (Icc 0 U)),
        ∃ hm : B.criticalExponent < 1,
        ∃ X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V,
          (∀ n (V : Ici (0 : ℝ)), IsWaveIntegral hU.le V.property B.charge B.cosmological
            (incomingWaveCurve hU.le hUR hp (hf n) (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp (hf n)) (X n V)) ∧
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
            let F := radiationComparisonRow hε.le B.innerRate (B.transmission hm * Ch)
              X (fun n v => P n (B.outerRate * v + ℓ))
            ((∀ n, MemLp (F n) 2 (volume.restrict (Ici 0))) ∧
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
              (∀ v, 0 ≤ v → Tendsto
                (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) v)
                atTop (𝓝 (massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v))) ∧
              ∃ Z : C(Icc ε U, WaveVector), ∃ Nh Γ : C(Icc ε U, ℝ),
                Tendsto (renormalizedWaveRow hε.le B.innerRate (X 0)) atTop (𝓝 Z) ∧
                Tendsto (scalarBoundaryRow hε.le (ν 0)) atTop (𝓝 Nh) ∧
                (∀ u, 0 < Z u 0 ∧ 0 < waveAmplitude Z u ∧ Nh u < 0 ∧
                  Γ u = (-2 * Nh u / (B.outerRate * waveAmplitude Z u)) *
                    (B.transmission hm * Ch) ^ 2 ∧ 0 < Γ u) ∧
                MassProfileLimit (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n))
                  Γ B.outerRate (fun _ => ℓ) (fun n => P n) := by
  have hs : 0 < s := B.innerRate_pos.trans hks
  have hrend : Tendsto r atTop (𝓝 B.event) := by
    have he : Tendsto (fun v : ℝ => Real.exp (-(2 * s) * v)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith only [hs]))
    have hh : Tendsto (fun v => r v - B.event) atTop (𝓝 0) :=
      squeeze_zero_norm' ((eventually_ge_atTop (0 : ℝ)).mono (fun v hv => hrdec v hv))
        (by simpa only [mul_zero] using he.const_mul dH)
    simpa only [sub_add_cancel, zero_add] using hh.add_const B.event
  have hOut := B.outgoing_estimates_of_radius hs hH hdH hdHR hc hb
    (fun v hv => (mul_pos hHlo (Real.exp_pos _)).trans_le (hlo v hv)) hrc hrb hrd hrdec hrend
  obtain ⟨δ, U, Y, Yr, β, Lc, τ, j, D, cL, N, C, Hs, ηL, Ldec, ηO, Odec, ηE, Edec,
    Rmatch, Olo, Ohi, Tr, jr, Dr, ηr, Cr, E₀, E₁, F₀, F₁, Drlo, Drhi, Er₀, Er₁, Mbound, Ed, hcommon⟩ :=
    B.exists_critical_late_wave hp hpfin hcrit hks hl hH hHlo hdH hdHR hA hApt hE
      hc hb hlo hrc hrb hrinit hrd hrdec hOut (min Ucap 1) (lt_min hUcap (by norm_num))
  obtain ⟨_hδ, _hY, hβ, _hβsmall, _hLc, _hτ, _hj, _hD, _hcL, _hcLk, _htail,
    _hN, _hC, _hHs, _hNhalf, _hηL, _hLdec, _hηO, _hOdec, _hηE, _hEdec,
    _hRmatch, hOlo, _hOhi, _hYr, _hYrY, _hTr, _hjr, _hDr, _hηr, _hCr,
    _hE₀, _hE₁, _hF₀, _hF₁, _hDrlo, _hDrhi, _hEr₀, _hEr₁, hMbound, _hEd,
    _hsmall, hcap, hU, hUδ, hUR, Laux, _hLaux, Taux, _hTaux, Saux, _hSaux,
    Tmatch, _hTmatch, hm, hfamily⟩ := hcommon
  have hU1 : U ≤ 1 := hcap.trans (min_le_right _ _)
  have hcap : U ≤ Ucap := hcap.trans (min_le_left _ _)
  let f := fun n => logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)
  have hf := (hdata δ).1
  let hfU := fun n => (hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hUδ) le_rfl)
  obtain ⟨arrival, X, harrival, _hscale, hX, hfloor, _hsection, _haux, hprofiles,
    _hgamma, _hscalar, _hlate, _hlambda, _hradial, _hlapse, _hexact, _htails, hcorner,
    hboundary, htransverse, hcompat, hfinite⟩ :=
    hfamily f hf (hdata δ).2.1 (hdata δ).2.2.1
  have hf0 : f 0 = 0 := by
    ext u
    dsimp only [f]
    rw [hP0]
    exact mul_zero _
  have hInitial := incoming_data_convergence hU.le hU1 hUR hp f hfU hf0
    (hdata U).2.2.2 (horizonPhi h r 0)
  obtain ⟨g, _hg, _hcharts, hslow, _hrows, hradiation, _hlateRadiation, hmassBound⟩ :=
    hprofiles (fun _ => ℓ) P (fun _ => rfl) (fun n => (hPi n).1) (fun n => (hPi n).2)
  obtain ⟨hrM, hMass⟩ := hmassBound
  have hbounded : HasUniformMassBound B.charge B.cosmological
      (fun n => incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) X :=
    ⟨Mbound, hMbound, fun _hr n V u v => hMass n V u v⟩
  have hresponse := hslow m Q hP0 hd hQi hQlim hfront hsuppP (hdata δ).2.2.2
  obtain ⟨Tg, hTg, _Zg, _hZg, _hZerr, _hRg, _hAg,
    AloG, AhiG, hAloG, hAhiG, _hAlimitsG, hampG, _hrestG⟩ := hboundary U hU le_rfl
  have hlapse (n : ℕ) := anchoring_lapse_data hU.le B.innerRate_pos hTg (X n) (hcompat n)
    (fun v hv => hampG n v hv ⟨U, le_rfl, le_rfl⟩)
  choose χ hχ using fun n => exists_regular_time_coordinate (hlapse n).1
    (hlapse n).2.1 (hlapse n).2.2.1 (0 : ℝ)
  have hχtop (n : ℕ) : Tendsto (χ n) (𝓝[<] (0 : ℝ)) atTop := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hh, _, _⟩ := hχ n
    exact hh
  obtain ⟨hrS, _hνlate, hνlimits, hζlimits, _hboundaryConstraint⟩ := htransverse
  refine ⟨U, hU, hUR, hcap, hfU, hm, X, hX, hfloor, hcompat,
    hfinite hf0 (hdata δ).2.2.2, hInitial, hbounded, χ, hχ, ?_⟩
  intro ε hε hεU
  have : Nonempty (Icc ε U) := ⟨⟨U, hεU, le_rfl⟩⟩
  obtain ⟨Tb, hTb, Zb, hZb, _hZberr, hRb, _hAb,
    Alo, Ahi, hAlo, hAhi, hAlimits, hamp, _hAtop, _hAtail, hZseq⟩ := hboundary ε hε hεU
  have hρ : 0 < 3 * B.inner / 4 := by have := B.inner_pos; positivity
  have hscalar (n : ℕ) := regular_scalar_energy hε.le hεU hρ hAloG hTg (X n) (hcompat n)
    (fun V v hv => (hX n V).longitudinal_section_derivative hv) (hχ n) (hfloor n)
    (fun t ht => ((hlapse n).2.2.2.2 t ht).1) (hradiation n).2.1
  obtain ⟨Tζ, Cζ, _hTζ, _hCζ, Zζ, hZζ, _hZζtail, _hZζseq⟩ := hζlimits ε hε hεU
  have htransverseScalar (n : ℕ) : ∃ Dφ : ℝ → C(Icc ε U, ℝ), ∃ Dhφ : C(Icc ε U, ℝ),
      IsTransverseScalarTrace hU.le (X n) (χ n) Dφ Dhφ := by
    obtain ⟨Dφ, Dhφ, hh, _htraceFormula, _hfiniteFormula⟩ :=
      incoming_transverse_scalar_boundary hU.le hε hUR hp (hfU n)
        (logarithmicIncoming_contDiff (hPC n) (1 - 1 / p.toReal) ℓ).continuousOn
        _ (X n) (hX n) (hcompat n) (hrS n) (Zb n) (Zζ n) (hZb n) (hZζ n)
        (fun u => (hρ.trans_le (hRb n u)).ne') (hχtop n)
    exact ⟨Dφ, Dhφ, hh⟩
  choose Dφ Dhφ hDφ using htransverseScalar
  have hflux (n : ℕ) (V : Ici (0 : ℝ)) := (hX n V).outgoing_integral_constraint
        hU.le V.property hUR hc (horizon_mass_integrable hs hH hc hb) hrc
        (fun v => ((sub_pos.2 hdHR).trans_le (hrb v)).ne')
        (horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb) hrd hp (hfU n)
  choose Dh hDh hDtail hDmono using fun n =>
    exists_optical_boundary_limit hε.le hρ hAlo hTb (X n) (hcompat n) (hfloor n)
      (fun v hv u => (hamp n v hv u).1) (hradiation n).2.1 (hflux n)
  obtain ⟨Tν, Cw, Cν, _hTν, _hCw, _hCν, Zw, Zν, _hZw, _hZwTail,
    hZν, _hZνTail, _hZνSign, hZνSeq, _hνCoeff⟩ := hνlimits ε hε hεU
  have hconformal (n : ℕ) :
      (∃ Tc Cc : ℝ, 0 ≤ Tc ∧ 0 < Cc ∧
        IsRegularConformalEnergy hε.le hεU B.innerRate (X n) (χ n) Tc Cc) ∧
      (ε < U → ∃ Dℓ : ℝ → C(Icc ε U, ℝ), ∃ Dhℓ : C(Icc ε U, ℝ),
        IsTransverseConformalTrace hU.le (X n) (χ n) Dℓ Dhℓ) := by
    have hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp (hfU n) u 0 = -1 := by
      filter_upwards [incomingWaveVelocity_ae hUR hp (hfU n)] with u hu
      rw [hu]
      rfl
    obtain ⟨Tc, Cc, hTc, hCc, hdiff⟩ := conformal_difference_of_traces hU hε hεU hρ hAhiG.le
      _ _ _ (X n) (hX n) rfl hinu (hcompat n) (hrS n) (hfloor n)
      (Zb n) (Zν n) (Dh n) (hZb n) (hZν n) (hDh n)
      (fun u => (hρ.trans_le (hRb n u)).ne') (hDφ n)
      (fun t ht => ((hlapse n).2.2.2.2 t ht).2)
    constructor
    · refine ⟨Tc, 2 * Cc ^ 2 / AloG, hTg.trans hTc, by positivity, ?_⟩
      exact regular_conformal_energy hε.le hεU B.innerRate_pos hAloG hCc.le (hTg.trans hTc)
        (X n) (hcompat n) (fun V v hv => (hX n V).longitudinal_section_derivative hv) (hχ n)
        (fun t ht => ((hlapse n).2.2.2.2 t (hTc.trans ht)).1)
        (fun t ht ht₀ => (hdiff t ht ht₀).2) (hradiation n).2.1
    · intro hεlt
      let G := fun t => 2 * Cc * (‖compactRadiationRow hε.le B.innerRate (X n) t‖ ^ 2 +
        Real.exp (-(2 * B.innerRate) * t))
      have hRadc : Continuous (compactRadiationRow hε.le B.innerRate (X n)) :=
        (compactRadiationRestriction hε.le).continuous.comp (continuous_radiationRow (X n) (hcompat n))
      have hGc : Continuous G := by dsimp only [G]; fun_prop
      have hi := (compactRadiationRestriction hε.le).comp_memLp' (hradiation n).2.1
      have hiRad : IntegrableOn (fun t => ‖compactRadiationRow hε.le B.innerRate (X n) t‖ ^ 2) (Ici 0) :=
        (memLp_two_iff_integrable_sq_norm hi.1).1 hi
      have hiExp : IntegrableOn (fun t => Real.exp (-(2 * B.innerRate) * t)) (Ici 0) :=
        (integrableOn_Ici_iff_integrableOn_Ioi).2
          (integrableOn_exp_mul_Ioi (by have := B.innerRate_pos; linarith) 0)
      have hGi : IntegrableOn G (Ici 0) := (hiRad.add hiExp).const_mul (2 * Cc)
      have hGpos (t : ℝ) : 0 ≤ G t := by dsimp only [G]; positivity
      have hfc : ContinuousOn (incomingVelocity (r 0) (f n)) (Ioi 0) := by
        have hh := (logarithmicIncoming_contDiff (hPC n) (1 - 1 / p.toReal) ℓ).continuousOn
        change ContinuousOn (fun u => incomingVelocity (r 0)
          (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) u) (Ioi 0)
        unfold incomingVelocity
        fun_prop
      obtain ⟨Dℓ, Dhℓ, htrace, _htail⟩ := exists_transverse_conformal_boundary
        hε hεlt (hTg.trans hTc) _ _ _ (X n) (hX n) rfl hinu hfc
        (incomingWaveVelocity_ae hUR hp (hfU n)) (hcompat n) hGc hGi hGpos
        (fun t ht ht₀ => by
          filter_upwards [(hdiff t ht ht₀).1] with u hu
          intro hm
          apply (hu hm).trans
          let q := Real.exp (-B.innerRate * t)
          let z := ‖compactRadiationRow hε.le B.innerRate (X n) t‖
          have he : Real.exp (-(2 * B.innerRate) * t) = q ^ 2 := by
            rw [show -(2 * B.innerRate) * t = -B.innerRate * t + -B.innerRate * t by ring, Real.exp_add]
            simp only [q, pow_two]
          have hy : q * z + q ^ 2 ≤ 2 * (z ^ 2 + q ^ 2) := by
            nlinarith only [sq_nonneg (z - q), sq_nonneg z, sq_nonneg q]
          have hh := mul_le_mul_of_nonneg_left hy hCc.le
          dsimp only [G]
          rw [he]
          dsimp only [q, z] at hh
          nlinarith only [hh]) (hχtop n)
      exact ⟨Dℓ, Dhℓ, htrace⟩
  have hregularRadius (n : ℕ) := regular_radius_boundary hε.le hεU (X n) (hcompat n)
    (fun V v hv => (hX n V).longitudinal_section_derivative hv) (hχ n) (hZb n) (hDh n)
  have htransverseWave (hεlt : ε < U) (n : ℕ) :
      ∃ Du : ℝ → C(Icc ε U, WaveVector), ∃ Duh : C(Icc ε U, WaveVector),
        IsTransverseWaveBoundary hU.le hεU (X n) (χ n) (Zb n) Du Duh ∧
        IsRegularWaveBoundary hε.le hεU (X n) (χ n) (Zb n) Du Duh ∧
        IsRegularWaveEvolution hε.le hεU B.charge B.cosmological (X n) (χ n) (Zb n) Du Duh ∧
        ∃ Tw Cw : ℝ, 0 ≤ Tw ∧ 0 < Cw ∧
          IsRegularWaveEnergy hε.le hεU B.innerRate (X n) (χ n) (Zb n) Tw Cw ∧
          HasBoundedRegularContinuationData hε.le hεU (X n) (χ n) (Zb n) (Dh n)
            Du Duh (3 * B.inner / 4) Tw ∧
          ∀ u₀ ∈ Ioo ε U, HasRegularCrossingSolution hε.le hεU B.charge B.cosmological
            (X n) (χ n) (Zb n) (Dh n) Du Duh Tw u₀ ∧
            HasLocalSphericalWeakExtension hε.le hεU B.charge B.cosmological (X n) (χ n) Tw u₀ := by
    obtain ⟨Dℓ, Dhℓ, hDℓ⟩ := (hconformal n).2 hεlt
    have hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp (hfU n) u 0 = -1 := by
      filter_upwards [incomingWaveVelocity_ae hUR hp (hfU n)] with u hu
      rw [hu]
      rfl
    let N := fun T => radialNuField T.property B.charge B.cosmological
      (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hrS n T)
    have hNc (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v :
        N S u v = N T u ⟨v, v.property.1, v.property.2.trans hST⟩ := by
      apply radialNuField_prefix_eq S.property T.property hST B.charge B.cosmological
        _ _ _ (hrS n T) (hrS n S) ?_ u v
      intro w v
      have he := congrArg (fun x : WaveState U (S : ℝ) => x.1 w v) (hcompat n S T hST)
      change (X n T).1 ⟨0 + (w : ℝ), by simpa using w.property.1, by simpa using w.property.2⟩
        ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X n S).1 w v at he
      simpa only [zero_add] using he.symm
    let A : C(C(Icc ε U, ℝ) × C(Icc ε U, ℝ) × C(Icc ε U, ℝ), C(Icc ε U, WaveVector)) :=
      (⟨fun q => ![q.1.1 q.2, q.1.2.1 q.2, q.1.2.2 q.2], by fun_prop⟩ :
        C((C(Icc ε U, ℝ) × C(Icc ε U, ℝ) × C(Icc ε U, ℝ)) × Icc ε U, WaveVector)).curry
    let Du := fun t => A (scalarBoundaryRow hε.le N t, Dφ n t, Dℓ t)
    let Duh := A (Zν n, Dhφ n, Dhℓ)
    have hlim : Tendsto Du atTop (𝓝 Duh) :=
      (A.continuous.tendsto _).comp ((hZν n).prodMk_nhds ((hDφ n).2.1.prodMk_nhds hDℓ.2.1))
    have hdu (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U) :
        HasDerivWithinAt (fun x => intervalExtension hU.le (X n T).1 x ⟨t, ht, htT⟩)
          (Du t u) (Icc 0 U) u := by
      apply hasDerivWithinAt_pi.2
      intro i
      fin_cases i
      · change HasDerivWithinAt _ (scalarBoundaryRow hε.le N t u) _ _
        rw [scalarBoundaryRow_apply hε.le N hNc T ht htT u]
        exact (hX n T).radial_hasDerivWithinAt (hrS n T) rfl hinu ⟨t, ht, htT⟩
          ⟨hε.le.trans u.property.1, u.property.2⟩
      · exact (hDφ n).1 T t ht htT u
      · exact hDℓ.1 T t ht htT u
    have hB : IsTransverseWaveBoundary hU.le hεU (X n) (χ n) (Zb n) Du Duh :=
      ⟨hdu, hlim, hlim.comp (hχtop n),
      renormalized_boundary_hasDerivWithinAt hε.le hεU (X n) (hcompat n) (hZb n) hlim
        (fun t ht => hdu ⟨t, ht⟩ t ht le_rfl)⟩
    have hfc : ContinuousOn (incomingVelocity (r 0) (f n)) (Ioi 0) := by
      have hh := (logarithmicIncoming_contDiff (hPC n) (1 - 1 / p.toReal) ℓ).continuousOn
      change ContinuousOn (fun u => incomingVelocity (r 0)
        (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) u) (Ioi 0)
      unfold incomingVelocity
      fun_prop
    have hDc := hB.continuousOn hU hε _ _ _ (X n) (hX n) rfl hinu hfc
      (incomingWaveVelocity_ae hUR hp (hfU n))
    have hregular := regular_wave_boundary hε.le hεU (X n) (hcompat n)
      (fun V v hv => (hX n V).longitudinal_section_derivative hv) (hχ n) (hZb n) hB hDc
    obtain ⟨Tc, Cc, _hTc, hCc, hEc⟩ := (hconformal n).1
    have hvc := (regular_wave_derivative hε.le hεU (X n) (hcompat n)
      (fun V v hv => (hX n V).longitudinal_section_derivative hv) (hχ n)).2.2
    have hevolution := regular_wave_evolution hU hε hεU _ _ _ (X n) (hX n) rfl hinu hfc
      (incomingWaveVelocity_ae hUR hp (hfU n)) (hcompat n) (hχ n) hB hregular
    have hconstraint := regular_spatial_constraint hU hε.le hεU _ _ _ (X n) (hX n) rfl hinu
      (incomingWave_constraint_data hU.le hUR hp (hfU n) (horizonPhi h r 0)).2
      (hχ n) hB hregular
    refine ⟨Du, Duh, hB, hregular, hevolution, ?_⟩
    obtain ⟨Tw, Cw, hTw, hCw, hEw⟩ := regular_wave_energy (Cs := 1 / ((3 * B.inner / 4) ^ 2 * AloG)) hε.le hεU
      B.innerRate_pos hAhiG hTg (by positivity) hCc.le (X n) (hχ n) hvc hregular (hregularRadius n)
      (fun t ht => ((hlapse n).2.2.2.2 t ht).2) (hscalar n) hEc (hradiation n).2.1
    have hdata := regular_wave_continuation_data hε.le hεU hρ (X n) (Dh n)
      (hχ n) hregular hEw (hfloor n) (hRb n)
    have hoptical := regular_optical_constraint hε.le hεU (X n) (hcompat n)
      (fun V v hv => (hX n V).longitudinal_section_derivative hv) (hχ n) hregular (hDh n) (hflux n)
    have hbounded := bounded_regular_continuation_data hε.le hεU (X n) (Dh n) (hχ n)
      hregular hoptical hEw hdata
    refine ⟨Tw, Cw, hTw, hCw, hEw, hbounded, ?_⟩
    intro u₀ hu₀
    have hcross := exists_regular_crossing_solution hε.le hεU B.charge B.cosmological hρ (X n) (Dh n)
      (hχ n) hregular hevolution hconstraint hvc (fun T u v => hρ.trans_le (hfloor n T u v)) hbounded hu₀
    exact ⟨hcross, hcross.local_weak_extension (hcompat n)
      (fun S u v => hρ.trans_le (hfloor n S u v)) (hχ n) hregular⟩
  have hDlower (n : ℕ) (u : Icc ε U) : Olo * ε ≤ Dh n u := by
    let w : Icc 0 U := ⟨u, hε.le.trans u.property.1, u.property.2⟩
    have hu : 0 < (w : ℝ) := hε.trans_le u.property.1
    have ha : 0 < arrival n w := (harrival n).2.2.2 w ⟨hu, w.property.2⟩
    let V : Ici (0 : ℝ) := ⟨(1 + β) * arrival n w, by
      change 0 ≤ (1 + β) * arrival n w
      positivity⟩
    have haV : arrival n w ≤ V := by
      change arrival n w ≤ (1 + β) * arrival n w
      nlinarith only [mul_nonneg hβ.le ha.le]
    obtain ⟨_h0, _h1, _h2, _h3, _h4, hentry, _hmore⟩ :=
      hcorner n V w hu ⟨V, V.property, le_rfl⟩ le_rfl
    rw [projIcc_of_mem V.property (show arrival n w ∈ Icc 0 (V : ℝ) from ⟨ha.le, haV⟩)] at hentry
    have hh := hDmono n (arrival n w) ha.le u
    rw [opticalRow_apply hε.le (X n) (hcompat n) V ha.le haV u] at hh
    exact (mul_le_mul_of_nonneg_left u.property.1 hOlo.le).trans (hentry.trans hh)
  have hnormalized (n : ℕ) :=
    (lapse_normalized_radial_limit hε.le hεU (X n) (hcompat n) (hZb n) (hDh n)).2
  have hnormalizedNeg (n : ℕ) (u : Icc ε U) :
      (-(anchoredAmplitude ⟨U, hεU, le_rfl⟩ (Zb n)) * Dh n) u < 0 := by
    change -(Real.exp (-Zb n ⟨U, hεU, le_rfl⟩ 2) * Real.exp (Zb n u 2)) * Dh n u < 0
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)))
      ((mul_pos hOlo hε).trans_le (hDlower n u))
  obtain ⟨hF, hr, _hdensity, _hresponse, hprofile⟩ := hresponse.2.2 ε hε hεU
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
  have hcompact : HasCompactifiedGeometry hε.le B.innerRate X ν :=
    compactified_geometry hε.le hTb hρ hAlo hAhi X ν hcompat hνcompat Zb Zν hZb hZν
      (hZseq hf0 (hdata δ).2.2.2).1 (hZseq hf0 (hdata δ).2.2.2).2.1
      (hZνSeq hf0 (hdata δ).2.2.2).2.2.1 (hZνSeq hf0 (hdata δ).2.2.2).2.2.2
      hfloor hRb hamp hAlimits
  have hνfinite (V : Ici (0 : ℝ)) : Tendsto (fun n => ν n V) atTop (𝓝 (ν 0 V)) :=
    (IsWaveIntegral.radial_tendsto (fun n => hX n V) (hX 0 V)
      (fun n => hr n V) (hr 0 V) (hfinite hf0 (hdata δ).2.2.2 V).fst_nhds).1
  have hmassFinite := (mass_rows (k := B.innerRate) hε.le X ν hr hcompat hνcompat
    (fun n V u v => (hX n V).outgoing_mass_integral hU.le V.property hUR hc
      (horizon_mass_integrable hs hH hc hb) hrc
      (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
      (horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb)
      hrd hp (hfU n) u v) (hfinite hf0 (hdata δ).2.2.2) hνfinite).2
  obtain ⟨Z, Nh, Γ, hZ, hNh, hsign, hmass⟩ := hprofile
  exact ⟨hF, ⟨Tb, 1 / ((3 * B.inner / 4) * Alo), Olo * ε, hTb,
    by positivity, mul_pos hOlo hε, Dh, Zb, hZb, hDh, hDtail, hDlower, hDmono,
    hnormalized, (fun n => (hnormalized n).comp (hχtop n)), hnormalizedNeg,
    hregularRadius,
    htransverseWave⟩,
    ⟨Tg, 1 / ((3 * B.inner / 4) ^ 2 * AloG), hTg, by positivity, hscalar⟩,
    ⟨Dφ, Dhφ, hDφ⟩, (fun n => (hconformal n).1), (fun hεlt n => (hconformal n).2 hεlt),
    hr, hcompact, hmassFinite, Z, Nh, Γ, hZ, hNh, hsign, hmass⟩

end CauchyHorizon.Background
