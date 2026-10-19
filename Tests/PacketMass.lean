import CauchyHorizon.Characteristic.PacketMass
import CauchyHorizon.Analysis.IntervalRebase
import CauchyHorizon.Reduced.WaveCovariance
import CauchyHorizon.Reduced.ClassicalIntegral

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology ENNReal ContDiff

namespace CauchyHorizon.Tests

-- At p=4 the original physical family has different zero and nonzero mass limit orders, even at u=U.
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
example (B : Background) {s l H Hlo dH : ℝ} {h r : ℝ → ℝ}
    (hcrit : B.innerRate = (3 / 4) * B.outerRate)
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
    let hi := horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb
    let hr0 := fun v => ((sub_pos.2 hdHR).trans_le (hrb v)).ne'
    let cν := Real.exp (∫ v in Ioi 0,
      2 * horizonK (r v) (horizonMass B.mass h v) B.charge B.cosmological - B.outerRate)
    let Ch := r 0 / (B.event * cν ^ B.criticalExponent)
    ∃ U : ℝ, ∃ hU : 0 < U, ∃ hUR : U < r 0, U ≤ Ucap ∧
      ∃ P : ℕ → ℝ →ᵇ ℝ, P 0 = 0 ∧
      (∀ n, n ≠ 0 → ∀ x, P n x = Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) *
        ψ ((x - t n) / L n)) ∧
      (∀ U₀ : ℝ, 0 < U₀ →
        Tendsto (fun n => primitiveEnergy (1 - 1 / (4 : ℝ≥0∞).toReal)
          (logarithmicIncoming (1 - 1 / (4 : ℝ≥0∞).toReal) ℓ (P n)) U₀) atTop (𝓝 E)) ∧
      ∃ hf : ∀ n, MemLp (logarithmicIncoming (1 - 1 / (4 : ℝ≥0∞).toReal) ℓ (P n)) 4
          (volume.restrict (Icc 0 U)),
      ∃ X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V,
        (∀ n (V : Ici (0 : ℝ)), IsWaveIntegral hU.le V.property B.charge B.cosmological
          (incomingWaveCurve hU.le hUR le_rfl (hf n) (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_rfl (hf n)) (X n V)) ∧
        (∀ n (V : Ici (0 : ℝ)), HasContinuousFirstOrderEquations hU.le V.property B.charge B.cosmological
          (incomingWaveCurve hU.le hUR le_rfl (hf n) (horizonPhi h r 0)) (X n V)) ∧
        (∀ n (V : Ici (0 : ℝ)), HasOpticalFluxEquations V.property B.charge B.cosmological
          (incomingWaveCurve hU.le hUR le_rfl (hf n) (horizonPhi h r 0)) (X n V)) ∧
        (∀ n (V : Ici (0 : ℝ)), HasContinuousWaveSystem hU.le V.property B.charge B.cosmological
          (incomingWaveCurve hU.le hUR le_rfl (hf n) (horizonPhi h r 0)) (X n V)) ∧
        HasConvergentIncomingData hU.le hUR le_rfl
          (fun n => logarithmicIncoming (1 - 1 / (4 : ℝ≥0∞).toReal) ℓ (P n)) hf (horizonPhi h r 0) ∧
        HasUniformMassBound B.charge B.cosmological
          (fun n => incomingWaveCurve hU.le hUR le_rfl (hf n) (horizonPhi h r 0)) X ∧
        ∃ hm : B.criticalExponent < 1,
        (∀ ε (hε : 0 < ε) (_hεU : ε ≤ U) (d : ℝ),
          let F := radiationComparisonRow hε.le B.innerRate (B.transmission hm * Ch)
            X (fun n v => P n (B.outerRate * v + d))
          (∀ n, MemLp (F n) 2 (volume.restrict (Ici 0))) ∧
            Tendsto (fun n => ∫ v in Ici (0 : ℝ), ‖F n v‖ ^ 2) atTop (𝓝 0)) ∧
        ∃ χ : ℕ → ℝ → ℝ,
        (∀ n, IsRegularTimeCoordinate (anchoringLapse hU.le (X n)) 0 (χ n)) ∧
        (∃ Dh Rv Rh : ℕ → C(Icc U U, ℝ),
          (∀ n, Tendsto (opticalRow hU.le (X n)) atTop (𝓝 (Dh n))) ∧
          (∀ n, Tendsto (lapseNormalizedRadialRow hU.le le_rfl B.innerRate (X n)) atTop (𝓝 (Rv n))) ∧
          (∀ n, Tendsto (fun w => lapseNormalizedRadialRow hU.le le_rfl B.innerRate (X n) (χ n w))
            (𝓝[<] (0 : ℝ)) (𝓝 (Rv n))) ∧
          (∀ n u, 0 < Dh n u ∧ Rv n u < 0) ∧
          ∀ n, let R := compactifiedRadiusRow hU.le (X n) (χ n) (Rh n)
            HasDerivWithinAt R (Rv n) (Iic 0) 0 ∧
            Tendsto (deriv R) (𝓝[<] (0 : ℝ)) (𝓝 (Rv n)) ∧
            ∀ (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (u : Icc U U),
              R (regularTime (anchoringLapse hU.le (X n)) t) u =
                (X n T).1 ⟨u, hU.le.trans u.property.1, u.property.2⟩ ⟨t, ht.le, htT⟩ 0) ∧
        (∃ Ts Cs : ℝ, 0 ≤ Ts ∧ 0 < Cs ∧
          ∀ n, IsRegularScalarEnergy hU.le le_rfl B.innerRate (X n) (χ n) Ts Cs) ∧
        (∃ Dφ : ℕ → ℝ → C(Icc U U, ℝ), ∃ Dhφ : ℕ → C(Icc U U, ℝ),
          ∀ n, IsTransverseScalarTrace hU.le (X n) (χ n) (Dφ n) (Dhφ n)) ∧
        (∀ n, ∃ Tc Cc : ℝ, 0 ≤ Tc ∧ 0 < Cc ∧
          IsRegularConformalEnergy (half_pos hU).le (half_le_self hU.le) B.innerRate (X n) (χ n) Tc Cc) ∧
        (∀ n, ∃ Dℓ : ℝ → C(Icc (U / 2) U, ℝ), ∃ Dhℓ : C(Icc (U / 2) U, ℝ),
          IsTransverseConformalTrace hU.le (X n) (χ n) Dℓ Dhℓ) ∧
        (∃ Zh : ℕ → C(Icc (U / 2) U, WaveVector), ∃ Oh : ℕ → C(Icc (U / 2) U, ℝ), ∀ n,
          Tendsto (renormalizedWaveRow (half_pos hU).le B.innerRate (X n)) atTop (𝓝 (Zh n)) ∧
          ∃ Du : ℝ → C(Icc (U / 2) U, WaveVector), ∃ Duh : C(Icc (U / 2) U, WaveVector),
            IsTransverseWaveBoundary hU.le (half_le_self hU.le) (X n) (χ n) (Zh n) Du Duh ∧
            IsRegularWaveBoundary (half_pos hU).le (half_le_self hU.le) (X n) (χ n) (Zh n) Du Duh ∧
            IsRegularWaveEvolution (half_pos hU).le (half_le_self hU.le) B.charge B.cosmological
              (X n) (χ n) (Zh n) Du Duh ∧
            ∃ Tw Cw : ℝ, 0 ≤ Tw ∧ 0 < Cw ∧ IsRegularWaveEnergy (half_pos hU).le
              (half_le_self hU.le) B.innerRate (X n) (χ n) (Zh n) Tw Cw ∧
              HasBoundedRegularContinuationData (half_pos hU).le (half_le_self hU.le) (X n) (χ n)
                (Zh n) (Oh n) Du Duh (3 * B.inner / 4) Tw ∧
              ∀ u₀ ∈ Ioo (U / 2) U, HasRegularCrossingSolution (half_pos hU).le (half_le_self hU.le)
                B.charge B.cosmological (X n) (χ n) (Zh n) (Oh n) Du Duh Tw u₀ ∧
                HasLocalSphericalWeakExtension (half_pos hU).le (half_le_self hU.le)
                  B.charge B.cosmological (X n) (χ n) Tw u₀) ∧
        ∃ hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0,
          let ν := fun n (V : Ici (0 : ℝ)) => radialNuField V.property B.charge B.cosmological
            (incomingWaveCurve hU.le hUR le_rfl (hf n) (horizonPhi h r 0)) (X n V).1 (hr n V)
          HasCompactifiedGeometry hU.le B.innerRate X ν ∧
          ∃ Mh : ℕ → C(Icc U U, ℝ), ∃ Ah : C(Icc U U, ℝ),
            (∀ n, Tendsto (massRow hU.le B.charge B.cosmological (X n) (ν n) (hr n))
              atTop (𝓝 (Mh n))) ∧
            (∃ C : ℝ, 0 ≤ C ∧
              (∀ n t, ‖massRow hU.le B.charge B.cosmological (X n) (ν n) (hr n) t‖ ≤ C) ∧
              ∀ n, ‖Mh n‖ ≤ C) ∧
            (∀ v, 0 ≤ v →
              Tendsto (fun n => massRow hU.le B.charge B.cosmological (X n) (ν n) (hr n) v -
                massRow hU.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v) atTop (𝓝 0)) ∧
            Tendsto (fun n => Mh n - Mh 0) atTop (𝓝 Ah) ∧ Ah ≠ 0 ∧
            ∃ T : ℝ, 0 ≤ T ∧
              HasMassFirstCrossings
                (fun n => massRow hU.le B.charge B.cosmological (X n) (ν n) (hr n)) Mh T ∧
              HasMassQuantileAsymptotics ψ B.outerRate t L
                (fun n => massRow hU.le B.charge B.cosmological (X n) (ν n) (hr n)) Mh T ∧
              ∀ d > (0 : ℝ), ∀ᶠ n in atTop,
              (∀ v, T ≤ v →
                ‖massRow hU.le B.charge B.cosmological (X n) (ν n) (hr n) v -
                  massRow hU.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v -
                  packetCumulative ψ ((B.outerRate * v - t n) / L n) • Ah‖ < d) ∧
              ‖Mh n - Mh 0 - Ah‖ < d := by
  have hmain := B.exists_packet_mass_response (p := 4) le_rfl (by norm_num)
    (by norm_num; exact hcrit) hks hl hH hHlo hdH hdHR hc hb hlo hrc hrb hrinit hrd hrdec
    hψ hcomp hpos hsupp hE t L hL htop hLtop ℓ Ucap hUcap
  obtain ⟨P, hP0, hformula, hprimitive, U, hU, hUR, hcap, hf, hm, X, hX, hEquations, hFlux, hWave, _hfloor, _hcompat, _hfinite,
    hInitial, hbounded, χ, hχ, hresponse⟩ := hmain
  have hhalf := (hresponse (U / 2) (half_pos hU) (half_le_self hU.le)).2.2.2.2.1
  have hhalfTrace := (hresponse (U / 2) (half_pos hU) (half_le_self hU.le)).2.2.2.2.2.1
    (half_lt_self hU)
  obtain ⟨_Tdh, _Cdh, _dh, _hTdh, _hCdh, _hdh, Oh, Zh, hZh, _hDhh, _htailh,
    _hloh, _hmonoh, _hRvh, _hRvχh, _hRvnegh, _hRboundh, hwave⟩ :=
    (hresponse (U / 2) (half_pos hU) (half_le_self hU.le)).2.1
  obtain ⟨_hF, hoptical, hscalar, htransverse, _hconformal, _hconformalTrace, hr, hcompact, Z, Nh, Γ, _hZ, _hNh, _hsign, _hmass, Mh, hMh, hfixed, hterminal, hpositive, Tcurve, hTcurve, hfirst, hquantile, hcurve⟩ :=
    hresponse U hU le_rfl
  obtain ⟨Td, Cd, d, _hTd, _hCd, hd, Dh, Zg, _hZg, hDh, _hDtail, hDlo, _hDmono,
    hRv, hRvχ, hRvneg, hRbound, _hwave⟩ := hoptical
  obtain ⟨C, hC, hrows⟩ := hbounded.rows_and_limits
  have hb := hrows U hU.le hr
  refine ⟨U, hU, hUR, hcap, P, hP0, hformula, (fun U₀ hU₀ => (hprimitive U₀ hU₀).2),
    hf, X, hX, hEquations, hFlux, hWave, hInitial, hbounded,
    hm, (fun ε hε hεU => (hresponse ε hε hεU).1), χ, hχ,
    ⟨Dh, (fun n => -(anchoredAmplitude ⟨U, le_rfl, le_rfl⟩ (Zg n)) * Dh n),
      (fun n => waveRadius (Zg n)), hDh, hRv, hRvχ,
      (fun n u => ⟨hd.trans_le (hDlo n u), hRvneg n u⟩),
      fun n => ⟨(hRbound n).2.2.2.1, (hRbound n).2.2.2.2.1, (hRbound n).1⟩⟩,
    hscalar, htransverse, hhalf, hhalfTrace, ⟨Zh, Oh, fun n => ⟨hZh n, hwave (half_lt_self hU) n⟩⟩,
    hr, hcompact, Mh, E • Γ, hMh, ⟨C, hC, hb.1, hb.2 Mh hMh⟩, hfixed,
    hterminal, ?_, Tcurve, hTcurve, hfirst, hquantile, hcurve⟩
  intro hz
  have hh := hpositive ⟨U, le_rfl, le_rfl⟩
  rw [hz] at hh
  simp at hh

-- At the anchoring ray the lapse-normalized radial quotient is exactly minus the optical flux.
example {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (k : ℝ)
    (X : (V : Ici (0 : ℝ)) → WaveState U V) (t : ℝ) :
    lapseNormalizedRadialRow hε hεU k X t ⟨U, hεU, le_rfl⟩ =
      -opticalRow hε X t ⟨U, hεU, le_rfl⟩ := by
  change -(Real.exp (-renormalizedWaveRow hε k X t ⟨U, hεU, le_rfl⟩ 2) *
    Real.exp (renormalizedWaveRow hε k X t ⟨U, hεU, le_rfl⟩ 2)) *
      opticalRow hε X t ⟨U, hεU, le_rfl⟩ = _
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _), neg_one_mul]

-- The exponential lapse fixes both the sign and the normalization of the regular coordinate.
example {k : ℝ} (hk : 0 < k) :
    ∃ χ : ℝ → ℝ, IsRegularTimeCoordinate (fun v => Real.exp (-(2 * k) * v)) 0 χ ∧
      ∀ v, regularTime (fun w => Real.exp (-(2 * k) * w)) v =
        -(Real.exp (-(2 * k) * v) / (2 * k)) := by
  have hk' : -(2 * k) < 0 := by linarith only [hk]
  obtain ⟨χ, hχ⟩ := exists_regular_time_coordinate (by fun_prop)
    (fun v => Real.exp_pos (-(2 * k) * v)) (fun v => integrableOn_exp_mul_Ioi hk' v) (0 : ℝ)
  refine ⟨χ, hχ, ?_⟩
  intro v
  rw [regularTime, integral_exp_mul_Ioi hk', neg_div_neg_eq]

-- The Banach-valued boundary derivative gives the physical derivative at every incoming point.
example {U ε k : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, ℝ))
    (hb : IsRegularRadiusBoundary hε hεU k X χ Z Dh) (u : Icc ε U) :
    HasDerivWithinAt (fun w => compactifiedRadiusRow hε X χ (waveRadius Z) w u)
      (-Real.exp (Z u 2 - Z ⟨U, hεU, le_rfl⟩ 2) * Dh u) (Iic 0) 0 := by
  have hd := (ContinuousMap.evalCLM ℝ u : C(Icc ε U, ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt
    (0 : ℝ) hb.2.2.2.1
  apply hd.congr_deriv
  change -(Real.exp (-Z ⟨U, hεU, le_rfl⟩ 2) * Real.exp (Z u 2)) * Dh u = _
  rw [sub_eq_add_neg, Real.exp_add]
  ring

-- Unit energy density measures the regular coordinate interval with the exact lapse Jacobian.
example {a χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate a 0 χ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ _w in Ioo (regularTime a T) 0, (1 : ℝ)) = ∫ t in Ioi T, a t := by
  simpa only [norm_one, one_pow, mul_one] using (hχ.energy_change hT (fun _ => (1 : ℝ))).2

-- The energy estimate controls the derivative of the actual reparameterized scalar field.
example {U ε k T₀ C T : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (hT₀ : 0 ≤ T₀) (hT : T₀ ≤ T)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hE : IsRegularScalarEnergy hε hεU k X χ T₀ C) :
    MemLp (deriv (fun w => waveScalar (renormalizedWaveRow hε 0 X (χ w)))) 2
      (volume.restrict (Ioo (regularTime (anchoringLapse (hε.trans hεU) X) T) 0)) := by
  apply MemLp.ae_eq ?_ ((hE.2.1 T hT).1)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
  exact (hE.1 w ⟨(hχ.2.2.2.1.monotone (hT₀.trans hT)).trans_lt hw.1, hw.2⟩).deriv.symm

-- The compact derivative keeps arbitrary incoming data, including its exact value at v=0.
example {U ε R e Λ φ₀ k : ℝ} (hU : 0 ≤ U) (hε : 0 < ε) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U))) (hc : ContinuousOn f (Ioi 0))
    (vOut : (T : Ici (0 : ℝ)) → C(Icc 0 (T : ℝ), WaveVector))
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ T, IsWaveIntegral hU T.property e Λ (incomingWaveCurve hU hUR hp hf φ₀)
      (vOut T) (incomingWaveVelocity hUR hp hf) (X T))
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hr : ∀ (T : Ici (0 : ℝ)) u v, (X T).1 u v 0 ≠ 0)
    (Z : C(Icc ε U, WaveVector)) (Sh : C(Icc ε U, ℝ))
    (hZ : Tendsto (renormalizedWaveRow hε.le k X) atTop (𝓝 Z))
    (hS : Tendsto (scalarBoundaryRow hε.le (fun T => scalarTransportCorrection T.property
      (radialNuField T.property e Λ (incomingWaveCurve hU hUR hp hf φ₀) (X T).1 (hr T))
      (X T).2.1)) atTop (𝓝 Sh))
    (hR : ∀ u, Z u 0 ≠ 0) {χ : ℝ → ℝ} (hχ : Tendsto χ (𝓝[<] (0 : ℝ)) atTop) :
    ∃ D : ℝ → C(Icc ε U, ℝ), ∃ Dh : C(Icc ε U, ℝ),
      IsTransverseScalarTrace hU X χ D Dh ∧
      (∀ u, Dh u = ((R - u) * f u + Sh u) / Z u 0) ∧ ∀ u, D 0 u = f u := by
  obtain ⟨D, Dh, hD, hDh, hfinite⟩ := incoming_transverse_scalar_boundary
    hU hε hUR hp hf hc vOut X hX hcompat hr Z Sh hZ hS hR hχ
  refine ⟨D, Dh, hD, hDh, fun u => ?_⟩
  let T : Ici (0 : ℝ) := ⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩
  let w : Icc 0 U := ⟨u, hε.le.trans u.property.1, u.property.2⟩
  have hz := waveIteration_incoming_value hU T.property e Λ
    (incomingWaveCurve hU hUR hp hf φ₀) (vOut T) (incomingWaveVelocity hUR hp hf)
    (X T) (hX T).choose w
  rw [(hX T).choose_spec, incomingWaveCurve_apply] at hz
  rw [hfinite T 0 le_rfl le_rfl u]
  change ((R - u) * f u + (∫ x in (0 : ℝ)..0, _)) / (X T).1 w ⟨0, le_rfl, le_rfl⟩ 0 = f u
  simp only [intervalIntegral.integral_same, add_zero, hz]
  change (R - u) * f u / (R - u) = f u
  exact mul_div_cancel_left₀ _ (sub_pos.2 (u.property.2.trans_lt hUR)).ne'

-- The norm bound is a pointwise bound on the physical derivative, also at the right endpoint.
example {U ε : ℝ} (hU : 0 < U) (hε : 0 < ε)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (D : ℝ → C(Icc ε U, ℝ)) (Dh : C(Icc ε U, ℝ))
    (hD : IsTransverseScalarTrace hU.le X χ D Dh) :
    ∃ T₀ : ℝ, ∃ hT₀ : 0 ≤ T₀, ∃ C : ℝ, 0 < C ∧ ∀ (T : Ici (0 : ℝ)) (t : ℝ)
      (ht : T₀ ≤ t) (htT : t ≤ T) (u : Icc ε U),
      |derivWithin (fun x => intervalExtension hU.le (X T).1 x
        ⟨t, hT₀.trans ht, htT⟩ 1) (Icc 0 U) u| ≤ C := by
  obtain ⟨T₀, C, hT₀, hC, hb⟩ := hD.2.2.2
  refine ⟨T₀, hT₀, C, hC, fun T t ht htT u => ?_⟩
  rw [(hD.1 T t (hT₀.trans ht) htT u).derivWithin
    (uniqueDiffOn_Icc hU u ⟨hε.le.trans u.property.1, u.property.2⟩)]
  exact ((D t).norm_coe_le_norm u).trans (hb t ht)

-- Any spatially constant log-lapse shift cancels from the anchored field.
example {K : Type*} [TopologicalSpace K] [CompactSpace K] (u₀ : K)
    (Z : C(K, WaveVector)) (c : ℝ) :
    waveAnchoredLog u₀ (Z + ContinuousMap.const K ![0, 0, c]) = waveAnchoredLog u₀ Z := by
  ext u
  change (Z u 2 + c) - (Z u₀ 2 + c) = Z u 2 - Z u₀ 2
  ring

-- The energy uses the same compact incoming interval as the field derivative.
example {U ε : ℝ} (hε : 0 ≤ ε) (k : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (t : ℝ) :
    ‖compactRadiationRow hε k X t‖ ≤ ‖radiationRow k X t‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro u
  exact (radiationRow k X t).norm_coe_le_norm ⟨u, hε.trans u.property.1, u.property.2⟩

-- The energy belongs to the derivative of the normalized log lapse, with the anchor subtracted.
example {U ε k T₀ C T : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (hT₀ : 0 ≤ T₀) (hT : T₀ ≤ T)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hE : IsRegularConformalEnergy hε hεU k X χ T₀ C) :
    MemLp (deriv (fun w => waveAnchoredLog ⟨U, hεU, le_rfl⟩ (renormalizedWaveRow hε 0 X (χ w)))) 2
      (volume.restrict (Ioo (regularTime (anchoringLapse (hε.trans hεU) X) T) 0)) := by
  apply MemLp.ae_eq ?_ ((hE.2.1 T hT).1)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
  exact (hE.1 w ⟨(hχ.2.2.2.1.monotone (hT₀.trans hT)).trans_lt hw.1, hw.2⟩).deriv.symm

-- The vertical primitive keeps the incoming derivative even when the time interval is degenerate.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F) :
    ∃ D : ℝ → C(Icc 0 V, WaveVector), ContinuousOn D (Ioi 0) ∧
      (∀ u, D u ⟨0, le_rfl, hV⟩ = F u) ∧
      ∀ u ∈ Ioc 0 U, HasDerivWithinAt (intervalExtension hU x.1) (D u) (Icc 0 U) u := by
  obtain ⟨D, S, hc, _hSc, _hDae, _hSae, hp, hd⟩ :=
    hx.exists_continuous_transverse_primitive hzin hinu hF hif
  refine ⟨D, hc, fun u => ?_, fun u hu => (hd u hu).1⟩
  rw [hp u]
  change F u + (∫ t in (0 : ℝ)..0, intervalExtension hV (S u) t) = F u
  simp only [intervalIntegral.integral_same, add_zero]

-- Anchor subtraction leaves the transverse derivative unchanged, also at u=U and t=T.
example {U ε : ℝ} (hU : 0 ≤ U) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (D : ℝ → C(Icc ε U, ℝ)) (Dh : C(Icc ε U, ℝ))
    (hD : IsTransverseConformalTrace hU X χ D Dh) (T : Ici (0 : ℝ)) :
    HasDerivWithinAt (fun x => intervalExtension hU (X T).1 x ⟨T, T.property, le_rfl⟩ 2 -
      (X T).1 ⟨U, hU, le_rfl⟩ ⟨T, T.property, le_rfl⟩ 2)
      (D T ⟨U, hεU, le_rfl⟩) (Icc 0 U) U :=
  (hD.1 T T T.property le_rfl ⟨U, hεU, le_rfl⟩).sub_const _

-- The uniform derivative limit preserves the full primitive, including its additive constant.
example {a b : ℝ} (hab : a ≤ b) {f d : ℕ → C(Icc a b, ℝ)} {fh dh : C(Icc a b, ℝ)}
    (hf : Tendsto f atTop (𝓝 fh)) (hd : Tendsto d atTop (𝓝 dh))
    (hder : ∀ n (u : Icc a b),
      HasDerivWithinAt (intervalExtension hab (f n)) (d n u) (Icc a b) u) (u : Icc a b) :
    fh u = fh ⟨a, le_rfl, hab⟩ + ∫ x in a..(u : ℝ), intervalExtension hab dh x := by
  have he := (continuous_derivative_limit hab hf hd (Eventually.of_forall hder)).1
  exact congrArg (fun z : C(Icc a b, ℝ) => z u) he

-- The horizon derivative is an ordinary derivative at interior points of the incoming interval.
example {U ε : ℝ} (hU : 0 ≤ U) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hD : IsTransverseWaveBoundary hU hεU X χ Z D Dh) {u : ℝ} (hu : u ∈ Ioo ε U) :
    HasDerivAt (intervalExtension hεU Z) (Dh ⟨u, hu.1.le, hu.2.le⟩) u :=
  (hD.2.2.2 ⟨u, hu.1.le, hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hu.2)

-- The anchored horizon log lapse has the same transverse derivative at the right endpoint.
example {U ε : ℝ} (hU : 0 ≤ U) (hεU : ε < U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hD : IsTransverseWaveBoundary hU hεU.le X χ Z D Dh) :
    derivWithin (fun x => Z (projIcc ε U hεU.le x) 2 - Z ⟨U, hεU.le, le_rfl⟩ 2)
      (Icc ε U) U = Dh ⟨U, hεU.le, le_rfl⟩ 2 := by
  have hd := (ContinuousLinearMap.proj (2 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt U
    (hD.2.2.2 ⟨U, hεU.le, le_rfl⟩)
  exact (hd.sub_const (Z ⟨U, hεU.le, le_rfl⟩ 2)).derivWithin
    (uniqueDiffOn_Icc hεU U ⟨hεU.le, le_rfl⟩)

-- Banach-valued continuity gives joint continuity up to the horizon, including both spatial endpoints.
example {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh) :
    let J := Ioc (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0
    Continuous (fun q : J × Icc ε U => compactifiedWaveRow hε hεU X χ Z q.1 q.2) ∧
    Continuous (fun q : J × Icc ε U => compactifiedTransverseRow χ D Dh q.1 q.2) := by
  constructor
  · exact continuous_eval.comp ((hB.2.2.1.domRestrict.comp continuous_fst).prodMk continuous_snd)
  · exact continuous_eval.comp ((hB.2.2.2.1.domRestrict.comp continuous_fst).prodMk continuous_snd)

-- Normalization preserves the radius and scalar and fixes the log lapse to zero at the anchor.
example {K : Type*} [TopologicalSpace K] [CompactSpace K] (u₀ u : K) (Z : C(K, WaveVector)) :
    waveNormalize u₀ Z u 0 = Z u 0 ∧ waveNormalize u₀ Z u 1 = Z u 1 ∧
      waveNormalize u₀ Z u 2 = Z u 2 - Z u₀ 2 ∧ waveNormalize u₀ Z u₀ 2 = 0 := by
  simp [waveNormalize_apply]

-- At the horizon's anchoring endpoint the transverse derivative is the original physical limit.
example {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε < U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU.le) X) 0 χ)
    (hB : IsRegularWaveBoundary hε hεU.le X χ Z D Dh) :
    derivWithin (intervalExtension hεU.le (compactifiedWaveRow hε hεU.le X χ Z 0)) (Icc ε U) U =
      Dh ⟨U, hεU.le, le_rfl⟩ := by
  have hd := hB.2.2.2.2 0 ⟨hχ.2.2.2.2.2.1 0, le_rfl⟩ ⟨U, hεU.le, le_rfl⟩
  simpa only [compactifiedTransverseRow, Function.update_self] using
    hd.derivWithin (uniqueDiffOn_Icc hεU U ⟨hεU.le, le_rfl⟩)

-- The vector estimate controls the actual derivative, with the spatial supremum before integration.
example {U ε k T₀ C T : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (hT₀ : 0 ≤ T₀) (hT : T₀ ≤ T)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ) (Z : C(Icc ε U, WaveVector))
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hE : IsRegularWaveEnergy hε hεU k X χ Z T₀ C) :
    let J := Ioo (regularTime (anchoringLapse (hε.trans hεU) X) T) 0
    let Ψ := compactifiedWaveRow hε hεU X χ Z
    MemLp (deriv Ψ) 2 (volume.restrict J) ∧
      (∫ w in J, ‖deriv Ψ w‖ ^ 2) ≤
        C * ∫ t in Ioi T, (‖compactRadiationRow hε k X t‖ ^ 2 + Real.exp (-(2 * k) * t)) := by
  let F := fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)
  have he : deriv (compactifiedWaveRow hε hεU X χ Z) =ᵐ[
      volume.restrict (Ioo (regularTime (anchoringLapse (hε.trans hεU) X) T) 0)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
    exact (hE.1 w ⟨(hχ.2.2.2.1.monotone (hT₀.trans hT)).trans_lt hw.1, hw.2⟩).deriv
  refine ⟨((hE.2.1 T hT).1).ae_eq he.symm, ?_⟩
  rw [integral_congr_ae (he.mono (fun _ hw => congrArg (fun z => ‖z‖ ^ 2) hw))]
  exact (hE.2.1 T hT).2

-- The same mixed bound gives L2 physical derivatives along every incoming ray, including u=U.
example {U ε k T₀ C T : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (hT₀ : 0 ≤ T₀) (hT : T₀ ≤ T)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ) (Z : C(Icc ε U, WaveVector))
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hE : IsRegularWaveEnergy hε hεU k X χ Z T₀ C) (u : Icc ε U) :
    MemLp (deriv (fun w => compactifiedWaveRow hε hεU X χ Z w u)) 2
      (volume.restrict (Ioo (regularTime (anchoringLapse (hε.trans hεU) X) T) 0)) := by
  have hi := (ContinuousMap.evalCLM ℝ u : C(Icc ε U, WaveVector) →L[ℝ] WaveVector).comp_memLp'
    ((hE.2.1 T hT).1)
  apply hi.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
  exact ((ContinuousMap.evalCLM ℝ u).hasFDerivAt.comp_hasDerivAt w
    (hE.1 w ⟨(hχ.2.2.2.1.monotone (hT₀.trans hT)).trans_lt hw.1, hw.2⟩)).deriv.symm

-- Affine continuation retains the endpoint value and adds exactly the energy of its new slope.
example {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (c q : WaveVector) :
    ∃ z : C(Icc a b, WaveVector), ∃ d : Lp WaveVector 2 (volume.restrict (Icc a b)),
      IsAffineCharacteristicData a b (fun _ => c) (fun _ => 0) q z d ∧
        (∫ x in Icc a b, ‖d x‖ ^ 2) = b * ‖q‖ ^ 2 := by
  obtain ⟨z, d, hd⟩ := exists_affine_characteristic_data ha hb continuous_const.continuousOn
    (fun x _ => hasDerivAt_const x c) (memLp_const (0 : WaveVector)) q
  refine ⟨z, d, hd, ?_⟩
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero, zero_add] using hd.2.2.2.2.2

-- The positive side has the physical radial slope, constant scalar and constant normalized log lapse.
example {U ε T b : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (z : C(Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b, C(Icc ε U, WaveVector)))
    (d : Lp C(Icc ε U, WaveVector) 2
      (volume.restrict (Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b)))
    (hd : IsRegularContinuationData hε hεU X χ Z O T b z d)
    (w : Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b) (hw : 0 ≤ (w : ℝ))
    (u : Icc ε U) :
    z w u = ![Z u 0 + (w : ℝ) * (-(anchoredAmplitude ⟨U, hεU, le_rfl⟩ Z) * O) u,
      Z u 1, Z u 2 - Z ⟨U, hεU, le_rfl⟩ 2] := by
  rw [hd.2.2.1 w hw]
  ext i
  fin_cases i <;> simp [compactifiedWaveRow, waveNormalize_apply, radialHorizonVelocity]

-- Evaluation on any incoming ray preserves the exact primitive required by the local solver.
example {K : Type*} [TopologicalSpace K] [CompactSpace K] {a b : ℝ}
    (f g : ℝ → C(K, WaveVector)) (q : C(K, WaveVector))
    (z : C(Icc a b, C(K, WaveVector))) (d : Lp C(K, WaveVector) 2 (volume.restrict (Icc a b)))
    (hd : IsAffineCharacteristicData a b f g q z d) (u : K) :
    ∃ hab : a ≤ b,
      ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) (ContinuousMap.evalCLM ℝ u) z =
        ContinuousMap.const _ (f a u) + horizontalPrimitive hab
          ((ContinuousMap.evalCLM ℝ u).compLpL 2 (volume.restrict (Icc a b)) d) := by
  obtain ⟨hab, hz⟩ := hd.1
  refine ⟨hab, ?_⟩
  rw [hz, map_add, horizontalPrimitive_compLp]
  rfl

-- A negative left endpoint and a smaller right endpoint retain the constant and decrease both norms.
example (z : C(Icc (-2 : ℝ) 3, WaveVector))
    (d : Lp WaveVector 2 (volume.restrict (Icc (-2 : ℝ) 3))) (z₀ : WaveVector)
    (hz : z = ContinuousMap.const _ z₀ + horizontalPrimitive (by norm_num) d) :
    ∃ d' : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) (1 - (-2)))),
      (d' =ᵐ[volume.restrict (Icc (0 : ℝ) (1 - (-2)))] fun t => d (-2 + t)) ∧
      ‖d'‖ ≤ ‖d‖ ∧ ‖z.comp (intervalRebase (by norm_num : (1 : ℝ) ≤ 3))‖ ≤ ‖z‖ ∧
      z.comp (intervalRebase (by norm_num : (1 : ℝ) ≤ 3)) =
        ContinuousMap.const _ z₀ + horizontalPrimitive (by norm_num) d' :=
  rebase_characteristic_data (by norm_num) (by norm_num) z d hz

-- All sufficiently late cuts use the same bounds and the same positive continuation width.
example {U ε ρ T₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hdata : HasBoundedRegularContinuationData hε hεU X χ Z O D Dh ρ T₀) :
    ∃ b R M : ℝ, 0 < b ∧ 0 < R ∧ 0 < M ∧ ∀ T, max T₀ 1 ≤ T →
      ∃ z : C(Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b, C(Icc ε U, WaveVector)),
      ∃ d : Lp C(Icc ε U, WaveVector) 2
        (volume.restrict (Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b)),
        IsRegularContinuationData hε hεU X χ Z O T b z d ∧
        (∀ w u, ρ / 2 ≤ z w u 0) ∧ ‖z‖ ≤ R ∧ ‖d‖ ≤ M ∧
        ‖compactifiedTransverseRow χ D Dh
          (regularTime (anchoringLapse (hε.trans hεU) X) T)‖ ≤ R := by
  obtain ⟨b, R, M, hb, hR, hM, hd, hbound⟩ := hdata
  refine ⟨b, R, M, hb, hR, hM, ?_⟩
  intro T hT
  obtain ⟨z, d, hz, hr, _hconstraint⟩ := hd T ((le_max_left _ _).trans hT)
    (lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hT))
  exact ⟨z, d, hz, hr, ((hbound T hT).2 z d hz).1, ((hbound T hT).2 z d hz).2,
    (hbound T hT).1⟩

-- Regular time zero is strictly inside the solved rectangle and has the exact initial horizon value.
example {U ε e Λ T₀ u₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀) :
    ∃ ua L A : ℝ, ∃ hL : 0 ≤ L, ∃ y : WaveState A L, ∃ t : Icc 0 A,
      ε < ua ∧ ua < u₀ ∧ u₀ < ua + L ∧ ua + L < U ∧
      0 < (t : ℝ) ∧ (t : ℝ) < A ∧
      y.1 t ⟨0, le_rfl, hL⟩ = waveNormalize ⟨U, hεU, le_rfl⟩ Z (projIcc ε U hεU ua) ∧
      ∀ w s, 0 < y.1 w s 0 := by
  obtain ⟨ua, L, T, b, hea, ham, hmr, hrU, _hT₀, _hT, hn, hb,
    hL, _hV, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, hfuture, _hout, hxin, _hbottom,
    hr, _hmatch, _hvelocity⟩ := hcross
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  let t : Icc 0 (b - V T) := ⟨-V T, (neg_pos.2 hn).le, by linarith⟩
  refine ⟨ua, L, b - V T, hL, y, t, hea, ham, hmr, hrU, neg_pos.2 hn, ?_, ?_, hr⟩
  · change -V T < b - V T
    linarith
  · rw [hxin, hfuture t (by change 0 ≤ V T + -V T; linarith)]
    simp only [t, V, add_neg_cancel, zero_smul, add_zero, compactifiedWaveRow, Function.update_self]

-- The normalized source has the exact Jacobian, even with arbitrary anchored log derivative.
example (e Λ α β : ℝ) (z p q : WaveVector) :
    waveSource e Λ (z - ![0, 0, α]) (Real.exp (-α) • (q - ![0, 0, β])) p =
      Real.exp (-α) • waveSource e Λ z p q := by
  simpa only [Real.log_exp, ← Real.exp_neg] using
    waveSource_regular_swap e Λ z p q (Real.exp_pos α) β

-- Both mixed derivative orders agree at the anchoring endpoint, using its one-sided u derivative.
example {U ε e Λ w : ℝ} (hε : 0 ≤ ε) (hεU : ε < U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector))
    (Dh : C(Icc ε U, WaveVector))
    (he : IsRegularWaveEvolution hε hεU.le e Λ X χ Z D Dh)
    (hw : w ∈ Ioo (regularTime (anchoringLapse (hε.trans hεU.le) X) 0) 0) :
    deriv (fun s => compactifiedTransverseRow χ D Dh s ⟨U, hεU.le, le_rfl⟩) w =
      derivWithin (intervalExtension hεU.le
        (waveNormalize ⟨U, hεU.le, le_rfl⟩ (regularWaveVelocityRow hε hεU.le X χ w))) (Icc ε U) U := by
  exact (he w hw ⟨U, hεU.le, le_rfl⟩).1.deriv.trans
    ((he w hw ⟨U, hεU.le, le_rfl⟩).2.derivWithin
      (uniqueDiffOn_Icc hεU U ⟨hεU.le, le_rfl⟩)).symm

-- The transformed scalar equation keeps both products and the exact physical radius denominator.
example {U ε e Λ w : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector))
    (Dh : C(Icc ε U, WaveVector))
    (he : IsRegularWaveEvolution hε hεU e Λ X χ Z D Dh)
    (hw : w ∈ Ioo (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0) (u : Icc ε U) :
    let Q := waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)
    let W := compactifiedTransverseRow χ D Dh
    HasDerivAt (fun s => W s u 1)
      (-(Q u 0 * W w u 1 + W w u 0 * Q u 1) / compactifiedWaveRow hε hεU X χ Z w u 0) w := by
  exact (ContinuousLinearMap.proj (1 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt w
    (he w hw u).1

-- Recovering the integral system also identifies the full incoming derivative, not only its initial value.
example {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ) (z p q S : WaveRectangle U V)
    (hr : ∀ u v, z u v 0 ≠ 0)
    (hS : ∀ u v, S u v = waveSource e Λ (z u v) (p u v) (q u v))
    (hz : ∀ u v, HasDerivWithinAt (intervalExtension hV (z u)) (q u v) (Icc 0 V) v)
    (hp : ∀ u v, HasDerivWithinAt (intervalExtension hV (p u)) (S u v) (Icc 0 V) v)
    (hq : ∀ v u, HasDerivWithinAt (intervalExtension hU (flipRectangle q v)) (S u v) (Icc 0 U) u)
    (hinit : ∀ u, HasDerivWithinAt (intervalExtension hU (flipRectangle z ⟨0, le_rfl, hV⟩))
      (p u ⟨0, le_rfl, hV⟩) (Icc 0 U) u) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U),
      HasDerivWithinAt (intervalExtension hU z) (p (projIcc 0 U hU u)) (Icc 0 U) u := by
  have hi := wave_integral_of_continuous_derivatives hU hV e Λ z p q S hr hS hz hp hq hinit
  filter_upwards [hi.1.horizontal_derivative hi.2, intervalToLp_ae hU 2 p] with u hu hp
  exact hu.congr_deriv hp

-- The whole horizon section, including both spatial endpoints, belongs to the same crossing solution.
example {U ε e Λ T₀ u₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀) :
    ∃ ua L A : ℝ, ∃ y : WaveState A L, ∃ t : Icc 0 A,
      ε < ua ∧ ua < u₀ ∧ u₀ < ua + L ∧ ua + L < U ∧ 0 < (t : ℝ) ∧ (t : ℝ) < A ∧
      ∀ s, y.1 t s = waveNormalize ⟨U, hεU, le_rfl⟩ Z (projIcc ε U hεU (ua + s)) ∧
        y.2.1 t s = Dh (projIcc ε U hεU (ua + s)) := by
  obtain ⟨ua, L, T, b, hea, ham, hmr, hrU, _hT₀, _hT, hn, hb,
    _hL, _hV, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, _hfuture, _hout, _hxin, _hbottom,
    _hr, hmatch, _hvelocity⟩ := hcross
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  let t : Icc 0 (b - V T) := ⟨-V T, (neg_pos.2 hn).le, by linarith⟩
  refine ⟨ua, L, b - V T, y, t, hea, ham, hmr, hrU, neg_pos.2 hn, ?_, ?_⟩
  · change -V T < b - V T
    linarith
  · intro s
    simpa only [t, V, add_neg_cancel, compactifiedWaveRow, compactifiedTransverseRow,
      Function.update_self] using hmatch t (by change V T + -V T ≤ 0; simp) s

-- Equality of primitives on a shifted interval identifies the L2 class, independently of representatives.
example (f g : Lp WaveVector 2 (volume.restrict (Icc (-2 : ℝ) 3)))
    (he : horizontalPrimitive (by norm_num) f = horizontalPrimitive (by norm_num) g) : f = g :=
  horizontalPrimitive_injective (by norm_num : (-2 : ℝ) < 3) he

-- The spatial constraint includes the one-sided anchoring endpoint.
example {U ε w : ℝ} (hε : 0 ≤ ε) (hεU : ε < U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (D : ℝ → C(Icc ε U, WaveVector))
    (Dh : C(Icc ε U, WaveVector))
    (hc : IsRegularSpatialConstraint hε hεU.le X χ Z D Dh)
    (hw : w ∈ Ioo (regularTime (anchoringLapse (hε.trans hεU.le) X) 0) 0) :
    let a : Icc ε U := ⟨U, hεU.le, le_rfl⟩
    let W := compactifiedTransverseRow χ D Dh w
    derivWithin (fun s => intervalExtension hεU.le W s 0) (Icc ε U) U =
      W a 2 * W a 0 - compactifiedWaveRow hε hεU.le X χ Z w a 0 * (W a 1) ^ 2 :=
  (hc w hw ⟨U, hεU.le, le_rfl⟩).derivWithin (uniqueDiffOn_Icc hεU U ⟨hεU.le, le_rfl⟩)

-- The same crossing solution satisfies the constraint and its integral sign strictly beyond V=0.
example {U ε e Λ T₀ u₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀) :
    ∃ L T b : ℝ, ∃ hL : 0 ≤ L,
      let V := regularTime (anchoringLapse (hε.trans hεU) X)
      ∃ y : WaveState (b - V T) L, ∃ t : Icc 0 (b - V T),
        0 < V T + (t : ℝ) ∧ (t : ℝ) < b - V T ∧
        (∀ w s, 0 < y.1 w s 0) ∧
        (∀ s, HasDerivWithinAt (fun x => intervalExtension hL (y.2.1 t) x 0)
          (y.2.1 t s 2 * y.2.1 t s 0 - y.1 t s 0 * (y.2.1 t s 1) ^ 2) (Icc 0 L) s) ∧
        ∀ s, y.2.1 t s 0 * Real.exp (-y.1 t s 2) ≤
          y.2.1 t ⟨0, le_rfl, hL⟩ 0 * Real.exp (-y.1 t ⟨0, le_rfl, hL⟩ 2) := by
  obtain ⟨_ua, L, T, b, _hea, _ham, _hmr, _hrU, _hT₀, _hT, hn, hb,
    hL, _hV, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, _hfuture, _hout, _hxin, _hbottom,
    hr, _hmatch, _hvelocity, hc, hi, _hradial⟩ := hcross
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  let t : Icc 0 (b - V T) := ⟨b / 2 - V T, by linarith, by linarith⟩
  refine ⟨L, T, b, hL, y, t, ?_, ?_, hr, hc t, ?_⟩
  · change 0 < V T + (b / 2 - V T)
    linarith
  · change b / 2 - V T < b - V T
    linarith
  · intro s
    rw [hi t s]
    apply sub_le_self
    apply intervalIntegral.integral_nonneg_of_forall s.property.1
    intro x
    exact mul_nonneg (mul_nonneg (hr t (projIcc 0 L hL x)).le (Real.exp_pos _).le) (sq_nonneg _)

-- An L1 derivative suffices at the joining point; no bounded derivative is required.
example {f g : ℝ → ℝ} (hc : ContinuousOn f (Icc (-1) 0))
    (hd : ∀ x ∈ Ioo (-1) 0, HasDerivAt f (g x) x)
    (hg : IntervalIntegrable g volume (-1) 0) :
    AbsolutelyContinuousOnInterval (fun x => f (min x 0)) (-1) 1 :=
  constant_continuation_absolutelyContinuous (by norm_num) (by norm_num) hc hd hg

-- The same bounded physical data now retain their incoming constraint through V=0.
example {U ε ρ T₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hdata : HasBoundedRegularContinuationData hε hεU X χ Z O D Dh ρ T₀) :
    ∃ b : ℝ, 0 < b ∧ ∀ T, T₀ ≤ T → 0 < T →
      ∃ z d, IsRegularContinuationData hε hεU X χ Z O T b z d ∧
        ∃ hab : regularTime (anchoringLapse (hε.trans hεU) X) T ≤ b,
          ∀ u : Icc ε U, ∃ n : C(Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b, ℝ),
            (∀ᵐ w ∂volume.restrict (Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b),
              d w u 0 = n (projIcc _ b hab w)) ∧
            AbsolutelyContinuousOnInterval (intervalExtension hab n)
              (regularTime (anchoringLapse (hε.trans hεU) X) T) b := by
  obtain ⟨b, _R, _M, hb, _hR, _hM, hd, _hbound⟩ := hdata
  refine ⟨b, hb, fun T hT hTp => ?_⟩
  obtain ⟨z, d, hz, _hr, hab, hconstraint⟩ := hd T hT hTp
  refine ⟨z, d, hz, hab, fun u => ?_⟩
  obtain ⟨n, hn, hAC, _hderiv⟩ := hconstraint u
  exact ⟨n, hn, hAC⟩

-- Translation with a negative left endpoint and a strict restriction preserves absolute continuity.
example {f : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f (-2) 3) :
    AbsolutelyContinuousOnInterval (fun t => f (-2 + t)) 0 3 := by
  simpa only [show (1 : ℝ) - -2 = 3 by norm_num] using
    absolutelyContinuous_rebase (by norm_num : (-2 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 3) hf

-- The propagated incoming constraint includes the actual radius derivative on the horizon and no atom there.
example {U ε e Λ T₀ u₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector))
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀) :
    ∃ L T b : ℝ, ∃ _hL : 0 ≤ L,
      let V := regularTime (anchoringLapse (hε.trans hεU) X)
      ∃ hV : 0 ≤ b - V T, ∃ y : WaveState (b - V T) L,
      ∃ N : C(Icc 0 (b - V T), C(Icc 0 L, ℝ)), ∃ th tf : Icc 0 (b - V T),
        V T + (th : ℝ) = 0 ∧ 0 < (th : ℝ) ∧ (th : ℝ) < tf ∧ (tf : ℝ) < b - V T ∧
        ∀ s, HasDerivWithinAt (fun t => intervalExtension hV y.1 t s 0)
            (N th s) (Icc 0 (b - V T)) th ∧
          AbsolutelyContinuousOnInterval (fun t => intervalExtension hV N t s *
            Real.exp (-intervalExtension hV y.1 t s 2)) 0 (b - V T) ∧
          N tf s * Real.exp (-y.1 tf s 2) =
            N ⟨0, le_rfl, hV⟩ s * Real.exp (-y.1 ⟨0, le_rfl, hV⟩ s 2) -
              ∫ t in (0 : ℝ)..(tf : ℝ), intervalExtension hV y.1 t s 0 *
                Real.exp (-intervalExtension hV y.1 t s 2) * (y.2.2 t s 1) ^ 2 := by
  obtain ⟨_ua, L, T, b, _hea, _ham, _hmr, _hrU, _hT₀, _hT, hn, hb,
    hL, hV, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, _hfuture, _hout, _hxin, _hbottom,
    _hr, _hmatch, _hvelocity, _hc, _hi, _hweak, _hdistribution, _hL2, _hmetric, _hcoord, _hconnection,
    _hRicci, _hsource, _hmixed, _hangular, _hoffdiag, _hmaxwell, _heinstein, _hscalar, _hspherical,
    _htransition, _hfields, N, _hnae, hder, _hnd, hni⟩ := hcross
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  let th : Icc 0 (b - V T) := ⟨-V T, (neg_pos.2 hn).le, by linarith⟩
  let tf : Icc 0 (b - V T) := ⟨b / 2 - V T, by linarith, by linarith⟩
  refine ⟨L, T, b, hL, hV, y, N, th, tf, add_neg_cancel _, neg_pos.2 hn, ?_, ?_, ?_⟩
  · change -V T < b / 2 - V T
    linarith
  · change b / 2 - V T < b - V T
    linarith
  · exact fun s => ⟨hder th s, (hni s).1, (hni s).2.2 tf⟩

end CauchyHorizon.Tests
