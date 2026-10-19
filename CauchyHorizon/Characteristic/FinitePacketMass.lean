import CauchyHorizon.Characteristic.ProfileMass
import CauchyHorizon.Analysis.SignedPackets
import CauchyHorizon.Characteristic.ProfilePhase
import CauchyHorizon.Characteristic.IncomingEquality
import CauchyHorizon.Characteristic.ContinuousFirstOrder
import CauchyHorizon.Characteristic.OpticalIdentities
import CauchyHorizon.Characteristic.ContinuousWave
import CauchyHorizon.Characteristic.RadiationPhase

/-! The original nonlinear construction applied to finite signed packet sums. -/

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction ENNReal ContDiff

namespace CauchyHorizon.Background

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 4096 in
def FinitePacketMassResponse (B : Background) {s l : ℝ} (D : AdmissibleOutgoingData B s l)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {ι : Type*} [Fintype ι]
    (ψ : ℝ → ℝ) (c E : ι → ℝ) (t L : ι → ℕ → ℝ) (ℓ Ucap : ℝ) : Prop :=
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
      (∀ n, n ≠ 0 → ∀ x, P n x = ∑ i, c i *
        (Real.sqrt (E i / ((∫ y, ψ y ^ 2) * L i n)) * ψ ((x - t i n) / L i n))) ∧
      (∀ U₀ : ℝ, 0 < U₀ →
        Tendsto (fun n => primitiveEnergy (1 - 1 / p.toReal)
          (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U₀ - ∫ x, P n x ^ 2)
          atTop (𝓝 0)) ∧
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
          (∀ n, P n = 0 → ∀ V : Ici (0 : ℝ), X n V = X 0 V) ∧
          ∃ χ : ℕ → ℝ → ℝ,
          (∀ n, IsRegularTimeCoordinate (anchoringLapse hU.le (X n)) 0 (χ n)) ∧
          ∀ ε (hε : 0 < ε) (hεU : ε ≤ U),
            (∀ d : ℝ,
              let F := radiationComparisonRow hε.le B.innerRate (B.transmission hm * Ch)
                X (fun n v => P n (B.outerRate * v + d))
              (∀ n, MemLp (F n) 2 (volume.restrict (Ici 0))) ∧
                Tendsto (fun n => ∫ v in Ici (0 : ℝ), ‖F n v‖ ^ 2) atTop (𝓝 0)) ∧
            (ε < U → ∀ n, ∃ Tw : ℝ, 0 ≤ Tw ∧ ∀ u₀ ∈ Ioo ε U,
              HasLocalSphericalWeakExtension hε.le hεU B.charge B.cosmological
                (X n) (χ n) Tw u₀) ∧
            ∃ hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0,
              let ν := fun n (V : Ici (0 : ℝ)) => radialNuField V.property B.charge B.cosmological
                (incomingWaveCurve hU.le hUR hp (hf n) (horizonPhi h r 0)) (X n V).1 (hr n V)
              HasCompactifiedGeometry hε.le B.innerRate X ν ∧
              (∀ v, 0 ≤ v → Tendsto
                (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) v)
                atTop (𝓝 (massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v))) ∧
              RadiationMassProfile hε.le B.innerRate B.outerRate (B.transmission hm * Ch)
                B.charge B.cosmological X ν hr (fun _ => 0) (fun n => P n) ∧
              ∀ n, P n = 0 → massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) =
                massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0)

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 4096 in
theorem exists_finite_packet_mass_response (B : Background)
    {s l H Hlo dH : ℝ} {h r : ℝ → ℝ} {p : ℝ≥0∞}
    (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    (hcrit : B.innerRate = (1 - 1 / p.toReal) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    (hc : Continuous h) (hb : ∀ v, ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v)
    (hrc : Continuous r) (hrb : ∀ v, B.event - dH ≤ r v) (hrinit : B.inner < r 0)
    (hrd : ∀ v ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological) (Ici 0) v)
    (hrdec : ∀ v ∈ Ici (0 : ℝ), ‖r v - B.event‖ ≤ dH * Real.exp (-(2 * s) * v))
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (c E : ι → ℝ) (hE : ∀ i, 0 < E i) (t L : ι → ℕ → ℝ)
    (hL : ∀ i n, 0 < L i n) (htop : ∀ i, Tendsto (t i) atTop atTop)
    (hLtop : ∀ i, Tendsto (L i) atTop atTop) (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    B.FinitePacketMassResponse {
      tail := h, radius := r, upper := H, lower := Hlo, deviation := dH,
      rate_pos := B.innerRate_pos.trans hks, upper_nonneg := hH, lower_pos := hHlo,
      deviation_nonneg := hdH, deviation_lt := hdHR, tail_continuous := hc,
      tail_bound := hb, tail_lower := hlo, radius_continuous := hrc, radius_lower := hrb,
      radius_initial := hrinit, radius_derivative := hrd, radius_decay := hrdec }
      hp ψ c E t L ℓ Ucap := by
  obtain ⟨A, Apt, hA, hApt, P, Q, hP0, _hQ0, hformula, hd, hPC, hPi,
    hQi, hQlim, hsup, m, hsuppP, hfront, hprimitive, hdata⟩ :=
    finite_packet_incoming_data hp hpfin hψ hcomp hpos hsupp c E hE t L hL htop hLtop ℓ
  obtain ⟨U, hU, hUR, hcap, hfU, hm, X, hX, hfloor, hcompat, hfinite, hInitial, hbounded,
    χ, hχ, hresponse⟩ :=
    B.exists_profile_mass_response hp hpfin hcrit hks hl hH hHlo hdH hdHR
      hc hb hlo hrc hrb hrinit hrd hrdec hA hApt (sq_nonneg (∑ i, |c i| * Real.sqrt (E i)))
      P Q hP0 hd hPC hPi hQi hQlim m ℓ hsuppP hfront hdata Ucap hUcap
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
  let f := fun n => logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)
  have hfeq (n : ℕ) (hn : P n = 0) : f n = f 0 := by dsimp only [f]; rw [hn, hP0]
  have hzero (n : ℕ) (hn : P n = 0) (V : Ici (0 : ℝ)) : X n V = X 0 V :=
    IsWaveIntegral.incoming_unique_of_eq hU.le V.property hUR hp (hfU n) (hfU 0)
      (hfeq n hn) (hX n V) (hX 0 V)
  refine ⟨P, hP0, hformula, (fun U₀ hU₀ => (hprimitive U₀ hU₀).2),
    U, hU, hUR, hcap, hfU, hm, X, hX, hfirst, hflux, hwave, hfloor, hcompat,
    hfinite, hInitial, hbounded, hzero, χ, hχ, ?_⟩
  intro ε hε hεU
  obtain ⟨hF, hOptical, _hScalar, _hTrace, _hConf, _hConfTrace, hr, hcompact, hmassFinite,
    Z, Nh, Γ, hZ, hNh, hsign, hmass⟩ := hresponse ε hε hεU
  have hweak (hεlt : ε < U) (n : ℕ) : ∃ Tw : ℝ, 0 ≤ Tw ∧ ∀ u₀ ∈ Ioo ε U,
      HasLocalSphericalWeakExtension hε.le hεU B.charge B.cosmological (X n) (χ n) Tw u₀ := by
    obtain ⟨_Td, _Cd, _d, _hTd, _hCd, _hd, _Dh, _Zg, _hZg, _hDh, _htail,
      _hlower, _hmono, _hnu, _hnuχ, _hsign, _hradius, hWave⟩ := hOptical
    obtain ⟨_Du, _Duh, _hB, _hregular, _hevolution, Tw, _Cw, hTw, _hCw,
      _henergy, _hdata, hcross⟩ := hWave hεlt n
    exact ⟨Tw, hTw, fun u₀ hu₀ => (hcross u₀ hu₀).2⟩
  refine ⟨radiation_comparison_phase hε.le B.outerRate_pos X P Q hd hQi hQlim hF,
    hweak, hr, hcompact, hmassFinite, ⟨Z, Nh, Γ, hZ, hNh, hsign,
    hmass.remove_constant_phase (fun n => (hPi n).1) hsup⟩, fun n hn => ?_⟩
  exact incoming_massRow_eq hU.le hε.le hUR hp (hfU n) (hfU 0) (hfeq n hn)
    (hr n) (hr 0) (funext (hzero n hn))

theorem exists_late_finite_packet_mass_response (B : Background)
    {s l H Hlo : ℝ} {h : ℝ → ℝ} {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    (hcrit : B.innerRate = (1 - 1 / p.toReal) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hc : ContinuousOn h (Ici 0)) (hb : ∀ v ∈ Ici (0 : ℝ), ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (c E : ι → ℝ) (hE : ∀ i, 0 < E i) (t L : ι → ℕ → ℝ)
    (hL : ∀ i n, 0 < L i n) (htop : ∀ i, Tendsto (t i) atTop atTop)
    (hLtop : ∀ i, Tendsto (L i) atTop atTop) (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ D : AdmissibleOutgoingData B s l,
      (∀ v ∈ Ici (0 : ℝ), D.tail v = h (v + T)) ∧
      D.upper = H * Real.exp (-s * T) ∧ D.lower = Hlo * Real.exp (-l * T) ∧
      B.FinitePacketMassResponse D hp ψ c E t L ℓ Ucap := by
  obtain ⟨T, hT, D, heq, hupper, hlower⟩ :=
    B.exists_admissible_late_data (B.innerRate_pos.trans hks) hH hHlo hc hb hlo
  refine ⟨T, hT, D, heq, hupper, hlower, ?_⟩
  exact B.exists_finite_packet_mass_response hp hpfin hcrit hks hl D.upper_nonneg D.lower_pos
    D.deviation_nonneg D.deviation_lt D.tail_continuous D.tail_bound D.tail_lower
    D.radius_continuous D.radius_lower D.radius_initial D.radius_derivative D.radius_decay
    hψ hcomp hpos hsupp c E hE t L hL htop hLtop ℓ Ucap hUcap

end CauchyHorizon.Background
