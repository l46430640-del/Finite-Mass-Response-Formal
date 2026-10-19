import CauchyHorizon.Characteristic.FinitePacketMass
import CauchyHorizon.Characteristic.PairProfile

/-! The normalized pair shape and exact cancellation on the original nonlinear family. -/

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction ENNReal ContDiff

namespace CauchyHorizon.Background

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 4096 in
def PairPacketMassResponse (B : Background) {s l : ℝ} (D : AdmissibleOutgoingData B s l)
    {p : ℝ≥0∞} (hp : 4 ≤ p) (ψ : ℝ → ℝ) (E : ℝ) (t L : ℕ → ℝ)
    (δ σ ℓ Ucap : ℝ) : Prop :=
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
        (ψ ((x - t n) / L n) + σ * ψ ((x - t n) / L n - δ))) ∧
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
          (δ = 0 → σ = -1 → ∀ n (V : Ici (0 : ℝ)), X n V = X 0 V) ∧
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
              ∃ Z : C(Icc ε U, WaveVector), ∃ Nh Γ : C(Icc ε U, ℝ),
                Tendsto (renormalizedWaveRow hε.le B.innerRate (X 0)) atTop (𝓝 Z) ∧
                Tendsto (scalarBoundaryRow hε.le (ν 0)) atTop (𝓝 Nh) ∧
                (∀ u, 0 < Z u 0 ∧ 0 < waveAmplitude Z u ∧ Nh u < 0 ∧
                  Γ u = (-2 * Nh u / (B.outerRate * waveAmplitude Z u)) *
                    (B.transmission hm * Ch) ^ 2 ∧ 0 < Γ u) ∧
                PairMassProfileLimit
                  (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n))
                  Γ B.outerRate E t L ψ δ σ ∧
                (δ = 0 → σ = -1 → ∀ n,
                  massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) =
                    massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0))

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 4096 in
theorem exists_pair_packet_mass_response (B : Background)
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
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop) (δ σ : ℝ)
    (htop₂ : Tendsto (fun n => t n + δ * L n) atTop atTop)
    (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    B.PairPacketMassResponse {
      tail := h, radius := r, upper := H, lower := Hlo, deviation := dH,
      rate_pos := B.innerRate_pos.trans hks, upper_nonneg := hH, lower_pos := hHlo,
      deviation_nonneg := hdH, deviation_lt := hdHR, tail_continuous := hc,
      tail_bound := hb, tail_lower := hlo, radius_continuous := hrc, radius_lower := hrb,
      radius_initial := hrinit, radius_derivative := hrd, radius_decay := hrdec }
      hp ψ E t L δ σ ℓ Ucap := by
  have hh := B.exists_finite_packet_mass_response hp hpfin hcrit hks hl hH hHlo hdH hdHR
    hc hb hlo hrc hrb hrinit hrd hrdec hψ hcomp hpos hsupp
    (![1, σ] : Fin 2 → ℝ) (fun _ => E) (fun _ => hE)
    ![t, fun n => t n + δ * L n] (fun _ => L) (fun _ => hL)
    (Fin.forall_fin_two.2 ⟨htop, htop₂⟩) (fun _ => hLtop) ℓ Ucap hUcap
  obtain ⟨P, hP0, hformula, hprimitive, U, hU, hUR, hcap, hf, hm, X, hX, hfirst, hflux, hwave,
    hfloor, hcompat, hfinite, hInitial, hbounded, hzero, χ, hχ, hresponse⟩ := hh
  have hP (n : ℕ) (hn : n ≠ 0) (x : ℝ) : P n x =
      Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) *
        (ψ ((x - t n) / L n) + σ * ψ ((x - t n) / L n - δ)) := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, one_mul, packet_pair_sum_eq (hL n)] using hformula n hn x
  have hz (hδ : δ = 0) (hσ : σ = -1) (n : ℕ) : P n = 0 := by
    by_cases hn : n = 0
    · simpa only [hn] using hP0
    · ext x
      simp [hP n hn, hδ, hσ]
  obtain ⟨Φ, _Φ', hΦ, _hΦ', _hdΦ, _hiΦ, _hiΦ', hMΦ⟩ :=
    smooth_packet_shape hψ hcomp (hpos (1 / 2) (by norm_num)).ne'
  have hM : 0 < ∫ y, ψ y ^ 2 := by simpa only [hΦ] using hMΦ
  refine ⟨P, hP0, hP, hprimitive, U, hU, hUR, hcap, hf, hm, X, hX, hfirst, hflux, hwave,
    hfloor, hcompat, hfinite, hInitial, hbounded,
    fun hδ hσ n => hzero n (hz hδ hσ n), χ, hχ, ?_⟩
  intro ε hε hεU
  have : Nonempty (Icc ε U) := ⟨⟨U, hεU, le_rfl⟩⟩
  obtain ⟨hF, hweak, hr, hcompact, hmassFinite, ⟨Z, Nh, Γ, hZ, hNh, hsign, hmass⟩, hmzero⟩ :=
    hresponse ε hε hεU
  exact ⟨hF, hweak, hr, hcompact, hmassFinite, Z, Nh, Γ, hZ, hNh, hsign,
    hmass.pair_normalized hE hL hM (fun u => (hsign u).2.2.2.2) hP,
    fun hδ hσ n => hmzero n (hz hδ hσ n)⟩

theorem exists_late_pair_packet_mass_response (B : Background)
    {s l H Hlo : ℝ} {h : ℝ → ℝ} {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    (hcrit : B.innerRate = (1 - 1 / p.toReal) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hc : ContinuousOn h (Ici 0)) (hb : ∀ v ∈ Ici (0 : ℝ), ‖h v‖ ≤ H * Real.exp (-s * v))
    (hlo : ∀ v ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * v) ≤ h v)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop) (δ σ : ℝ)
    (htop₂ : Tendsto (fun n => t n + δ * L n) atTop atTop)
    (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ D : AdmissibleOutgoingData B s l,
      (∀ v ∈ Ici (0 : ℝ), D.tail v = h (v + T)) ∧
      D.upper = H * Real.exp (-s * T) ∧ D.lower = Hlo * Real.exp (-l * T) ∧
      B.PairPacketMassResponse D hp ψ E t L δ σ ℓ Ucap := by
  obtain ⟨T, hT, D, heq, hupper, hlower⟩ :=
    B.exists_admissible_late_data (B.innerRate_pos.trans hks) hH hHlo hc hb hlo
  refine ⟨T, hT, D, heq, hupper, hlower, ?_⟩
  exact B.exists_pair_packet_mass_response hp hpfin hcrit hks hl D.upper_nonneg D.lower_pos
    D.deviation_nonneg D.deviation_lt D.tail_continuous D.tail_bound D.tail_lower
    D.radius_continuous D.radius_lower D.radius_initial D.radius_derivative D.radius_decay
    hψ hcomp hpos hsupp hE t L hL htop hLtop δ σ htop₂ ℓ Ucap hUcap

end CauchyHorizon.Background
