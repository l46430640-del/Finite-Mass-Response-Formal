import CauchyHorizon.Characteristic.FinitePacketMass

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction ENNReal ContDiff

namespace CauchyHorizon.Tests

-- The two-packet budget is unchanged by the relative sign.
example (P Q : ℝ →ᵇ ℝ) (hP : Integrable (fun x => P x ^ 2))
    (hQ : Integrable (fun x => Q x ^ 2)) {σ : ℝ} (hσ : |σ| = 1) :
    Integrable (fun x => (P x + σ * Q x) ^ 2) ∧
      (∫ x, (P x + σ * Q x) ^ 2) ≤
        (Real.sqrt (∫ x, P x ^ 2) + Real.sqrt (∫ x, Q x ^ 2)) ^ 2 := by
  have hf : ∀ i : Fin 2, Integrable (fun x => (![P, Q] i) x ^ 2) :=
    Fin.forall_fin_two.2 ⟨hP, hQ⟩
  have hh := finite_sum_squared_integral (Finset.univ : Finset (Fin 2)) ![1, σ] ![P, Q]
    (fun i _ => hf i)
  simpa [Fin.sum_univ_two, hσ] using hh

-- The quadratic comparison retains the interference integral with its exact sign.
example (P Q : ℝ →ᵇ ℝ) (hP : Integrable (fun x => P x ^ 2))
    (hQ : Integrable (fun x => Q x ^ 2)) (σ : ℝ) :
    (∫ x, (P x + σ * Q x) ^ 2) = (∫ x, P x ^ 2) +
      2 * σ * (∫ x, P x * Q x) + σ ^ 2 * (∫ x, Q x ^ 2) := by
  have hmP := (memLp_two_iff_integrable_sq P.continuous.aestronglyMeasurable).2 hP
  have hmQ := (memLp_two_iff_integrable_sq Q.continuous.aestronglyMeasurable).2 hQ
  have hi : Integrable (fun x => P x * Q x) := hmP.integrable_mul hmQ
  simp_rw [show ∀ x, (P x + σ * Q x) ^ 2 =
    P x ^ 2 + (2 * σ) * (P x * Q x) + σ ^ 2 * Q x ^ 2 from fun _ => by ring]
  have hsum : Integrable (fun x => P x ^ 2 + (2 * σ) * (P x * Q x)) :=
    hP.add (hi.const_mul (2 * σ))
  rw [integral_add hsum (hQ.const_mul (σ ^ 2)),
    integral_add hP (hi.const_mul (2 * σ)), integral_const_mul, integral_const_mul]

-- Empty finite sums have zero energy; the analytic budget lemma has no nonemptiness premise.
example : Integrable (fun _ : ℝ => (0 : ℝ)) ∧ (0 : ℝ) ≤ 0 := by
  simpa only [Finset.sum_empty, zero_pow (by decide : 2 ≠ 0), integral_zero] using
    finite_sum_squared_integral (∅ : Finset Unit) (fun _ => 1)
    (fun _ => (0 : ℝ →ᵇ ℝ)) (by simp)

-- Equal opposite packets construct identically zero data, not just a zero limiting energy.
example {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    {E : ℝ} (hE : 0 < E) (t L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (htop : Tendsto t atTop atTop) (hLtop : Tendsto L atTop atTop) (ℓ : ℝ) :
    ∃ P : ℕ → ℝ →ᵇ ℝ, (∀ n, P n = 0) ∧
      ∀ n, n ≠ 0 → ∀ x, P n x =
        Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) * ψ ((x - t n) / L n) -
        Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) * ψ ((x - t n) / L n) := by
  obtain ⟨_A, _Apt, _hA, _hApt, P, _Q, hP0, _hQ0, hf, _rest⟩ :=
    finite_packet_incoming_data (p := 4) le_rfl (by norm_num) hψ hcomp hpos hsupp
      (![1, -1] : Fin 2 → ℝ) (fun _ => E) (fun _ => hE) (fun _ => t) (fun _ => L)
      (fun _ => hL) (fun _ => htop) (fun _ => hLtop) ℓ
  have hz (n : ℕ) : P n = 0 := by
    by_cases hn : n = 0
    · simpa only [hn] using hP0
    · ext x
      simpa [Fin.sum_univ_two] using hf n hn x
  exact ⟨P, hz, fun n _ x => by simp [hz]⟩

-- Removing a fixed phase retains the same actual terminal traces and a single bound for all times.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {M : ℕ → ℝ → C(K, ℝ)} {Γ : C(K, ℝ)} {a ℓ : ℝ} {P : ℕ → ℝ →ᵇ ℝ}
    (h : MassProfileLimit M Γ a (fun _ => ℓ) (fun n => P n))
    (hi : ∀ n, Integrable (fun x => P n x ^ 2))
    (hs : Tendsto (fun n => ‖P n‖) atTop (𝓝 0)) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ Mh : ℕ → C(K, ℝ),
      (∀ n, Tendsto (M n) atTop (𝓝 (Mh n))) ∧
      ∀ d > (0 : ℝ), ∀ᶠ n in atTop,
        (∀ v, T ≤ v → ‖M n v - M 0 v - (∫ x in Iic (a * v), P n x ^ 2) • Γ‖ < d) ∧
        ‖Mh n - Mh 0 - (∫ x, P n x ^ 2) • Γ‖ < d := by
  simpa only [MassProfileLimit, add_zero] using h.remove_constant_phase hi hs

-- At p=4 the same finite-sum family carries the mass law, compactification and weak extensions.
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
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (c E : ι → ℝ) (hE : ∀ i, 0 < E i) (t L : ι → ℕ → ℝ)
    (hL : ∀ i n, 0 < L i n) (htop : ∀ i, Tendsto (t i) atTop atTop)
    (hLtop : ∀ i, Tendsto (L i) atTop atTop) (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    let hi := horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb
    let hr0 := fun v => ((sub_pos.2 hdHR).trans_le (hrb v)).ne'
    ∃ P : ℕ → ℝ →ᵇ ℝ, P 0 = 0 ∧
      (∀ n, n ≠ 0 → ∀ x, P n x = ∑ i, c i *
        (Real.sqrt (E i / ((∫ y, ψ y ^ 2) * L i n)) * ψ ((x - t i n) / L i n))) ∧
      ∃ U : ℝ, ∃ hU : 0 < U, ∃ hUR : U < r 0, U ≤ Ucap ∧
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
          ∃ χ : ℕ → ℝ → ℝ,
          (∀ n, IsRegularTimeCoordinate (anchoringLapse hU.le (X n)) 0 (χ n)) ∧
          ∀ ε (hε : 0 < ε) (hεU : ε ≤ U),
            (ε < U → ∀ n, ∃ Tw : ℝ, 0 ≤ Tw ∧ ∀ u₀ ∈ Ioo ε U,
              HasLocalSphericalWeakExtension hε.le hεU B.charge B.cosmological
                (X n) (χ n) Tw u₀) ∧
            ∃ hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0,
              let ν := fun n (V : Ici (0 : ℝ)) => radialNuField V.property B.charge B.cosmological
                (incomingWaveCurve hU.le hUR le_rfl (hf n) (horizonPhi h r 0)) (X n V).1 (hr n V)
              HasCompactifiedGeometry hε.le B.innerRate X ν ∧
              (∀ v, 0 ≤ v → Tendsto
                (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) v)
                atTop (𝓝 (massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0) v))) ∧
              ∃ Γ : C(Icc ε U, ℝ), (∀ u, 0 < Γ u) ∧
                MassProfileLimit (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n))
                  Γ B.outerRate (fun _ => 0) (fun n => P n) := by
  have hh := B.exists_finite_packet_mass_response (p := 4) le_rfl (by norm_num)
    (by norm_num; exact hcrit) hks hl hH hHlo hdH hdHR hc hb hlo hrc hrb hrinit hrd hrdec
    hψ hcomp hpos hsupp c E hE t L hL htop hLtop ℓ Ucap hUcap
  obtain ⟨P, hP0, hformula, _hprimitive, U, hU, hUR, hcap, hf, hm, X, hX, hEquations, hFlux, hWave,
    _hfloor, _hcompat, _hfinite, hInitial, hbounded, _hzero, χ, hχ, hresponse⟩ := hh
  refine ⟨P, hP0, hformula, U, hU, hUR, hcap, hf, X, hX, hEquations, hFlux, hWave, hInitial, hbounded,
    χ, hχ, fun ε hε hεU => ?_⟩
  obtain ⟨_hF, hweak, hr, hcompact, hmassFinite, ⟨Z, Nh, Γ, _hZ, _hNh, hsign, hmass⟩, _hmzero⟩ :=
    hresponse ε hε hεU
  exact ⟨hweak, hr, hcompact, hmassFinite, Γ, fun u => (hsign u).2.2.2.2, hmass⟩

end CauchyHorizon.Tests
