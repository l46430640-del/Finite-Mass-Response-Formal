import CauchyHorizon.Characteristic.PairPacketMass
import CauchyHorizon.Analysis.PacketInterference

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction ENNReal ContDiff

namespace CauchyHorizon.Tests

-- Both time ranges use the fixed component energy, including overlapping packets.
example {E L : ℝ} (hE : 0 ≤ E) (hL : 0 < L)
    (ψ : ℝ → ℝ) (hM : 0 < ∫ z, ψ z ^ 2) (t δ σ y : ℝ) :
    let P := fun x => Real.sqrt (E / ((∫ z, ψ z ^ 2) * L)) *
      (ψ ((x - t) / L) + σ * ψ ((x - t) / L - δ))
    (∫ x in Iic y, P x ^ 2) = 2 * E * packetPairCumulative ψ δ σ ((y - t) / L) ∧
    (∫ x, P x ^ 2) = 2 * E * packetPairTotal ψ δ σ :=
  packet_pair_integrals hE hL ψ hM t δ σ y

-- Opposite coincident packets vanish at every level, including the terminal energy.
example (ψ : ℝ → ℝ) (y : ℝ) :
    packetPairCumulative ψ 0 (-1) y = 0 ∧ packetPairTotal ψ 0 (-1) = 0 :=
  packetPairCumulative_opposite ψ y

-- Equal coincident packets have four times one component's energy, so G(infinity)=2.
example (ψ : ℝ → ℝ) (hM : 0 < ∫ z, ψ z ^ 2) (y : ℝ) :
    packetPairCumulative ψ 0 1 y = 2 * packetCumulative ψ y ∧
      packetPairTotal ψ 0 1 = 2 := by
  simp only [packetPairCumulative, packetPairTotal, packetCumulative, sub_zero, one_mul]
  simp_rw [show ∀ z, (ψ z + ψ z) ^ 2 = 4 * ψ z ^ 2 from fun z => by ring]
  rw [integral_const_mul, integral_const_mul]
  constructor <;> field_simp [ne_of_gt hM] <;> ring

-- A nonnegative separation automatically supplies the second escaping support.
example {t L : ℕ → ℝ} (htop : Tendsto t atTop atTop) (hL : ∀ n, 0 < L n)
    {δ : ℝ} (hδ : 0 ≤ δ) : Tendsto (fun n => t n + δ * L n) atTop atTop := by
  apply tendsto_atTop.2
  intro R
  filter_upwards [(tendsto_atTop.1 htop) R] with n hn
  exact hn.trans (le_add_of_nonneg_right (mul_nonneg hδ (hL n).le))

-- The plotted overlap produces strict enhancement and suppression for every allowed positive shape.
example {ψ : ℝ → ℝ} (hc : Continuous ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) :
    1 < packetPairTotal ψ (1 / 4) 1 ∧ 0 ≤ packetPairTotal ψ (1 / 4) (-1) ∧
      packetPairTotal ψ (1 / 4) (-1) < 1 :=
  packetPairTotal_strict_overlap hc hcomp hpos hsupp (by norm_num) (by norm_num)

-- The plotted separated pair has the same terminal normalization for either relative sign.
example {ψ : ℝ → ℝ} (hc : Continuous ψ) (hcomp : HasCompactSupport ψ)
    (hM : 0 < ∫ z, ψ z ^ 2) (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0) :
    packetPairTotal ψ (5 / 4) 1 = 1 ∧ packetPairTotal ψ (5 / 4) (-1) = 1 := by
  constructor <;> rw [packetPairTotal_separated hc hcomp hM hsupp (by norm_num)] <;> norm_num

-- Strict leading bounds give one eventual bound for all actual terminal masses on the compact interval.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {M : ℕ → ℝ → C(K, ℝ)} {Γ : C(K, ℝ)} {a E δ σ A C : ℝ} {t L : ℕ → ℝ}
    {ψ : ℝ → ℝ} (hprofile : PairMassProfileLimit M Γ a E t L ψ δ σ)
    (hA : A < packetPairTotal ψ δ σ) (hC : packetPairTotal ψ δ σ < C) :
    ∃ Mh : ℕ → C(K, ℝ), (∀ n, Tendsto (M n) atTop (𝓝 (Mh n))) ∧
      ∀ᶠ n in atTop, ∀ u, A < (Mh n - Mh 0) u / (2 * E * Γ u) ∧
        (Mh n - Mh 0) u / (2 * E * Γ u) < C := by
  obtain ⟨_T, _hT, Mh, hMh, herr⟩ := hprofile
  let d := min (packetPairTotal ψ δ σ - A) (C - packetPairTotal ψ δ σ)
  have hd : 0 < d := lt_min (sub_pos.2 hA) (sub_pos.2 hC)
  refine ⟨Mh, hMh, ?_⟩
  filter_upwards [herr d hd] with n hn
  intro u
  have he := abs_lt.1 (hn.2 u)
  have hleft : d ≤ packetPairTotal ψ δ σ - A := min_le_left _ _
  have hright : d ≤ C - packetPairTotal ψ δ σ := min_le_right _ _
  constructor <;> linarith

-- One sequence index works for every late time and every point of the compact interval.
example {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {M : ℕ → ℝ → C(K, ℝ)} {Γ : C(K, ℝ)} {a E δ σ : ℝ} {t L : ℕ → ℝ}
    {ψ : ℝ → ℝ} {P : ℕ → ℝ → ℝ}
    (hprofile : MassProfileLimit M Γ a (fun _ => 0) P)
    (hE : 0 < E) (hL : ∀ n, 0 < L n) (hM : 0 < ∫ z, ψ z ^ 2)
    (hΓ : ∀ u, 0 < Γ u)
    (hP : ∀ n, n ≠ 0 → ∀ x, P n x = Real.sqrt (E / ((∫ z, ψ z ^ 2) * L n)) *
      (ψ ((x - t n) / L n) + σ * ψ ((x - t n) / L n - δ))) :
    ∃ T : ℝ, 0 ≤ T ∧ ∃ Mh : ℕ → C(K, ℝ),
      (∀ n, Tendsto (M n) atTop (𝓝 (Mh n))) ∧
      ∀ d > (0 : ℝ), ∀ᶠ n in atTop,
        (∀ v, T ≤ v → ∀ u, |(M n v - M 0 v) u / (2 * E * Γ u) -
          packetPairCumulative ψ δ σ ((a * v - t n) / L n)| < d) ∧
        ∀ u, |(Mh n - Mh 0) u / (2 * E * Γ u) - packetPairTotal ψ δ σ| < d :=
  hprofile.pair_normalized hE hL hM hΓ hP

-- Exact equality of the mass functions also fixes their actual horizon limits.
example {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {M : ℕ → ℝ → C(K, ℝ)} {Γ : C(K, ℝ)} {a E δ σ : ℝ} {t L : ℕ → ℝ}
    {ψ : ℝ → ℝ} (hprofile : PairMassProfileLimit M Γ a E t L ψ δ σ)
    (hz : ∀ n, M n = M 0) :
    ∃ Mh : ℕ → C(K, ℝ), (∀ n, Tendsto (M n) atTop (𝓝 (Mh n))) ∧ ∀ n, Mh n = Mh 0 := by
  obtain ⟨_T, _hT, Mh, hMh, _herr⟩ := hprofile
  refine ⟨Mh, hMh, fun n => tendsto_nhds_unique ?_ (hMh 0)⟩
  simpa only [hz n] using hMh n

-- The pair law, cancellation and weak extensions use the same physical solution and coordinate.
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
    (δ σ : ℝ) (hδ : 0 ≤ δ) (ℓ Ucap : ℝ) (hUcap : 0 < Ucap) :
    let hi := horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb
    let hr0 := fun v => ((sub_pos.2 hdHR).trans_le (hrb v)).ne'
    ∃ P : ℕ → ℝ →ᵇ ℝ, P 0 = 0 ∧
      (∀ n, n ≠ 0 → ∀ x, P n x = Real.sqrt (E / ((∫ y, ψ y ^ 2) * L n)) *
        (ψ ((x - t n) / L n) + σ * ψ ((x - t n) / L n - δ))) ∧
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
          (δ = 0 → σ = -1 → ∀ n (V : Ici (0 : ℝ)), X n V = X 0 V) ∧
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
                PairMassProfileLimit
                  (fun n => massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n))
                  Γ B.outerRate E t L ψ δ σ ∧
                (δ = 0 → σ = -1 → ∀ n,
                  massRow hε.le B.charge B.cosmological (X n) (ν n) (hr n) =
                    massRow hε.le B.charge B.cosmological (X 0) (ν 0) (hr 0)) := by
  have htop₂ : Tendsto (fun n => t n + δ * L n) atTop atTop := by
    apply tendsto_atTop.2
    intro R
    filter_upwards [(tendsto_atTop.1 htop) R] with n hn
    exact hn.trans (le_add_of_nonneg_right (mul_nonneg hδ (hL n).le))
  have hh := B.exists_pair_packet_mass_response (p := 4) le_rfl (by norm_num)
    (by norm_num; exact hcrit) hks hl hH hHlo hdH hdHR hc hb hlo hrc hrb hrinit hrd hrdec
    hψ hcomp hpos hsupp hE t L hL htop hLtop δ σ htop₂ ℓ Ucap hUcap
  obtain ⟨P, hP0, hformula, _hprimitive, U, hU, hUR, hcap, hf, _hm, X, hX, hEquations, hFlux, hWave,
    _hfloor, _hcompat, _hfinite, hInitial, hbounded, hzero, χ, hχ, hresponse⟩ := hh
  refine ⟨P, hP0, hformula, U, hU, hUR, hcap, hf, X, hX, hEquations, hFlux, hWave, hInitial, hbounded,
    hzero, χ, hχ, fun ε hε hεU => ?_⟩
  obtain ⟨_hF, hweak, hr, hcompact, hmassFinite, _Z, _Nh, Γ, _hZ, _hNh, hsign, hpair, hmzero⟩ :=
    hresponse ε hε hεU
  exact ⟨hweak, hr, hcompact, hmassFinite, Γ, fun u => (hsign u).2.2.2.2, hpair, hmzero⟩

end CauchyHorizon.Tests
