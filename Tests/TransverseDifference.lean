import CauchyHorizon.Characteristic.TransverseDifference
import CauchyHorizon.Characteristic.InnerTransport
import CauchyHorizon.Characteristic.AuxiliaryRadiationHalfline
import CauchyHorizon.Characteristic.AuxiliaryRadiationTail
import CauchyHorizon.Radial.InnerRadiationCoefficient
import CauchyHorizon.Characteristic.GammaTransmissionTail

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CauchyHorizon.Tests

-- The row retains the signed difference before taking its spatial norm.
example {U V k : ℝ} (x : WaveState U V) (z w : C(Icc (0 : ℝ) V, Icc (0 : ℝ) U))
    (b : Icc (0 : ℝ) V) (u : Icc (0 : ℝ) U) (hu : u ∈ Icc (z b) (w b)) :
    transverseRadiationRows k x z w b u = Real.exp (k * b) *
      (x.1 u b 0 * x.2.1 u b 1 - x.1 (z b) b 0 * x.2.1 (z b) b 1) := by
  simp only [transverseRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
    min_eq_left hu.2, max_eq_right hu.1]

-- A collapsed spatial interval has zero difference even for nonzero radiation.
example {U V k : ℝ} (x : WaveState U V) (z : C(Icc (0 : ℝ) V, Icc (0 : ℝ) U)) :
    transverseRadiationRows k x z z = 0 := by
  ext b u
  simp only [transverseRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
    max_eq_left (min_le_right u (z b)), sub_self, mul_zero, ContinuousMap.zero_apply]

-- Independent source and observation times need no feedback absorption or earlier row ordering.
example {U V R e Λ φ₀ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x)
    (l b₀ : Icc 0 V) (hl₀ : l ≤ b₀)
    (z w : C(Icc (0 : ℝ) V, Icc (0 : ℝ) U)) (hzw : ∀ b, b₀ ≤ b → z b ≤ w b)
    (A : C(Icc 0 V, ℝ)) (hA0 : ∀ v, 0 ≤ A v) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) x.1 hx.choose
    (∀ (b : Icc 0 V), b₀ ≤ b → ∀ (u : Icc 0 U) (hzu : z b < u), u ≤ w b →
      ∃ T : C(Icc (z b : ℝ) u, Icc 0 V),
        let τ := fun t => T (projIcc (z b : ℝ) u hzu.le t)
        τ (z b) = b ∧ l ≤ τ u ∧ (∀ t ∈ Icc (z b : ℝ) u, τ t ≤ b) ∧
        (∀ t ∈ Icc (z b : ℝ) u, ν (projIcc 0 U hU t) (τ t) < 0) ∧
        (∀ t ∈ Icc (z b : ℝ) u, -(4 : ℝ) ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧
          x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0) ∧
        (∀ t ∈ Ioo (z b : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
          (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) ∧
        (∀ t ∈ Icc (z b : ℝ) u, ∀ v ∈ Icc (τ t) b, 1 ≤ x.1 (projIcc 0 U hU t) v 0) ∧
        (∀ t ∈ Icc (z b : ℝ) u, ∀ v ∈ Icc (τ t) b,
          |ν (projIcc 0 U hU t) v| ≤ 4 * (-ν (projIcc 0 U hU t) (τ t)) *
            Real.exp (-(2 * 1) * ((v : ℝ) - τ t))) ∧
        (∀ t ∈ Icc (z b : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
          4 * Real.exp (-(2 * 1) * ((b : ℝ) - τ t))) ∧
        (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z b : ℝ) u →
          Real.exp (1 * τ t) * |x.1 (projIcc 0 U hU t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
            (-ν (projIcc 0 U hU t) (τ t)) * A (τ t))) →
      let M := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 V) U) (fun _ => hU) 0 1 0 x
      (∫ t in (b₀ : ℝ)..V, ‖transverseRadiationRows 1 x z w (projIcc 0 V hV t)‖ ^ 2) ≤
        512 * (∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2) +
          512 * ∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  intro ν hchart M
  have hh := (hx.transverse_radiation_difference_energy (k := 1) (ρ := 1) (N := 4) (L := 4) (Lᵧ := 4)
    hU hV hUR le_rfl hf (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    l b₀ hl₀ z w hzw A hA0 hchart).2
  norm_num at hh
  exact hh

section Restart

variable {M e Λ U V k : ℝ} {h r : ℝ → ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
  {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)

-- A one-sided conformal remainder may be negative; no absolute-value premise is needed.
example (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    3 / 4 ≤ -Real.exp (x.1 u b 2) / (4 * ν u b) →
    x.1 u b 2 - x.1 u a 2 + 2 * k * ((b : ℝ) - a) ≤ -1 →
    (∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ 0 →
      |ν u b| ≤ (2 * Real.exp (-1)) * (-ν u a) * Real.exp (-2 * k * ((b : ℝ) - a)) ∧
      |x.2.1 u b 0| ≤ (Real.exp (-1) * (-x.2.1 u a 0)) * Real.exp (-2 * k * ((b : ℝ) - a)) := by
  intro ν hκ hR hJ
  simpa only [add_zero] using hx.inner_exact_transport_of_remainders
    hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u a b hab ha hκ hR hJ

-- Restarting subtracts two old remainders, while the optical budget is not doubled.
example (u : Icc 0 U) (a₀ a b : Icc 0 V) (h₀a : a₀ ≤ a) (hab : a ≤ b)
    (h₀ : x.2.1 u a₀ 0 < 0) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    3 / 4 ≤ -Real.exp (x.1 u b 2) / (4 * ν u b) →
    |x.1 u a 2 - x.1 u a₀ 2 + 2 * k * ((a : ℝ) - a₀)| ≤ 1 →
    |x.1 u b 2 - x.1 u a₀ 2 + 2 * k * ((b : ℝ) - a₀)| ≤ 1 →
    (∫ t in (a₀ : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ 1 / 16 →
      |ν u b| ≤ (2 * Real.exp 2) * (-ν u a) * Real.exp (-2 * k * ((b : ℝ) - a)) ∧
      |x.2.1 u b 0| ≤ (Real.exp (33 / 16) * (-x.2.1 u a 0)) * Real.exp (-2 * k * ((b : ℝ) - a)) := by
  intro ν hκ hRa hRb hJ
  simpa only [mul_one, show (2 : ℝ) + 1 / 16 = 33 / 16 by norm_num] using
    hx.inner_exact_transport_restart hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
      u a₀ a b h₀a hab h₀ hκ hRa hRb hJ

end Restart

-- The half-line difference agrees with the signed physical increment in every containing prefix.
example (B : Background) {U β Y L l b₀ : ℝ} (hU : 0 ≤ U)
    (X : (V : Ici (0 : ℝ)) → WaveState U V) (gY g A : ℝ → ℝ)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hhalf : AuxiliaryRadiationHalfline B hU X gY g β Y L l b₀ A) :
    ∃ D : C(ℝ, C(Icc (0 : ℝ) U, ℝ)), MemLp D 2 (volume.restrict (Ici b₀)) ∧
      ∀ (V : Ici (0 : ℝ)) (t : Icc 0 (V : ℝ)), b₀ ≤ t → ∀ u : Icc 0 U,
        projIcc 0 U hU (gY t) ≤ u → u ≤ projIcc 0 U hU (g ((t : ℝ) / (1 + β))) →
          D t u = Real.exp (B.innerRate * t) *
            ((X V).1 u t 0 * (X V).2.1 u t 1 -
              (X V).1 (projIcc 0 U hU (gY t)) t 0 * (X V).2.1 (projIcc 0 U hU (gY t)) t 1) := by
  obtain ⟨D, hD, hi, _⟩ := hhalf
  refine ⟨D, hi, ?_⟩
  intro V t ht u hzu huw
  rw [hD t ht u]
  simp only [min_eq_left huw, max_eq_right hzu, radiationRow_eq X hcompat V t.property.2,
    projIcc_of_mem V.property t.property, spatialRadiationRows, ContinuousMap.curry_apply,
    ContinuousMap.coe_mk, zero_mul, sub_zero]
  ring

-- Coincident moving endpoints give zero difference, without requiring zero total radiation.
example (B : Background) {U β Y L l b₀ : ℝ} (hU : 0 ≤ U)
    (X : (V : Ici (0 : ℝ)) → WaveState U V) (gY g A : ℝ → ℝ)
    (hhalf : AuxiliaryRadiationHalfline B hU X gY g β Y L l b₀ A)
    (heq : ∀ t ≥ b₀, gY t = g (t / (1 + β))) :
    ∃ D : C(ℝ, C(Icc (0 : ℝ) U, ℝ)), MemLp D 2 (volume.restrict (Ici b₀)) ∧
      ∀ t ≥ b₀, D t = 0 := by
  obtain ⟨D, hD, hi, _⟩ := hhalf
  refine ⟨D, hi, ?_⟩
  intro t ht
  ext u
  rw [hD t ht u]
  simp only [heq t ht, max_eq_left (min_le_right _ _), sub_self, ContinuousMap.zero_apply]

-- The tail index works for every eligible observation cutoff, including a zero coefficient.
example (B : Background) {U β Y l T₀ S Eprofile Etotal : ℝ} (hU : 0 ≤ U)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (gY g : ℕ → ℝ → ℝ)
    (htail : AuxiliaryRadiationTail B hU X gY g β Y 0 l T₀ S Eprofile Etotal) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, l ≤ T ∧ ∀ l' : ℝ, T ≤ l' →
      ∀ᶠ n : ℕ in atTop, ∀ b₀ : ℝ, max l' T₀ ≤ b₀ / (1 + β) → S ≤ b₀ →
        ∃ D : C(ℝ, C(Icc (0 : ℝ) U, ℝ)),
          (∀ t ≥ b₀, ∀ u : Icc (0 : ℝ) U,
            let z := projIcc 0 U hU (gY n t)
            let w := projIcc 0 U hU (g n (t / (1 + β)))
            D t u = radiationRow B.innerRate (X n) t (max z (min u w)) -
              radiationRow B.innerRate (X n) t z) ∧
          MemLp D 2 (volume.restrict (Ici b₀)) ∧
          (∫ t in Ici b₀, ‖D t‖ ^ 2) < ε := by
  intro ε hε
  obtain ⟨T, hlT, hT⟩ := htail ε hε
  refine ⟨T, hlT, ?_⟩
  intro l' hl'
  filter_upwards [hT l' hl'] with n hn
  intro b₀ hstart hS
  obtain ⟨D, hD, hiD, hE⟩ := hn b₀ hstart hS
  refine ⟨D, hD, hiD, ?_⟩
  simpa only [zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div, zero_add] using hE

-- The squared singular source coefficient vanishes at the inner endpoint.
example (B : Background) :
    Tendsto (fun Y => ((Y - B.inner) ^ 2 * B.criticalWeight Y / (-B.F Y)) ^ 2)
      (𝓝[>] B.inner) (𝓝 0) := by
  obtain ⟨C, _hC, hCbound⟩ := B.exists_inner_radiation_coefficient_bound
  have hlim : Tendsto (fun Y => C * (Y - B.inner)) (𝓝[>] B.inner) (𝓝 0) := by
    have hc : Continuous (fun Y => C * (Y - B.inner)) := by fun_prop
    simpa only [sub_self, mul_zero] using (hc.continuousAt (x := B.inner)).tendsto.mono_left
      (show 𝓝[>] B.inner ≤ 𝓝 B.inner from nhdsWithin_le_nhds)
  apply squeeze_zero' (Eventually.of_forall (fun Y => sq_nonneg _)) _ hlim
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds (show B.inner < (B.inner + B.event) / 2 by linarith only [B.inner_lt_event]))]
    with Y hY hcap
  exact hCbound Y ⟨hY, hcap.le⟩

-- The full residual can be made small below any fixed radius cap, with nonzero energy budgets.
example (B : Background) (hm : B.criticalExponent < 1) (L Ch Eprofile Etotal Yr ε : ℝ)
    (hYr : B.inner < Yr) (hε : 0 < ε) :
    ∃ Y ∈ Ioo B.inner Yr, B.innerTransmissionError hm L Ch Eprofile Etotal Y < ε := by
  obtain ⟨Y, hY, hcap, hsmall⟩ := ((show ∀ᶠ Y : ℝ in 𝓝[>] B.inner, B.inner < Y from
    self_mem_nhdsWithin).and ((eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hYr)).and
      ((B.inner_transmission_error_tendsto hm L Ch Eprofile Etotal).eventually_lt_const hε))).exists
  exact ⟨Y, ⟨hY, hcap⟩, hsmall⟩

-- One eventual sequence index controls every later observation cutoff on the same original curve.
example (B : Background) {U β c : ℝ} (hU : 0 ≤ U)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (g P : ℕ → ℝ → ℝ)
    (htail : RadiationGammaTransmissionTail B hU X g P β c) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧ ∀ᶠ n in atTop, ∀ b ≥ T,
      let F := fun t => radiationRow B.innerRate (X n) t
        (projIcc 0 U hU (g n (t / (1 + β)))) - c * P n t
      MemLp F 2 (volume.restrict (Ici b)) ∧ (∫ t in Ici b, F t ^ 2) < ε := by
  intro ε hε
  obtain ⟨T, hT, hn⟩ := htail ε hε
  refine ⟨T, hT, ?_⟩
  filter_upwards [hn] with n hn
  intro b hb F
  have hsub : Ici b ⊆ Ici T := Ici_subset_Ici.2 hb
  refine ⟨hn.1.mono_measure (Measure.restrict_mono hsub le_rfl), ?_⟩
  exact (setIntegral_mono_set ((memLp_two_iff_integrable_sq hn.1.1).1 hn.1)
    (Eventually.of_forall (fun t => sq_nonneg _))
    (Eventually.of_forall (fun _ ht => hsub ht))).trans_lt hn.2

end CauchyHorizon.Tests
