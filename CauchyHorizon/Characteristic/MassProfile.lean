import CauchyHorizon.Characteristic.MassResponse

/-! The cumulative profile from minus infinity and its actual geometric coefficient. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

def MassProfileLimit {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (M : ℕ → ℝ → C(K, ℝ)) (Γ : C(K, ℝ)) (a : ℝ) (ℓ : ℕ → ℝ) (P : ℕ → ℝ → ℝ) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧ ∃ Z : ℕ → C(K, ℝ), (∀ n, Tendsto (M n) atTop (𝓝 (Z n))) ∧
    ∀ d > (0 : ℝ), ∀ᶠ n in atTop,
      (∀ t, T ≤ t → ‖M n t - M 0 t - (∫ s in Iic (a * t + ℓ n), P n s ^ 2) • Γ‖ < d) ∧
      ‖Z n - Z 0 - (∫ s, P n s ^ 2) • Γ‖ < d

def RadiationMassProfile {U ε : ℝ} (hε : 0 ≤ ε) (k a c e Λ : ℝ)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (n : ℕ) → (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)))
    (hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0)
    (ℓ : ℕ → ℝ) (P : ℕ → ℝ → ℝ) : Prop :=
  ∃ Z : C(Icc ε U, WaveVector), ∃ Nh Γ : C(Icc ε U, ℝ),
    Tendsto (renormalizedWaveRow hε k (X 0)) atTop (𝓝 Z) ∧
    Tendsto (scalarBoundaryRow hε (N 0)) atTop (𝓝 Nh) ∧
    (∀ u, 0 < Z u 0 ∧ 0 < waveAmplitude Z u ∧ Nh u < 0 ∧
      Γ u = (-2 * Nh u / (a * waveAmplitude Z u)) * c ^ 2 ∧ 0 < Γ u) ∧
    MassProfileLimit (fun n => massRow hε e Λ (X n) (N n) (hr n)) Γ a ℓ P

theorem mass_profile_limit {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {C M : ℕ → ℝ → C(K, ℝ)} {Q : C(K, ℝ)} {a c : ℝ} {ℓ m : ℕ → ℝ} {P : ℕ → ℝ → ℝ}
    (ha : 0 < a)
    (hresponse : MassResponseLimit C (fun n t => ContinuousMap.const K (c * P n (a * t + ℓ n))) M)
    (hQ : Tendsto (C 0) atTop (𝓝 Q)) (hP : ∀ n, Integrable (fun s => P n s ^ 2))
    (hfront : Tendsto (fun n => m n - ℓ n) atTop atTop)
    (hsupport : ∀ n s, s ≤ m n → P n s = 0) :
    MassProfileLimit M ((c ^ 2 / a) • Q) a ℓ P := by
  obtain ⟨T, hT, Q', hQ', Z, hZ, hlimit⟩ := hresponse
  have hQQ : Q' = Q := tendsto_nhds_unique hQ' hQ
  subst Q'
  refine ⟨T, hT, Z, hZ, ?_⟩
  intro d hd
  filter_upwards [hlimit d hd, (tendsto_atTop.1 hfront) (a * T)] with n hn hmn
  have hzero (s : ℝ) (hs : s ≤ a * T + ℓ n) : P n s ^ 2 = 0 := by
    rw [hsupport n s (by linarith only [hs, hmn])]
    norm_num
  have hleft : (∫ s in Iic (a * T + ℓ n), P n s ^ 2) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun s hs => hzero s hs)
  have hleft' : (∫ s in Iio (a * T + ℓ n), P n s ^ 2) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun s hs => hzero s hs.le)
  have hfinite (t : ℝ) : (∫ s in a * T + ℓ n..a * t + ℓ n, P n s ^ 2) =
      ∫ s in Iic (a * t + ℓ n), P n s ^ 2 := by
    have hh := intervalIntegral.integral_Iic_sub_Iic
      ((hP n).integrableOn (s := Iic (a * T + ℓ n))) ((hP n).integrableOn (s := Iic (a * t + ℓ n)))
    simpa only [hleft, sub_zero] using hh.symm
  have hterminal : (∫ s in Ici (a * T + ℓ n), P n s ^ 2) = ∫ s, P n s ^ 2 := by
    have hh := intervalIntegral.integral_Iio_add_Ici
      ((hP n).integrableOn (s := Iio (a * T + ℓ n))) ((hP n).integrableOn (s := Ici (a * T + ℓ n)))
    simpa only [hleft', zero_add] using hh
  constructor
  · intro t ht
    have hh := hn.1 t ht
    rw [(mass_profile_integrals ha Q (P n) c (ℓ n) T t).1, hfinite t] at hh
    simpa only [smul_smul, mul_comm (∫ s in Iic (a * t + ℓ n), P n s ^ 2) (c ^ 2 / a)] using hh
  · have hh := hn.2
    rw [(mass_profile_integrals ha Q (P n) c (ℓ n) T T).2, hterminal] at hh
    simpa only [smul_smul, mul_comm (∫ s, P n s ^ 2) (c ^ 2 / a)] using hh

theorem radiation_mass_profile {U ε k a c e Λ : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    (hc : c ≠ 0)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (n : ℕ) → (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)))
    (hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0)
    (ℓ m : ℕ → ℝ) (P : ℕ → ℝ → ℝ) (Z : C(Icc ε U, WaveVector)) (Nh : C(Icc ε U, ℝ))
    (hresponse : RadiationMassResponse hε k c e Λ X N hr (fun n t => P n (a * t + ℓ n)))
    (hZ : Tendsto (renormalizedWaveRow hε k (X 0)) atTop (𝓝 Z))
    (hN : Tendsto (scalarBoundaryRow hε (N 0)) atTop (𝓝 Nh))
    (hR : ∀ u, 0 < Z u 0) (hNh : ∀ u, Nh u < 0)
    (hP : ∀ n, Integrable (fun s => P n s ^ 2))
    (hfront : Tendsto (fun n => m n - ℓ n) atTop atTop)
    (hsupport : ∀ n s, s ≤ m n → P n s = 0) :
    RadiationMassProfile hε k a c e Λ X N hr ℓ P := by
  let Q := waveMassCoefficient (Nh, Z)
  let Γ := (c ^ 2 / a) • Q
  have hQ : Tendsto (massCoefficientRow hε k (X 0) (N 0)) atTop (𝓝 Q) :=
    waveMassCoefficient.continuous.tendsto (Nh, Z) |>.comp (hN.prodMk_nhds hZ)
  refine ⟨Z, Nh, Γ, hZ, hN, ?_, mass_profile_limit ha hresponse hQ hP hfront hsupport⟩
  intro u
  have hA : 0 < waveAmplitude Z u := Real.exp_pos _
  have hΓ : Γ u = (-2 * Nh u / (a * waveAmplitude Z u)) * c ^ 2 := by
    change (c ^ 2 / a) * (-2 * (Nh u * Real.exp (-Z u 2))) =
      (-2 * Nh u / (a * Real.exp (Z u 2))) * c ^ 2
    rw [Real.exp_neg]
    field_simp
  refine ⟨hR u, hA, hNh u, hΓ, ?_⟩
  rw [hΓ]
  exact mul_pos (div_pos (by linarith only [hNh u]) (mul_pos ha hA)) (sq_pos_of_ne_zero hc)

end CauchyHorizon
