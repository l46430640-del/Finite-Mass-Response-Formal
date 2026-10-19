import CauchyHorizon.Reduced.ScalarRegularity

/-! The radiation increment estimate also applies to actual transverse derivatives. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem radiation_transport_majorant {V k q ρ N Z₀ Z₁ : ℝ} (hV : 0 ≤ V)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (r ν ψ M : C(Icc 0 V, ℝ))
    (T b : Icc 0 V) (hTb : T ≤ b)
    (hseg : Z₁ = Z₀ + ∫ w in (T : ℝ)..b,
      -ν (projIcc 0 V hV w) * ψ (projIcc 0 V hV w))
    (hr : ∀ v ∈ Icc T b, ρ ≤ r v)
    (hν : ∀ v ∈ Icc T b, |ν v| ≤ N * Real.exp (-q * ((v : ℝ) - T)))
    (hM : ∀ v ∈ Icc T b, Real.exp (k * v) * |r v * ψ v| ≤ M v) :
    Real.exp (k * T) * |Z₁| ≤ Real.exp (k * T) * |Z₀| +
      N / ρ * ∫ w in (T : ℝ)..b, Real.exp (-(q + k) * (w - T)) * M (projIcc 0 V hV w) := by
  let F := fun w => -ν (projIcc 0 V hV w) * ψ (projIcc 0 V hV w)
  let K := fun w => Real.exp (-(q + k) * (w - T)) * M (projIcc 0 V hV w)
  have hKc : Continuous K := by fun_prop
  have hbnd : ∀ w ∈ Icc (T : ℝ) b, ‖Real.exp (k * T) * F w‖ ≤ N / ρ * K w := by
    intro w hw
    have hwV : w ∈ Icc 0 V := ⟨T.property.1.trans hw.1, hw.2.trans b.property.2⟩
    let v : Icc 0 V := ⟨w, hwV⟩
    have hv : v ∈ Icc T b := hw
    have hψ : |ψ v| ≤ Real.exp (-k * w) * M v / ρ := by
      apply (le_div_iff₀ hρ).2
      have hh := mul_le_mul_of_nonneg_left (hM v hv) (Real.exp_pos (-k * w)).le
      have he : Real.exp (-k * w) * Real.exp (k * w) = 1 := by
        rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
      change Real.exp (-k * w) * (Real.exp (k * w) * |r v * ψ v|) ≤ _ at hh
      rw [← mul_assoc, he, one_mul, abs_mul, abs_of_pos (hρ.trans_le (hr v hv))] at hh
      nlinarith only [hh, mul_le_mul_of_nonneg_right (hr v hv) (abs_nonneg (ψ v))]
    simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_neg,
      projIcc_of_mem hV hwV]
    calc
      _ ≤ Real.exp (k * T) * ((N * Real.exp (-q * (w - T))) * (Real.exp (-k * w) * M v / ρ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hν v hv) hψ (abs_nonneg _)
          (mul_nonneg hN (Real.exp_pos _).le)) (Real.exp_pos _).le
      _ = N / ρ * K w := by
        have he : Real.exp (k * T) * Real.exp (-q * (w - T)) * Real.exp (-k * w) =
            Real.exp (-(q + k) * (w - T)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        dsimp only [K]
        rw [projIcc_of_mem hV hwV]
        calc
          _ = (N / ρ * M v) *
              (Real.exp (k * T) * Real.exp (-q * (w - T)) * Real.exp (-k * w)) := by ring
          _ = _ := by rw [he]; ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (show (T : ℝ) ≤ b from hTb)
    (Filter.Eventually.of_forall (fun w hw => hbnd w (Ioc_subset_Icc_self hw)))
    (hKc.const_mul (N / ρ) |>.intervalIntegrable (μ := volume) T b)
  rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), intervalIntegral.integral_const_mul] at hi
  have hh := mul_le_mul_of_nonneg_left (abs_add_le Z₀ (∫ w in (T : ℝ)..b, F w))
    (Real.exp_pos (k * T)).le
  rw [← hseg, mul_add] at hh
  exact hh.trans (add_le_add_right hi _)

theorem IsWaveIntegral.transverse_radiation_majorant
    {U V e Λ k q ρ N : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (M : C(Icc 0 V, ℝ))
    (u : Icc 0 U) (hu : 0 < (u : ℝ)) (T b : Icc 0 V) (hTb : T ≤ b) :
    let ν := radialNuField hV e Λ zIn x.1 hx.choose
    let Z := fun v => x.1 u v 0 * derivWithin (fun t => intervalExtension hU x.1 t v 1) (Icc 0 U) u
    ν u T < 0 → (∀ v ∈ Icc T b, ρ ≤ x.1 u v 0) →
    (∀ v ∈ Icc T b, |ν u v| ≤ N * (-ν u T) * Real.exp (-q * ((v : ℝ) - T))) →
    (∀ v ∈ Icc T b, Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v) →
      Real.exp (k * T) * |Z b| ≤ Real.exp (k * T) * |Z T| +
        N * (-ν u T) / ρ * ∫ w in (T : ℝ)..b,
          Real.exp (-(q + k) * (w - T)) * M (projIcc 0 V hV w) := by
  intro ν Z hn hr hν hM
  let F := fun w => -ν u (projIcc 0 V hV w) * x.2.1 u (projIcc 0 V hV w) 1
  have hFc : Continuous F := by fun_prop
  have hZ (v : Icc 0 V) : Z v = zIn u 0 * f u + scalarTransportCorrection hV ν x.2.1 u v := by
    have hd := hx.scalar_hasDerivWithinAt_of_continuous hzin hinu hc hif ⟨hu, u.property.2⟩ v
    have hdd := hd.derivWithin ((uniqueDiffOn_Icc (hu.trans_le u.property.2)) _ u.property)
    change x.1 u v 0 * derivWithin _ _ _ = _
    rw [hdd, mul_div_cancel₀ _ (hx.choose u v)]
  have hseg : Z b = Z T + ∫ w in (T : ℝ)..b, F w := by
    rw [hZ, hZ]
    change zIn u 0 * f u + (∫ w in (0 : ℝ)..b, F w) =
      zIn u 0 * f u + (∫ w in (0 : ℝ)..T, F w) + ∫ w in (T : ℝ)..b, F w
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable (0 : ℝ) T) (hFc.intervalIntegrable (T : ℝ) b)]
    ring
  exact radiation_transport_majorant hV hρ (mul_nonneg hN (neg_pos.2 hn).le)
    ⟨fun v => x.1 u v 0, by fun_prop⟩ (ν u) ⟨fun v => x.2.1 u v 1, by fun_prop⟩ M
      T b hTb hseg hr hν hM

end CauchyHorizon
