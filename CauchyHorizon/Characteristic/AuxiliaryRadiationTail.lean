import CauchyHorizon.Characteristic.AuxiliaryRadiationHalfline
import CauchyHorizon.Radial.CriticalWeight

/-! Reference-subtracted matching controls the actual total-field source tail. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

def AuxiliaryRadiationTail (B : Background) {U : ℝ} (hU : 0 ≤ U)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (gY g : ℕ → ℝ → ℝ)
    (β Y L l T₀ S Eprofile Etotal : ℝ) : Prop :=
  let C := Real.exp (2 + 1 / 16) * (L * (Y - B.inner)) ^ 2
  let K := B.criticalWeight Y / (Real.exp (-1) * (-B.F Y) / B.outerRate)
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, l ≤ T ∧ ∀ l' : ℝ, T ≤ l' →
    ∀ᶠ n in atTop, ∀ b₀ : ℝ, max l' T₀ ≤ b₀ / (1 + β) → S ≤ b₀ →
      ∃ D : C(ℝ, C(Icc (0 : ℝ) U, ℝ)),
        (∀ t ≥ b₀, ∀ u : Icc (0 : ℝ) U,
          let z := projIcc 0 U hU (gY n t)
          let w := projIcc 0 U hU (g n (t / (1 + β)))
          D t u = radiationRow B.innerRate (X n) t (max z (min u w)) -
            radiationRow B.innerRate (X n) t z) ∧
        MemLp D 2 (volume.restrict (Ici b₀)) ∧
        (∫ t in Ici b₀, ‖D t‖ ^ 2) <
          6 * (C / ((B.inner / 2) * B.innerRate)) ^ 2 * K ^ 2 * Eprofile +
            2 * (C * (2 * Real.exp 2) / (4 * B.innerRate ^ 2 * (B.inner / 2) ^ 2)) ^ 2 * Etotal + ε

set_option maxHeartbeats 800000 in
theorem auxiliary_radiation_tail (B : Background) {U β Y L l T₀ S Eprofile Etotal : ℝ}
    (hU : 0 ≤ U) (hl : 0 ≤ l)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (gY g ζ H : ℕ → ℝ → ℝ)
    (hζ : ∀ n, MemLp (ζ n) 2 (volume.restrict (Ici l)))
    (hH : ∀ n, MemLp (H n) 2 (volume.restrict (Ici l)))
    (hHE : ∀ n, (∫ t in Ici l, H n t ^ 2) ≤ Eprofile)
    (hclose : Tendsto (fun n => ∫ t in Ici l, (ζ n t - ζ 0 t - H n t) ^ 2) atTop (𝓝 0))
    (hR : ∀ n, MemLp (radiationRow B.innerRate (X n)) 2 (volume.restrict (Ici 0)))
    (hRE : ∀ n, (∫ t in Ici (0 : ℝ), ‖radiationRow B.innerRate (X n) t‖ ^ 2) ≤ Etotal)
    (hhalf : ∀ n l' b₀, l ≤ l' → max l' T₀ ≤ b₀ / (1 + β) → S ≤ b₀ →
      AuxiliaryRadiationHalfline B hU (X n) (gY n) (g n) β Y L l' b₀
        (fun t => B.criticalWeight Y / (Real.exp (-1) * (-B.F Y) / B.outerRate) * |ζ n t|)) :
    AuxiliaryRadiationTail B hU X gY g β Y L l T₀ S Eprofile Etotal := by
  let C := Real.exp (2 + 1 / 16) * (L * (Y - B.inner)) ^ 2
  let K := B.criticalWeight Y / (Real.exp (-1) * (-B.F Y) / B.outerRate)
  let CA := 2 * (C / ((B.inner / 2) * B.innerRate)) ^ 2
  let CM := 2 * (C * (2 * Real.exp 2) / (4 * B.innerRate ^ 2 * (B.inner / 2) ^ 2)) ^ 2
  let W := CA * K ^ 2
  have hW : 0 ≤ W := by dsimp only [W, CA]; positivity
  have hCM : 0 ≤ CM := by dsimp only [CM]; positivity
  have hζi (n : ℕ) : IntegrableOn (fun t => ζ n t ^ 2) (Ici l) :=
    (memLp_two_iff_integrable_sq (hζ n).1).1 (hζ n)
  have hHi (n : ℕ) : IntegrableOn (fun t => H n t ^ 2) (Ici l) :=
    (memLp_two_iff_integrable_sq (hH n).1).1 (hH n)
  have hEi (n : ℕ) : IntegrableOn (fun t => (ζ n t - ζ 0 t - H n t) ^ 2) (Ici l) :=
    (memLp_two_iff_integrable_sq (((hζ n).sub (hζ 0)).sub (hH n)).1).1
      (((hζ n).sub (hζ 0)).sub (hH n))
  intro ε hε
  let η := ε / (6 * (W + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηeq : 6 * (W + 1) * η = ε := by
    dsimp only [η]
    field_simp [ne_of_gt (show 0 < W + 1 by positivity)]
  have htail : Tendsto (fun T : ℝ => ∫ t in Ici T, ζ 0 t ^ 2) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  obtain ⟨T, hT⟩ := eventually_atTop.1 (htail.eventually_lt_const hη)
  refine ⟨max l T, le_max_left _ _, ?_⟩
  intro l' hl'
  have hll : l ≤ l' := (le_max_left _ _).trans hl'
  have hsub : Ici l' ⊆ Ici l := Ici_subset_Ici.2 hll
  have hzero : (∫ t in Ici l', ζ 0 t ^ 2) < η := hT _ ((le_max_right _ _).trans hl')
  filter_upwards [hclose.eventually_lt_const hη] with n hn
  have he : (∫ t in Ici l', (ζ n t - ζ 0 t - H n t) ^ 2) < η :=
    (setIntegral_mono_set (hEi n) (Eventually.of_forall (fun t => sq_nonneg _))
      (Eventually.of_forall (fun _ ht => hsub ht))).trans_lt hn
  have hmodel : (∫ t in Ici l', H n t ^ 2) ≤ Eprofile :=
    (setIntegral_mono_set (hHi n) (Eventually.of_forall (fun t => sq_nonneg _))
      (Eventually.of_forall (fun _ ht => hsub ht))).trans (hHE n)
  have hsource : (∫ t in Ici l', ζ n t ^ 2) ≤ 3 * Eprofile + 6 * η := by
    have hiE := (hEi n).mono_set hsub
    have hiZ := (hζi 0).mono_set hsub
    have hiH := (hHi n).mono_set hsub
    have hiEZ : IntegrableOn (fun t => (ζ n t - ζ 0 t - H n t) ^ 2 + ζ 0 t ^ 2) (Ici l') :=
      hiE.add hiZ
    have hh := integral_mono ((hζi n).mono_set hsub)
      (((hiE.add hiZ).add hiH).const_mul 3) (fun t => by
        change ζ n t ^ 2 ≤ 3 * ((ζ n t - ζ 0 t - H n t) ^ 2 + ζ 0 t ^ 2 + H n t ^ 2)
        nlinarith only [sq_nonneg (ζ n t - 2 * ζ 0 t - H n t),
          sq_nonneg (ζ n t - ζ 0 t - 2 * H n t), sq_nonneg (ζ 0 t - H n t)])
    change (∫ t in Ici l', ζ n t ^ 2) ≤
      ∫ t in Ici l', 3 * ((ζ n t - ζ 0 t - H n t) ^ 2 + ζ 0 t ^ 2 + H n t ^ 2) at hh
    rw [integral_const_mul, integral_add hiEZ hiH, integral_add hiE hiZ] at hh
    linarith only [hh, he, hzero, hmodel]
  have htotal : (∫ t in Ici l', ‖radiationRow B.innerRate (X n) t‖ ^ 2) ≤ Etotal :=
    (setIntegral_mono_set ((memLp_two_iff_integrable_sq_norm (hR n).1).1 (hR n))
      (Eventually.of_forall (fun t => sq_nonneg _))
      (Eventually.of_forall (fun _ (ht : l' ≤ _) => (hl.trans hll).trans ht))).trans (hRE n)
  intro b₀ hstart hS
  obtain ⟨D, hD, hiD, hED⟩ := hhalf n l' b₀ hll hstart hS
  refine ⟨D, hD, hiD, ?_⟩
  change (∫ t in Ici b₀, ‖D t‖ ^ 2) ≤ CA * (∫ t in Ici l', (K * |ζ n t|) ^ 2) +
    CM * ∫ t in Ici l', ‖radiationRow B.innerRate (X n) t‖ ^ 2 at hED
  simp only [mul_pow, sq_abs, integral_const_mul, ← mul_assoc] at hED
  have hh := hED.trans (add_le_add (mul_le_mul_of_nonneg_left hsource hW)
    (mul_le_mul_of_nonneg_left htotal hCM))
  calc
    _ < 3 * W * Eprofile + CM * Etotal + ε := by nlinarith only [hh, hηeq, hη]
    _ = _ := by dsimp only [W, CA, CM, C, K]; ring

end CauchyHorizon
