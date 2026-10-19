import CauchyHorizon.Characteristic.MassDensity
import CauchyHorizon.Characteristic.RadiationComparison

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

def RadiationMassDensity {U ε : ℝ} (hε : 0 ≤ ε) (k c : ℝ)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (n : ℕ) → (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)))
    (P : ℕ → ℝ → ℝ) : Prop :=
  let J : C(Icc ε U, Icc 0 U) := ⟨fun u => ⟨u, hε.trans u.property.1, u.property.2⟩, by fun_prop⟩
  MassDensityLimit (fun n => massCoefficientRow hε k (X n) (N n))
    (fun n t => (radiationRow k (X n) t).comp J) (fun n t => ContinuousMap.const _ (c * P n t))

theorem radiation_mass_density {U ε k c ER EP : ℝ} (hε : 0 ≤ ε)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (n : ℕ) → (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ))) (P : ℕ → ℝ → ℝ)
    (hX : ∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X n T) = X n S)
    (hN : ∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      N n S u v = N n T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (hC : MassCoefficientControl (fun n => massCoefficientRow hε k (X n) (N n)))
    (hR : ∀ n, MemLp (radiationRow k (X n)) 2 (volume.restrict (Ici 0)))
    (hRE : ∀ n, (∫ t in Ici (0 : ℝ), ‖radiationRow k (X n) t‖ ^ 2) ≤ ER)
    (hP : ∀ n, MemLp (P n) 2 (volume.restrict (Ici 0)))
    (hPE : ∀ n, (∫ t in Ici (0 : ℝ), P n t ^ 2) ≤ EP)
    (herror : Tendsto (fun n => ∫ t in Ici (0 : ℝ), ‖radiationComparisonRow hε k c X P n t‖ ^ 2) atTop (𝓝 0))
    (hvanish : ∀ S : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) S, P n t = 0) :
    RadiationMassDensity hε k c X N P := by
  let J : C(Icc ε U, Icc 0 U) := ⟨fun u => ⟨u, hε.trans u.property.1, u.property.2⟩, by fun_prop⟩
  let R := fun n t => (radiationRow k (X n) t).comp J
  let H := fun n t => ContinuousMap.const (Icc ε U) (c * P n t)
  have hRi (n : ℕ) : MemLp (R n) 2 (volume.restrict (Ici 0)) :=
    (ContinuousMap.compCLM ℝ ℝ J).comp_memLp' (hR n)
  have hHi (n : ℕ) : MemLp (H n) 2 (volume.restrict (Ici 0)) :=
    (ContinuousLinearMap.const ℝ (Icc ε U) : ℝ →L[ℝ] C(Icc ε U, ℝ)).comp_memLp' ((hP n).const_mul c)
  apply mass_density_limit (ER := ER) (EH := c ^ 2 * EP)
    (fun n => continuousOn_massCoefficientRow hε (X n) (N n) (hX n) (hN n)) hC hRi hHi
  · intro n
    have hh := integral_mono ((memLp_two_iff_integrable_sq_norm (hRi n).1).1 (hRi n))
      ((memLp_two_iff_integrable_sq_norm (hR n).1).1 (hR n)) (fun t =>
        pow_le_pow_left₀ (norm_nonneg _) ((ContinuousMap.norm_le _ (norm_nonneg _)).2
          (fun u => (radiationRow k (X n) t).norm_coe_le_norm (J u))) 2)
    exact hh.trans (hRE n)
  · intro n
    have hh := integral_mono ((memLp_two_iff_integrable_sq_norm (hHi n).1).1 (hHi n))
      (((hP n).const_mul c).integrable_sq) (fun t => by
        have hb : ‖H n t‖ ≤ ‖c * P n t‖ :=
          (ContinuousMap.norm_le _ (norm_nonneg _)).2 (fun _ => le_rfl)
        simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hb 2)
    have he : (∫ t in Ici (0 : ℝ), (c * P n t) ^ 2) = c ^ 2 * ∫ t in Ici (0 : ℝ), P n t ^ 2 := by
      simp only [mul_pow, integral_const_mul]
    exact hh.trans (he.trans_le (mul_le_mul_of_nonneg_left (hPE n) (sq_nonneg c)))
  · exact herror
  · intro S
    filter_upwards [hvanish S] with n hn t ht
    ext u
    simp only [H, ContinuousMap.const_apply, hn t ht, mul_zero, ContinuousMap.zero_apply]

end CauchyHorizon
