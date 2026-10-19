import CauchyHorizon.Reduced.LocalStability

/-! Local stability and uniqueness from radius and state-norm bounds. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_local_wave_stability (e Λ ρ M : ℝ) (hρ : 0 < ρ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ d → V ≤ d →
      ∀ (z z' : C(Icc 0 U, WaveVector)) (v v' : C(Icc 0 V, WaveVector))
        (u u' : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x y : WaveState U V),
        IsWaveIntegral hU hV e Λ z v u x → IsWaveIntegral hU hV e Λ z' v' u' y →
        (∀ s t, ρ ≤ x.1 s t 0) → (∀ s t, ρ ≤ y.1 s t 0) → ‖x‖ ≤ M → ‖y‖ ≤ M →
        ‖x - y‖ ≤ 2 * (‖z - z'‖ + ‖v - v'‖ + ‖u - u'‖) := by
  let lo := waveBoxLower ρ M 0
  let hi := waveBoxUpper M 0
  have hr : 0 < lo.1 0 := by simpa [lo, waveBoxLower] using hρ
  obtain ⟨K, hK, hstab⟩ := local_wave_stability (hi := hi) hr e Λ M
  obtain ⟨d, hd, hd1, _hdN, _hdS, _hdT, hdK⟩ := exists_small_wave_rectangle zero_lt_one 0 0 K
  refine ⟨d, hd, hd1, ?_⟩
  intro U V hU hV hUd hVd z z' v v' u u' x y hx hy hxr hyr hxn hyn
  have hrange (z : WaveState U V) (hzr : ∀ u v, ρ ≤ z.1 u v 0) (hzn : ‖z‖ ≤ M) : waveRange lo hi z := by
    have hz (u : Icc 0 U) (v : Icc 0 V) (i : Fin 3) : |z.1 u v i| ≤ M :=
      (norm_le_pi_norm _ i).trans (((z.1 u).norm_coe_le_norm v).trans
        ((z.1.norm_coe_le_norm u).trans ((norm_fst_le z).trans hzn)))
    have hw (u : Icc 0 U) (v : Icc 0 V) (i : Fin 3) : |z.2.1 u v i| ≤ M :=
      (norm_le_pi_norm _ i).trans (((z.2.1 u).norm_coe_le_norm v).trans
        ((z.2.1.norm_coe_le_norm u).trans (((norm_fst_le z.2).trans (norm_snd_le z)).trans hzn)))
    intro u v
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro i
    · change (if i = 0 then ρ - 0 else -(M + 0)) ≤ z.1 u v i
      split_ifs with he
      · simpa only [he, sub_zero] using hzr u v
      · simpa only [add_zero] using (abs_le.1 (hz u v i)).1
    · simpa only [hi, waveBoxUpper, add_zero] using (abs_le.1 (hz u v i)).2
    · simpa only [lo, waveBoxLower, add_zero] using (abs_le.1 (hw u v i)).1
    · simpa only [hi, waveBoxUpper, add_zero] using (abs_le.1 (hw u v i)).2
  have hsmall : K * (Real.sqrt U + V) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt hUd) hVd) (zero_le_one.trans hK)).trans hdK
  exact hstab hU hV (hUd.trans hd1) hsmall z z' v v' u u' x y hx hy
    (hrange x hxr hxn) (hrange y hyr hyn) (((norm_snd_le x.2).trans (norm_snd_le x)).trans hxn)

theorem exists_local_wave_uniqueness (e Λ ρ M : ℝ) (hρ : 0 < ρ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ d → V ≤ d →
      ∀ (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
        (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x y : WaveState U V),
        IsWaveIntegral hU hV e Λ zIn vOut uIn x → IsWaveIntegral hU hV e Λ zIn vOut uIn y →
        (∀ u v, ρ ≤ x.1 u v 0) → (∀ u v, ρ ≤ y.1 u v 0) → ‖x‖ ≤ M → ‖y‖ ≤ M → x = y := by
  obtain ⟨d, hd, hd1, hstab⟩ := exists_local_wave_stability e Λ ρ M hρ
  refine ⟨d, hd, hd1, ?_⟩
  intro U V hU hV hUd hVd zIn vOut uIn x y hx hy hxr hyr hxn hyn
  have he := hstab hU hV hUd hVd zIn zIn vOut vOut uIn uIn x y hx hy hxr hyr hxn hyn
  have hz : ‖x - y‖ ≤ 0 := by simpa only [sub_self, norm_zero, add_zero, mul_zero] using he
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

end CauchyHorizon
