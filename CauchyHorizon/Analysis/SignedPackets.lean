import CauchyHorizon.Analysis.PacketData
import CauchyHorizon.Analysis.FiniteProfiles
import Mathlib.Data.Finset.Lattice.Fold

/-! Actual finite packet sums, with a common budget and all cross terms retained. -/

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction ENNReal ContDiff

namespace CauchyHorizon

theorem finite_packet_incoming_data {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ⊤)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcomp : HasCompactSupport ψ)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < ψ x)
    (hsupp : ∀ x, x ∉ Ioo (0 : ℝ) 1 → ψ x = 0)
    (c E : ι → ℝ) (hE : ∀ i, 0 < E i) (t L : ι → ℕ → ℝ)
    (hL : ∀ i n, 0 < L i n) (htop : ∀ i, Tendsto (t i) atTop atTop)
    (hLtop : ∀ i, Tendsto (L i) atTop atTop) (ℓ : ℝ) :
    let budget := (∑ i, |c i| * Real.sqrt (E i)) ^ 2
    ∃ A Apt : ℝ, 0 ≤ A ∧ 0 ≤ Apt ∧ ∃ P Q : ℕ → ℝ →ᵇ ℝ,
      P 0 = 0 ∧ Q 0 = 0 ∧
      (∀ n, n ≠ 0 → ∀ x, P n x = ∑ i, c i *
        (Real.sqrt (E i / ((∫ y, ψ y ^ 2) * L i n)) * ψ ((x - t i n) / L i n))) ∧
      (∀ n x, HasDerivAt (P n) (Q n x) x) ∧ (∀ n, ContDiff ℝ 1 (P n)) ∧
      (∀ n, Integrable (fun x => P n x ^ 2) ∧ (∫ x, P n x ^ 2) ≤ budget) ∧
      (∀ n, Integrable (fun x => Q n x ^ 2)) ∧
      Tendsto (fun n => ∫ x, Q n x ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖P n‖) atTop (𝓝 0) ∧
      ∃ m : ℕ → ℝ, (∀ n x, x ≤ m n → P n x = 0) ∧
      Tendsto (fun n => m n - ℓ) atTop atTop ∧
      (∀ U : ℝ, 0 < U →
        (∀ n, 0 ≤ primitiveEnergy (1 - 1 / p.toReal)
          (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U ∧
          primitiveEnergy (1 - 1 / p.toReal) (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U ≤ budget) ∧
        Tendsto (fun n => primitiveEnergy (1 - 1 / p.toReal)
          (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) U - ∫ x, P n x ^ 2)
          atTop (𝓝 0)) ∧
      ∀ δ : ℝ,
        (∀ n, MemLp (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p (volume.restrict (Icc 0 δ))) ∧
        (∀ n, (eLpNorm (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p
          (volume.restrict (Icc 0 δ))).toReal ≤ A) ∧
        (∀ n, ∀ᵐ u ∂volume.restrict (Icc 0 δ),
          |logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n) u| ≤ Apt * u ^ (-1 / p.toReal)) ∧
        Tendsto (fun n => (eLpNorm (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P n)) p
          (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) := by
  classical
  choose A Apt hA hApt P Q hP0 hQ0 hformula hd hc hPi _hPE hQi hQlim hs hfront _hprimitive hdata
    using fun i => smooth_packet_incoming_data hp hpfin hψ hcomp hpos hsupp
      (hE i) (t i) (L i) (hL i) (htop i) (hLtop i) ℓ
  let S : ℕ → ℝ →ᵇ ℝ := fun n => ∑ i, c i • P i n
  let D : ℕ → ℝ →ᵇ ℝ := fun n => ∑ i, c i • Q i n
  have hS (n : ℕ) (x : ℝ) : S n x = ∑ i, c i * P i n x := by simp [S]
  have hD (n : ℕ) (x : ℝ) : D n x = ∑ i, c i * Q i n x := by simp [D]
  have hdS (n : ℕ) (x : ℝ) : HasDerivAt (S n) (D n x) x := by
    rw [show (S n : ℝ → ℝ) = (fun y => ∑ i, c i * P i n y) from funext (hS n), hD]
    exact HasDerivAt.fun_sum (fun i (_hi : i ∈ Finset.univ) => (hd i n x).const_mul (c i))
  have hSi (n : ℕ) : Integrable (fun x => S n x ^ 2) ∧
      (∫ x, S n x ^ 2) ≤ (∑ i, |c i| * Real.sqrt (E i)) ^ 2 := by
    obtain ⟨hi, he⟩ := finite_sum_squared_integral Finset.univ c (fun i => P i n)
      (fun i _ => (hPi i n).1)
    simp_rw [← hS] at hi he
    refine ⟨hi, he.trans (pow_le_pow_left₀ ?_ ?_ 2)⟩
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hPi i n).2) (abs_nonneg _))
  have hDi (n : ℕ) : Integrable (fun x => D n x ^ 2) ∧
      (∫ x, D n x ^ 2) ≤ (∑ i, |c i| * Real.sqrt (∫ x, Q i n x ^ 2)) ^ 2 := by
    simpa only [hD] using finite_sum_squared_integral Finset.univ c (fun i => Q i n)
      (fun i _ => hQi i n)
  have hDlim : Tendsto (fun n => ∫ x, D n x ^ 2) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _ =>
      ((Real.continuous_sqrt.tendsto 0).comp (hQlim i)).const_mul |c i|)
    have hlim : Tendsto (fun n => (∑ i, |c i| * Real.sqrt (∫ x, Q i n x ^ 2)) ^ 2)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, Finset.sum_const_zero,
        zero_pow (by decide : 2 ≠ 0)] using hh.pow 2
    exact squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) (fun n => (hDi n).2) hlim
  obtain ⟨Φ, _Φ', hΦ, _hΦ', _hdΦ, _hiΦ, _hiΦ', _hMΦ⟩ :=
    smooth_packet_shape hψ hcomp (hpos (1 / 2) (by norm_num)).ne'
  have hPnorm (i : ι) : Tendsto (fun n => ‖P i n‖) atTop (𝓝 0) := by
    apply (normalizedPacket_norm_tendsto (E i) Φ (t i) (L i) (hLtop i)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have he : P i n = normalizedPacket (E i) Φ (t i n) (L i n) := by
      ext x
      rw [hformula i n hn.ne']
      change _ = Real.sqrt (E i / ((∫ y, Φ y ^ 2) * L i n)) * Φ ((x - t i n) / L i n)
      simp_rw [hΦ]
    rw [he]
  have hSnorm : Tendsto (fun n => ‖S n‖) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _ => (hPnorm i).const_mul |c i|)
    have hlim : Tendsto (fun n => ∑ i, |c i| * ‖P i n‖) atTop (𝓝 0) := by
      simpa only [mul_zero, Finset.sum_const_zero] using hh
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
    simpa only [S, norm_smul, Real.norm_eq_abs] using norm_sum_le Finset.univ (fun i => c i • P i n)
  let m : ℕ → ℝ := fun n => Finset.univ.inf' Finset.univ_nonempty (fun i => t i n)
  have hsm (n : ℕ) (x : ℝ) (hx : x ≤ m n) : S n x = 0 := by
    rw [hS]
    apply Finset.sum_eq_zero
    intro i _hi
    rw [hs i n x (hx.trans (Finset.inf'_le _ (Finset.mem_univ i))), mul_zero]
  have hmtop : Tendsto m atTop atTop := by
    apply tendsto_atTop.2
    intro R
    filter_upwards [eventually_all.2 (fun i => (tendsto_atTop.1 (htop i)) R)] with n hn
    exact (Finset.le_inf'_iff Finset.univ_nonempty _).2 (fun i _ => hn i)
  have hmfront : Tendsto (fun n => m n - ℓ) atTop atTop := by
    apply tendsto_atTop.2
    intro R
    filter_upwards [(tendsto_atTop.1 hmtop) (R + ℓ)] with n hn
    linarith only [hn]
  have hlog (n : ℕ) (u : ℝ) : logarithmicIncoming (1 - 1 / p.toReal) ℓ (S n) u =
      ∑ i, c i * logarithmicIncoming (1 - 1 / p.toReal) ℓ (P i n) u := by
    simp only [logarithmicIncoming, hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨∑ i, |c i| * A i, ∑ i, |c i| * Apt i,
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hA i).le),
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hApt i).le),
    S, D, by simp [S, hP0], by simp [D, hQ0], ?_, hdS, ?_, hSi,
    fun n => (hDi n).1, hDlim, hSnorm, m, hsm, hmfront, ?_, ?_⟩
  · intro n hn x
    simp only [hS, hformula _ n hn]
  · intro n
    rw [show (S n : ℝ → ℝ) = (fun y => ∑ i, c i * P i n y) from funext (hS n)]
    exact ContDiff.sum (fun i (_hi : i ∈ Finset.univ) => contDiff_const.mul (hc i n))
  · intro U hU
    have hpR : 4 ≤ p.toReal := by
      simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hpfin hp
    have hb : 0 < 1 - 1 / p.toReal := sub_pos.2 ((div_lt_one (by linarith)).2 (by linarith))
    exact logarithmicIncoming_primitive_energy_tendsto hb S D hdS
      (fun n => (hSi n).1) (fun n => (hSi n).2) (fun n => (hDi n).1) hDlim
      (fun R => ((tendsto_atTop.1 hmtop) R).mono (fun n hn x hx => hsm n x (hx.trans hn))) ℓ hU
  · intro δ
    have hnorm (n : ℕ) := finite_sum_lp_norm Finset.univ c
      (fun i => logarithmicIncoming (1 - 1 / p.toReal) ℓ (P i n))
      ((by norm_num : (1 : ℝ≥0∞) ≤ 4).trans hp) (fun i _ => (hdata i δ).1 n)
    simp_rw [← hlog] at hnorm
    refine ⟨fun n => (hnorm n).1, fun n => (hnorm n).2.trans ?_, ?_, ?_⟩
    · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        ((hdata i δ).2.1 n) (abs_nonneg _))
    · intro n
      filter_upwards [eventually_all.2 (fun i => (hdata i δ).2.2.1 n)] with u hu
      rw [hlog]
      calc
        _ ≤ ∑ i, |c i * logarithmicIncoming (1 - 1 / p.toReal) ℓ (P i n) u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |c i| * (Apt i * u ^ (-1 / p.toReal)) :=
          Finset.sum_le_sum (fun i _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hu i) (abs_nonneg _))
        _ = _ := by simp only [← mul_assoc, ← Finset.sum_mul]
    · have hh := tendsto_finsetSum Finset.univ (fun i _ =>
        ((hdata i δ).2.2.2).const_mul |c i|)
      have hlim : Tendsto (fun n => ∑ i, |c i| *
          (eLpNorm (logarithmicIncoming (1 - 1 / p.toReal) ℓ (P i n)) p
            (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) := by
        simpa only [mul_zero, Finset.sum_const_zero] using hh
      exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => (hnorm n).2) hlim

end CauchyHorizon
