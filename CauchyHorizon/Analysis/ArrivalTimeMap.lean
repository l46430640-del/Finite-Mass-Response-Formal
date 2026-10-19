import CauchyHorizon.Analysis.ArrivalInverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! A uniform change of arrival time from normalized logarithmic phases. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

theorem exists_normalized_arrival_time_map {a T d₁ d₂ : ℝ} (ha : 0 < a)
    (τ : Ioi (0 : ℝ) → ℝ) (hτ : ∀ ε, T ≤ τ ε) :
    ∃ S : ℝ, ∃ σ : Ioi (0 : ℝ) → ℝ, T ≤ S ∧ (∀ ε, S ≤ σ ε) ∧
      ∀ g h : ℝ → ℝ, ContinuousOn g (Ici T) → StrictAntiOn g (Ici T) →
        Tendsto g atTop (𝓝 0) → ContinuousOn h (Ici T) →
        (∀ t ∈ Ici T, 0 < g t ∧ DifferentiableAt ℝ g t ∧ 0 < h t ∧ DifferentiableAt ℝ h t) →
        (∀ (ε : Ioi (0 : ℝ)) (t : ℝ), τ ε ≤ t →
          |d₁ - Real.log (g t) - a * t| + |-deriv g t / g t - a| < ε ∧
          |d₂ - Real.log (h t) - a * t| + |-deriv h t / h t - a| < ε) →
        ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Ici S) ∧
          (∀ t ∈ Ici S, T < ψ t ∧ g (ψ t) = h t ∧
            HasDerivAt ψ ((-deriv h t / h t) / (-deriv g (ψ t) / g (ψ t))) t ∧
            |ψ t - t| ≤ (|d₁ - d₂| + 2) / a) ∧
          ∀ (ε : Ioi (0 : ℝ)) (t : ℝ), σ ε ≤ t →
            |ψ t - t - (d₁ - d₂) / a| + |deriv ψ t - 1| < ε := by
  have htriangle (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  let ε₀ : Ioi (0 : ℝ) := ⟨min 1 (a / 4), by change 0 < min (1 : ℝ) (a / 4); positivity⟩
  let L := (|d₁ - d₂| + 2) / a
  let S := τ ε₀ + (|d₁ - d₂| + 3) / a
  have hSbase : τ ε₀ < S := lt_add_of_pos_right _ (by positivity)
  have hTS : T ≤ S := (hτ ε₀).trans hSbase.le
  let η := fun ε : Ioi (0 : ℝ) =>
    (⟨min (a / 4) (a * ε / 8), by
      have he : 0 < (ε : ℝ) := ε.property
      change 0 < min (a / 4) (a * ε / 8)
      positivity⟩ : Ioi (0 : ℝ))
  let σ := fun ε => max S (τ (η ε) + L)
  refine ⟨S, σ, hTS, fun _ => le_max_left _ _, ?_⟩
  intro g h hgc hga hgl hhc hpoint herr
  have hbase : Ici (τ ε₀) ⊆ Ici T := fun _ ht => (hτ ε₀).trans ht
  have hneg (t : ℝ) (ht : τ ε₀ ≤ t) : deriv g t < 0 := by
    have hh := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt (herr ε₀ t ht).1
    have hlo := (abs_lt.1 hh).1
    have he : (ε₀ : ℝ) ≤ a / 4 := min_le_right _ _
    have hp : 0 < -deriv g t / g t := by linarith only [hlo, he, ha]
    exact neg_pos.1 ((div_pos_iff_of_pos_right (hpoint t (hbase ht)).1).1 hp)
  obtain ⟨v, hvc, _hvl, hvinv, _hvleft⟩ := exists_arrival_inverse_closed
    (hgc.mono hbase) (hga.mono hbase) hgl (fun t ht => (hpoint t (hbase ht)).1)
    (fun t ht => ⟨(hpoint t (hbase ht)).2.1, hneg t ht⟩)
  have hdomain (t : ℝ) (ht : S ≤ t) : h t ∈ Ioo 0 (g (τ ε₀)) := by
    have htT := hTS.trans ht
    have h₁ := (abs_lt.1 ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt
      (herr ε₀ (τ ε₀) le_rfl).1)).2
    have h₂ := (abs_lt.1 ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt
      (herr ε₀ t (hSbase.le.trans ht)).2)).1
    have he : (ε₀ : ℝ) ≤ 1 := min_le_left _ _
    have htime := mul_le_mul_of_nonneg_left ht ha.le
    have heq : a * S = a * τ ε₀ + |d₁ - d₂| + 3 := by dsimp only [S]; field_simp; ring
    rw [heq] at htime
    have hlog : Real.log (h t) < Real.log (g (τ ε₀)) := by
      linarith only [h₁, h₂, he, htime, neg_abs_le (d₁ - d₂)]
    exact ⟨(hpoint t htT).2.2.1,
      (Real.log_lt_log_iff (hpoint t htT).2.2.1 (hpoint (τ ε₀) (hτ ε₀)).1).1 hlog⟩
  let ψ := fun t => v (h t)
  have hinv (t : ℝ) (ht : S ≤ t) := hvinv (h t) (hdomain t ht)
  have hφc : ContinuousOn ψ (Ici S) := hvc.comp (hhc.mono (fun _ ht => hTS.trans ht)) hdomain
  have hder (t : ℝ) (ht : S ≤ t) :
      HasDerivAt ψ ((-deriv h t / h t) / (-deriv g (ψ t) / g (ψ t))) t := by
    have hh := (hinv t ht).2.2.comp t (hpoint t (hTS.trans ht)).2.2.2.hasDerivAt
    apply hh.congr_deriv
    change (deriv g (ψ t))⁻¹ * deriv h t = _
    rw [(hinv t ht).2.1]
    field_simp [(hpoint t (hTS.trans ht)).2.2.1.ne', (hneg (ψ t) (hinv t ht).1.le).ne]
  have hphase (t : ℝ) (ht : S ≤ t) :
      a * (ψ t - t - (d₁ - d₂) / a) =
        (d₂ - Real.log (h t) - a * t) - (d₁ - Real.log (g (ψ t)) - a * ψ t) := by
    rw [(hinv t ht).2.1]
    field_simp
    ring
  have hshift (t : ℝ) (ht : S ≤ t) : |ψ t - t| ≤ L := by
    have hb₁ := ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt
      (herr ε₀ (ψ t) (hinv t ht).1.le).1).le.trans (min_le_left _ _)
    have hb₂ := ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt
      (herr ε₀ t (hSbase.le.trans ht)).2).le.trans (min_le_left _ _)
    have heq : a * (ψ t - t) = (d₁ - d₂) +
        ((d₂ - Real.log (h t) - a * t) - (d₁ - Real.log (g (ψ t)) - a * ψ t)) := by
      have hh := hphase t ht
      have hc : a * ((d₁ - d₂) / a) = d₁ - d₂ := by field_simp
      linarith only [hh, hc]
    have hh : |a * (ψ t - t)| ≤ |d₁ - d₂| + 2 := by
      rw [heq]
      have hh := add_le_add (le_refl |d₁ - d₂|) ((htriangle _ _).trans (add_le_add hb₂ hb₁))
      exact (abs_add_le _ _).trans (by simpa only [one_add_one_eq_two] using hh)
    rw [abs_mul, abs_of_pos ha] at hh
    exact (le_div_iff₀ ha).2 (by nlinarith only [hh])
  refine ⟨ψ, hφc, fun t ht => ⟨(hτ ε₀).trans_lt (hinv t ht).1,
    (hinv t ht).2.1, hder t ht, hshift t ht⟩, ?_⟩
  intro ε t ht
  have htS : S ≤ t := (le_max_left _ _).trans ht
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have htη : τ (η ε) ≤ t := by
    have hh := (le_max_right _ _).trans ht
    linarith only [hh, hL]
  have hψη : τ (η ε) ≤ ψ t := by
    have hh := (le_max_right _ _).trans ht
    have hlo := (abs_le.1 (hshift t htS)).1
    linarith only [hh, hlo]
  have hb₁ := (herr (η ε) (ψ t) hψη).1
  have hb₂ := (herr (η ε) t htη).2
  have hp₁ := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt hb₁
  have hp₂ := (le_add_of_nonneg_right (abs_nonneg _)).trans_lt hb₂
  have hd₁ := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt hb₁
  have hd₂ := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt hb₂
  have hηa : (η ε : ℝ) ≤ a / 4 := min_le_left _ _
  have hηε : (η ε : ℝ) ≤ a * ε / 8 := min_le_right _ _
  have hp : |ψ t - t - (d₁ - d₂) / a| < 2 * (η ε : ℝ) / a := by
    apply (lt_div_iff₀ ha).2
    have hh := (htriangle _ _).trans_lt (add_lt_add hp₂ hp₁)
    rw [← hphase t htS, abs_mul, abs_of_pos ha] at hh
    nlinarith only [hh]
  let b := -deriv g (ψ t) / g (ψ t)
  let c := -deriv h t / h t
  have hb : a / 2 < b := by
    have hh := (abs_lt.1 hd₁).1
    change -(η ε : ℝ) < b - a at hh
    linarith only [hh, hηa, ha]
  have hb0 : 0 < b := (half_pos ha).trans hb
  have hjac : |deriv ψ t - 1| < 4 * (η ε : ℝ) / a := by
    rw [(hder t htS).deriv]
    change |c / b - 1| < _
    rw [div_sub_one hb0.ne', abs_div, abs_of_pos hb0]
    have hdiff : |c - b| < 2 * (η ε : ℝ) := by
      have hh := (htriangle (c - a) (b - a)).trans_lt (add_lt_add hd₂ hd₁)
      simpa only [sub_sub_sub_cancel_right, ← two_mul] using hh
    apply (div_lt_iff₀ hb0).2
    have hmul := mul_lt_mul_of_pos_left hb
      (div_pos (mul_pos (by norm_num : 0 < (4 : ℝ)) (η ε).property) ha)
    have heq : (4 * (η ε : ℝ) / a) * (a / 2) = 2 * (η ε : ℝ) := by field_simp; ring
    rw [heq] at hmul
    exact hdiff.trans hmul
  have hh := add_lt_add hp hjac
  apply hh.trans_le
  rw [← add_div]
  apply (div_le_iff₀ ha).2
  have hηpos : 0 < (η ε : ℝ) := (η ε).property
  nlinarith only [hηε, hηpos]

end CauchyHorizon
