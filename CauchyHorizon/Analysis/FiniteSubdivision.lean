import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! A uniform small-step implication propagates across any finite interval. -/

namespace CauchyHorizon

theorem interval_subdivision_induction {A d : ℝ} (hA : 0 ≤ A) (hd : 0 < d) {P : ℝ → Prop}
    (hzero : P 0)
    (hstep : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ A → b ≤ d → P a → P (a + b)) : P A := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (A / d) 0)
  have hNp : (0 : ℝ) < N := (le_max_right _ _).trans_lt hN
  let w := A / N
  have hw : 0 ≤ w := div_nonneg hA hNp.le
  have hwd : w ≤ d := (div_le_iff₀ hNp).2 (by
    have hn := (div_lt_iff₀ hd).mp ((le_max_left _ _).trans_lt hN)
    nlinarith)
  have hNW : (N : ℝ) * w = A := by dsimp only [w]; field_simp
  have hi : ∀ k : ℕ, k ≤ N → P ((k : ℝ) * w) := by
    intro k
    induction k with
    | zero => intro _hk; simpa only [Nat.cast_zero, zero_mul] using hzero
    | succ k ih =>
      intro hk
      have hkw : ((k : ℝ) + 1) * w ≤ A := by
        have hn : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
        simpa only [hNW] using mul_le_mul_of_nonneg_right hn hw
      have hs := hstep (k * w) w (mul_nonneg (Nat.cast_nonneg _) hw) hw (by nlinarith) hwd
        (ih (Nat.le_trans (Nat.le_succ k) hk))
      simpa only [Nat.cast_succ, add_mul, one_mul] using hs
  simpa only [hNW] using hi N le_rfl

end CauchyHorizon
