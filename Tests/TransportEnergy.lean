import CauchyHorizon.Analysis.TransportEnergyBound

open Set MeasureTheory

namespace CauchyHorizon.Tests

-- Both a nonzero source and a nonzero lower boundary flux survive the estimate.
example {L S w : ℝ} (hL : 0 ≤ L) (hS : 0 ≤ S) (hw : 0 < w) :
    (∫ t in (0 : ℝ)..S, L ^ 2 + (L - t) ^ 2) ≤
      ((∫ t in (0 : ℝ)..S, t ^ 2) + ∫ x in (0 : ℝ)..L, x ^ 2 + S / w) * Real.exp (w * L) := by
  let p : ℝ × ℝ → ℝ := fun z => z.1
  let q : ℝ × ℝ → ℝ := fun z => z.1 - z.2
  have hp : ContinuousOn p (Icc 0 L ×ˢ Icc 0 S) := by fun_prop
  have hq : ContinuousOn q (Icc 0 L ×ˢ Icc 0 S) := by fun_prop
  have he := transport_energy_identity hL hS hp hq
    (c := fun _ => 1) (A := fun _ => 0) (B := fun _ => 0) (d := fun _ => 0)
    (f := fun _ => 1) (g := fun _ => 0) (qv := fun _ => -1) (cv := fun _ => 0)
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    (fun x _ t _ => by simpa only [p, zero_mul, zero_add, id_eq] using! hasDerivAt_id x)
    (fun x _ t _ => by
      simpa only [q, zero_mul, zero_add, one_mul, sub_neg_eq_add, add_zero, id_eq] using! (hasDerivAt_id x).sub_const t)
    (fun x _ t _ => by simpa only [q, id_eq] using! (hasDerivWithinAt_id t (Icc 0 S)).const_sub x)
    (fun x _ t _ => hasDerivWithinAt_const t (Icc 0 S) 1)
  have hb := transport_energy_bound hL hS hp hq
    (c := fun _ => 1) (A := fun _ => 0) (B := fun _ => 0) (d := fun _ => 0)
    (f := fun _ => 1) (g := fun _ => 0) (cv := fun _ => 0) (G := fun _ => 0) (η := fun _ => w)
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const continuousOn_const continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ => hw) (fun _ _ => zero_le_one) (fun _ _ => by norm_num) he.2
  simpa only [p, q, zero_sub, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_sq,
    zero_add, one_pow, one_mul, add_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one,
    mul_comm S (1 : ℝ), mul_comm L w] using hb

end CauchyHorizon.Tests
