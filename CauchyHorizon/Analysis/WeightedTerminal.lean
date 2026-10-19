import CauchyHorizon.Analysis.TerminalFixedPoint
import Mathlib.Tactic.FieldSimp

/-! Exponential rescaling preserves the small nonlinear Lipschitz bound. -/

open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace CauchyHorizon

noncomputable def terminalWeight (d t : ℝ) : ℝ := Real.exp (-d * max t 0)

theorem terminalWeight_continuous (d : ℝ) : Continuous (terminalWeight d) := by
  unfold terminalWeight
  fun_prop

theorem terminalWeight_pos (d t : ℝ) : 0 < terminalWeight d t := Real.exp_pos _

theorem terminalWeight_le_one {d : ℝ} (hd : 0 < d) (t : ℝ) : terminalWeight d t ≤ 1 :=
  Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hd.le) (le_max_right t 0))

theorem terminalWeight_eq {d t : ℝ} (ht : 0 ≤ t) :
    terminalWeight d t = Real.exp (-d * t) := by simp [terminalWeight, max_eq_left ht]

theorem terminalWeight_hasDerivWithinAt (d : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (terminalWeight d) (-d * terminalWeight d t) (Ici 0) t := by
  apply (((((hasDerivAt_id t).const_mul (-d)).exp).congr_deriv ?_).hasDerivWithinAt).congr
    (fun _ hw => terminalWeight_eq hw) (terminalWeight_eq ht)
  rw [terminalWeight_eq ht]
  simp only [id_eq]
  ring

theorem terminalWeight_hasDerivAt (d : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (terminalWeight d) (-d * terminalWeight d t) t :=
  (terminalWeight_hasDerivWithinAt d ht.le).hasDerivAt (Ici_mem_nhds ht)

noncomputable def rescaledFuture {d ε : ℝ} {z : ℝ → ℝ}
    (hz : ContinuousOn z (Ici 0)) (hb : ∀ t ∈ Ici (0 : ℝ), ‖z t‖ ≤ ε * Real.exp (-d * t)) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => futureExtension z t / terminalWeight d t)
    ((futureExtension_continuous hz).div (terminalWeight_continuous d)
      (fun t => (terminalWeight_pos d t).ne')) ε (fun t => by
        rw [norm_div, Real.norm_of_nonneg (terminalWeight_pos d t).le,
          div_le_iff₀ (terminalWeight_pos d t)]
        exact hb (max t 0) (le_max_right t 0))

theorem rescaledFuture_norm_le {d ε : ℝ} (hε : 0 ≤ ε) {z : ℝ → ℝ}
    (hz : ContinuousOn z (Ici 0)) (hb : ∀ t ∈ Ici (0 : ℝ), ‖z t‖ ≤ ε * Real.exp (-d * t)) :
    ‖rescaledFuture hz hb‖ ≤ ε := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hε _

theorem weighted_mem_collar {δ w x : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1) (hx : ‖x‖ ≤ δ) :
    w * x ∈ Icc (-δ) δ := by
  have hb : ‖w * x‖ ≤ δ := by
    rw [norm_mul, Real.norm_of_nonneg hw]
    exact (mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)).trans (by simpa using hx)
  exact abs_le.1 hb

theorem weighted_source_difference {δ ε w z : ℝ} {L J : ℝ≥0} {g j : ℝ → ℝ}
    (hg : LipschitzOnWith L g (Icc (-δ) δ)) (hj : LipschitzOnWith J j (Icc (-δ) δ))
    (hw : 0 < w) (hw1 : w ≤ 1) (hz : ‖z‖ ≤ ε)
    {x y : ℝ} (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
    ‖(g (w * x) / w + z * j (w * x)) - (g (w * y) / w + z * j (w * y))‖ ≤
      ((L : ℝ) + ε * J) * ‖x - y‖ := by
  have hxm := weighted_mem_collar hw.le hw1 hx
  have hym := weighted_mem_collar hw.le hw1 hy
  have hgd := hg.norm_sub_le hxm hym
  have hjd := hj.norm_sub_le hxm hym
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg hw.le] at hgd hjd
  have hgdiv : ‖(g (w * x) - g (w * y)) / w‖ ≤ L * ‖x - y‖ := by
    rw [norm_div, Real.norm_of_nonneg hw.le, div_le_iff₀ hw]
    calc
      _ ≤ L * (w * ‖x - y‖) := hgd
      _ = _ := by ring
  have hjmul : ‖z * (j (w * x) - j (w * y))‖ ≤ ε * J * ‖x - y‖ := by
    have hε := (norm_nonneg z).trans hz
    rw [norm_mul]
    calc
      _ ≤ ε * (J * (w * ‖x - y‖)) :=
        mul_le_mul hz hjd (norm_nonneg _) ((norm_nonneg z).trans hz)
      _ ≤ ε * (J * (1 * ‖x - y‖)) := by gcongr
      _ = _ := by ring
  calc
    _ = ‖(g (w * x) - g (w * y)) / w + z * (j (w * x) - j (w * y))‖ := by congr 1; ring
    _ ≤ ‖(g (w * x) - g (w * y)) / w‖ + ‖z * (j (w * x) - j (w * y))‖ := norm_add_le _ _
    _ ≤ L * ‖x - y‖ + ε * J * ‖x - y‖ := add_le_add hgdiv hjmul
    _ = _ := by ring

noncomputable def weightedTerminalSource {c δ ε : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    {L J : ℝ≥0} {g j e : ℝ → ℝ}
    (hg : LipschitzOnWith L g (Icc (-δ) δ)) (hj : LipschitzOnWith J j (Icc (-δ) δ))
    (hg0 : g 0 = 0) (he : Continuous e) (hep : ∀ t, 0 < e t) (he1 : ∀ t, e t ≤ 1)
    (Z : ℝ →ᵇ ℝ) (hZ : ‖Z‖ ≤ ε)
    (hsmall : (L : ℝ) + ε * J ≤ c / 2) (hsize : ε * ‖j 0‖ ≤ c * δ / 2) : TerminalSource where
  rate := c
  radius := δ
  rate_pos := hc
  radius_pos := hδ
  source t x := g (e t * x) / e t + Z t * j (e t * x)
  continuous Y hY := by
    have hmem (t : ℝ) := weighted_mem_collar (hep t).le (he1 t)
      ((Y.norm_coe_le_norm t).trans hY)
    have hcomp := he.mul Y.continuous
    exact ((hg.continuousOn.comp_continuous hcomp hmem).div he (fun t => (hep t).ne')).add
      (Z.continuous.mul (hj.continuousOn.comp_continuous hcomp hmem))
  difference t x y hx hy :=
    (weighted_source_difference hg hj (hep t) (he1 t)
      ((Z.norm_coe_le_norm t).trans hZ) hx hy).trans
        (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))
  zero_bound t := by
    simp only [mul_zero, hg0, zero_div, zero_add, norm_mul]
    exact (mul_le_mul_of_nonneg_right ((Z.norm_coe_le_norm t).trans hZ) (norm_nonneg _)).trans hsize

end CauchyHorizon
