import CauchyHorizon.Reduced.IntegralBall
import Mathlib.Topology.MetricSpace.Contracting

/-! Uniform local existence for the actual characteristic integral equations. -/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CauchyHorizon

def IsWaveIntegral {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x : WaveState U V) : Prop :=
  ∃ hx : ∀ u v, x.1 u v 0 ≠ 0, waveIteration hU hV e Λ zIn vOut uIn x hx = x

theorem exists_small_wave_rectangle {δ : ℝ} (hδ : 0 < δ) (N S B : ℝ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ d * N ≤ δ ∧ Real.sqrt d * S ≤ δ ∧
      d * S ≤ δ ∧ B * (Real.sqrt d + d) ≤ 1 / 2 := by
  have hN : Tendsto (fun d : ℝ => d * N) (𝓝 0) (𝓝 0) := by
    simpa using (show Continuous (fun d : ℝ => d * N) by fun_prop).tendsto 0
  have hS : Tendsto (fun d : ℝ => Real.sqrt d * S) (𝓝 0) (𝓝 0) := by
    simpa using (show Continuous (fun d : ℝ => Real.sqrt d * S) by fun_prop).tendsto 0
  have hT : Tendsto (fun d : ℝ => d * S) (𝓝 0) (𝓝 0) := by
    simpa using (show Continuous (fun d : ℝ => d * S) by fun_prop).tendsto 0
  have hB : Tendsto (fun d : ℝ => B * (Real.sqrt d + d)) (𝓝 0) (𝓝 0) := by
    simpa using (show Continuous (fun d : ℝ => B * (Real.sqrt d + d)) by fun_prop).tendsto 0
  have he : ∀ᶠ d in 𝓝 (0 : ℝ), d ≤ 1 ∧ d * N ≤ δ ∧ Real.sqrt d * S ≤ δ ∧
      d * S ≤ δ ∧ B * (Real.sqrt d + d) ≤ 1 / 2 := by
    filter_upwards [eventually_le_nhds (by norm_num : (0 : ℝ) < 1),
      hN.eventually_le_const hδ, hS.eventually_le_const hδ, hT.eventually_le_const hδ,
      hB.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with d hd hN hS hT hB
    exact ⟨hd, hN, hS, hT, hB⟩
  have hp : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < d := self_mem_nhdsWithin
  exact (hp.and (he.filter_mono nhdsWithin_le_nhds)).exists

theorem exists_local_wave_integral (e Λ r R M : ℝ) (hr : 0 < r) (hR : 0 ≤ R) (hM : 0 ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ δ < r ∧ ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ d → V ≤ d →
      ∀ (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
        (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))),
        (∀ u, r ≤ zIn u 0) → ‖zIn‖ ≤ R → ‖vOut‖ ≤ R → ‖uIn‖ ≤ M →
      ∃! x : WaveState U V, ‖x - waveSeed zIn vOut uIn‖ ≤ δ ∧
        IsWaveIntegral hU hV e Λ zIn vOut uIn x := by
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hδr : δ < r := half_lt_self hr
  let lo := waveBoxLower r R δ
  let hi := waveBoxUpper R δ
  have hrl : 0 < lo.1 0 := by change 0 < r - δ; linarith
  obtain ⟨C, _hL, hC⟩ := wave_coefficients_control (hi := hi) hrl e Λ
  obtain ⟨B, hB, hdiff⟩ := waveIteration_local_bound (hi := hi) hrl e Λ (M + δ)
  let S : ℝ := C * (1 + M + δ)
  have hS : 0 ≤ S := mul_nonneg C.2 (by positivity)
  obtain ⟨d, hd, hd1, hdN, hdS, hdT, hdB⟩ := exists_small_wave_rectangle hδ (R + δ) S B
  refine ⟨δ, hδ, hδr, d, hd, hd1, ?_⟩
  intro U V hU hV hUd hVd zIn vOut uIn hzr hz hv hu
  let seed := waveSeed zIn vOut uIn
  let Ball := Metric.closedBall seed δ
  have hnorm (x : Ball) : ‖(x : WaveState U V) - seed‖ ≤ δ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm x.val seed] using
      (show x.val ∈ Metric.closedBall seed δ from x.property)
  have hrange (x : Ball) : waveRange lo hi x.val := waveSeed_ball_range zIn vOut uIn hzr hz hv (hnorm x)
  have hrad (x : Ball) : ∀ u v, x.val.1 u v 0 ≠ 0 := waveRange_radius hrl (hrange x)
  have htrans (x : Ball) : ‖x.val.2.2‖ ≤ M + δ :=
    (waveSeed_component_bounds zIn vOut uIn (hnorm x)).2.2.trans (by linarith)
  have hsource (x : Ball) : ‖rectangleSource hU e Λ x.val (hrad x)‖ ≤ S := by
    refine (rectangleSource_norm_le hU e Λ hC x.val (hrad x) (hrange x)).trans ?_
    exact mul_le_mul_of_nonneg_left (by
      have hs := (Real.sqrt_le_one).2 (hUd.trans hd1)
      linarith [htrans x]) C.2
  have hinvariant (x : Ball) : waveIteration hU hV e Λ zIn vOut uIn x.val (hrad x) ∈ Ball := by
    change dist (waveIteration hU hV e Λ zIn vOut uIn x.val (hrad x)) seed ≤ δ
    rw [dist_eq_norm (waveIteration hU hV e Λ zIn vOut uIn x.val (hrad x)) seed]
    apply waveIteration_seed_bound hU hV e Λ zIn vOut uIn x.val (hrad x)
      (N := R + δ) (S := S)
      ((waveSeed_component_bounds zIn vOut uIn (hnorm x)).2.1.trans (by linarith)) (hsource x)
    · exact (mul_le_mul_of_nonneg_right hVd (by positivity : 0 ≤ R + δ)).trans hdN
    · exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hUd) hS).trans hdS
    · exact (mul_le_mul_of_nonneg_right hVd hS).trans hdT
  let T : Ball → Ball := fun x => ⟨waveIteration hU hV e Λ zIn vOut uIn x.val (hrad x), hinvariant x⟩
  have hcontract : ContractingWith (1 / 2) T := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul (α := Ball) (β := Ball) fun x y => ?_⟩
    change dist (waveIteration hU hV e Λ zIn vOut uIn x.val (hrad x))
      (waveIteration hU hV e Λ zIn vOut uIn y.val (hrad y)) ≤ (1 / 2 : ℝ≥0) * dist x.val y.val
    rw [dist_eq_norm (waveIteration hU hV e Λ zIn vOut uIn x.val (hrad x))
      (waveIteration hU hV e Λ zIn vOut uIn y.val (hrad y)), dist_eq_norm x.val y.val]
    refine (hdiff hU hV (hUd.trans hd1) zIn vOut uIn x.val y.val (hrange x) (hrange y) (htrans x)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg (x.val - y.val))
    exact ((mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt hUd) hVd)
      (le_trans zero_le_one hB)).trans hdB).trans_eq (by norm_num)
  let : CompleteSpace Ball := Metric.isClosed_closedBall.isComplete.completeSpace_coe
  let : Nonempty Ball := ⟨⟨seed, by simp [Ball, hδ.le]⟩⟩
  let x := hcontract.fixedPoint T
  have hfix : T x = x := hcontract.fixedPoint_isFixedPt
  refine ⟨x.val, ⟨hnorm x, hrad x, congrArg Subtype.val hfix⟩, ?_⟩
  intro y hy
  let yb : Ball := ⟨y, by
    change y ∈ Metric.closedBall seed δ
    rw [Metric.mem_closedBall, dist_eq_norm y seed]
    exact hy.1⟩
  have hyfix : Function.IsFixedPt T yb := by
    apply Subtype.ext
    exact hy.2.choose_spec
  exact congrArg Subtype.val (hcontract.fixedPoint_unique hyfix)

end CauchyHorizon
