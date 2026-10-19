import CauchyHorizon.Reduced.IntegralEstimates

/-! A ball about characteristic data stays in a controlled positive-radius range. -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CauchyHorizon

variable {U V : ℝ}

noncomputable def waveSeed (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))) : WaveState U V :=
  (incomingField zIn, ContinuousMap.const _ vOut, incomingTransverse uIn)

theorem incomingTransverse_norm_le (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))) :
    ‖incomingTransverse (V := V) uIn‖ ≤ ‖uIn‖ := by
  let T : WaveVector →L[ℝ] C(Icc 0 V, WaveVector) := ContinuousLinearMap.const ℝ _
  have hT : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound (by norm_num)
    intro z
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg z)).2 (fun _ => le_rfl)
  change ‖T.compLp uIn‖ ≤ ‖uIn‖
  exact (T.norm_compLp_le uIn).trans (by simpa using mul_le_mul_of_nonneg_right hT (norm_nonneg uIn))

theorem waveSeed_component_bounds (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))) {x : WaveState U V} {δ : ℝ}
    (hx : ‖x - waveSeed zIn vOut uIn‖ ≤ δ) :
    ‖x.1‖ ≤ ‖zIn‖ + δ ∧ ‖x.2.1‖ ≤ ‖vOut‖ + δ ∧ ‖x.2.2‖ ≤ ‖uIn‖ + δ := by
  let s := waveSeed (V := V) zIn vOut uIn
  have hz : ‖s.1‖ ≤ ‖zIn‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg zIn)).2
    intro u
    exact (ContinuousMap.norm_le _ (norm_nonneg zIn)).2 (fun _ => zIn.norm_coe_le_norm u)
  have hv : ‖s.2.1‖ ≤ ‖vOut‖ := (ContinuousMap.norm_le _ (norm_nonneg vOut)).2 (fun _ => le_rfl)
  have hu : ‖s.2.2‖ ≤ ‖uIn‖ := incomingTransverse_norm_le uIn
  have hdz := (norm_fst_le (x - s)).trans hx
  have hdv := ((norm_fst_le (x.2 - s.2)).trans (norm_snd_le (x - s))).trans hx
  have hdu := ((norm_snd_le (x.2 - s.2)).trans (norm_snd_le (x - s))).trans hx
  change ‖x.1 - s.1‖ ≤ δ at hdz
  change ‖x.2.1 - s.2.1‖ ≤ δ at hdv
  change ‖x.2.2 - s.2.2‖ ≤ δ at hdu
  refine ⟨?_, ?_, ?_⟩
  · have h := norm_le_insert s.1 x.1
    rw [norm_sub_rev] at h
    linarith
  · have h := norm_le_insert s.2.1 x.2.1
    rw [norm_sub_rev] at h
    linarith
  · have h := norm_le_insert s.2.2 x.2.2
    rw [norm_sub_rev] at h
    linarith

noncomputable def waveBoxLower (r R δ : ℝ) : WaveVector × WaveVector :=
  ((fun i => if i = 0 then r - δ else -(R + δ)), fun _ => -(R + δ))

noncomputable def waveBoxUpper (R δ : ℝ) : WaveVector × WaveVector :=
  (fun _ => R + δ, fun _ => R + δ)

theorem waveSeed_ball_range (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))) {x : WaveState U V} {r R δ : ℝ}
    (hzr : ∀ u, r ≤ zIn u 0) (hz : ‖zIn‖ ≤ R) (hv : ‖vOut‖ ≤ R)
    (hx : ‖x - waveSeed zIn vOut uIn‖ ≤ δ) :
    waveRange (waveBoxLower r R δ) (waveBoxUpper R δ) x := by
  obtain ⟨hxn, hvn, _⟩ := waveSeed_component_bounds zIn vOut uIn hx
  have hcoord (u : Icc 0 U) (v : Icc 0 V) (i : Fin 3) :
      |x.1 u v i| ≤ R + δ ∧ |x.2.1 u v i| ≤ R + δ := by
    constructor
    · exact (norm_le_pi_norm _ i).trans
        (((x.1 u).norm_coe_le_norm v).trans ((x.1.norm_coe_le_norm u).trans (hxn.trans (by linarith))))
    · exact (norm_le_pi_norm _ i).trans
        (((x.2.1 u).norm_coe_le_norm v).trans ((x.2.1.norm_coe_le_norm u).trans (hvn.trans (by linarith))))
  have hrad (u : Icc 0 U) (v : Icc 0 V) : r - δ ≤ x.1 u v 0 := by
    have hd := (norm_le_pi_norm ((x.1 - (waveSeed zIn vOut uIn).1) u v) 0).trans
      ((((x.1 - (waveSeed zIn vOut uIn).1) u).norm_coe_le_norm v).trans
        (((x.1 - (waveSeed zIn vOut uIn).1).norm_coe_le_norm u).trans
          ((norm_fst_le (x - waveSeed zIn vOut uIn)).trans hx)))
    change |x.1 u v 0 - zIn u 0| ≤ δ at hd
    linarith [(abs_le.1 hd).1, hzr u]
  intro u v
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro i
  · change (if i = 0 then r - δ else -(R + δ)) ≤ x.1 u v i
    split_ifs with hi
    · simpa only [hi] using hrad u v
    · exact (abs_le.1 (hcoord u v i).1).1
  · exact (abs_le.1 (hcoord u v i).1).2
  · exact (abs_le.1 (hcoord u v i).2).1
  · exact (abs_le.1 (hcoord u v i).2).2

theorem rectangleSource_norm_le (hU : 0 ≤ U) (e Λ : ℝ)
    {lo hi : WaveVector × WaveVector} {C : ℝ≥0}
    (hC : ∀ p ∈ Icc lo.1 hi.1 ×ˢ Icc lo.2 hi.2,
      ‖(wavePotential e Λ p.1, waveLinear p.1 p.2)‖ ≤ C)
    (x : WaveState U V) (hx : ∀ u v, x.1 u v 0 ≠ 0) (hxr : waveRange lo hi x) :
    ‖rectangleSource hU e Λ x hx‖ ≤ C * (Real.sqrt U + ‖x.2.2‖) := by
  have hG : ‖rectanglePotential hU e Λ x.1 hx‖ ≤ Real.sqrt U * C := by
    unfold rectanglePotential
    refine (intervalToL2_norm_le hU _).trans ?_
    rw [sub_zero]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg U)
    apply (ContinuousMap.norm_le _ C.2).2
    intro u
    apply (ContinuousMap.norm_le _ C.2).2
    intro v
    exact (norm_fst_le _).trans (hC _ (hxr u v))
  have hA : ‖rectangleOperator hU x.1 x.2.1 hx‖ ≤ C := by
    unfold rectangleOperator
    refine (intervalToLinf_norm_le hU _).trans ?_
    apply (ContinuousMap.norm_le _ C.2).2
    intro u
    refine (pointwiseOperator_norm_le _).trans ?_
    apply (ContinuousMap.norm_le _ C.2).2
    intro v
    exact (norm_snd_le _).trans (hC _ (hxr u v))
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ Real.sqrt U * C + C * ‖x.2.2‖ := add_le_add hG
      ((operatorProduct_norm_le _ _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
    _ = _ := by ring

theorem waveIteration_seed_bound (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 U, WaveVector)) (vOut : C(Icc 0 V, WaveVector))
    (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x : WaveState U V)
    (hx : ∀ u v, x.1 u v 0 ≠ 0) {δ S N : ℝ}
    (hxn : ‖x.2.1‖ ≤ N) (hF : ‖rectangleSource hU e Λ x hx‖ ≤ S)
    (hz : V * N ≤ δ) (hv : Real.sqrt U * S ≤ δ) (hu : V * S ≤ δ) :
    ‖waveIteration hU hV e Λ zIn vOut uIn x hx - waveSeed zIn vOut uIn‖ ≤ δ := by
  apply norm_prod_le_iff.2
  refine ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · change ‖incomingField zIn + longitudinalIntegral hV x.2.1 - incomingField zIn‖ ≤ δ
    rw [add_sub_cancel_left]
    exact (longitudinalIntegral_norm_le hV _).trans ((mul_le_mul_of_nonneg_left hxn hV).trans hz)
  · change ‖ContinuousMap.const _ vOut + horizontalPrimitive hU (rectangleSource hU e Λ x hx) -
        ContinuousMap.const _ vOut‖ ≤ δ
    rw [add_sub_cancel_left]
    have h := horizontalPrimitive_norm_le hU (rectangleSource hU e Λ x hx)
    rw [sub_zero] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg U)).trans hv)
  · change ‖incomingTransverse uIn + verticalPrimitive hV (rectangleSource hU e Λ x hx) -
        incomingTransverse uIn‖ ≤ δ
    rw [add_sub_cancel_left]
    have h := verticalPrimitive_norm_le hV (rectangleSource hU e Λ x hx)
    rw [sub_zero] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hF hV).trans hu)

end CauchyHorizon
