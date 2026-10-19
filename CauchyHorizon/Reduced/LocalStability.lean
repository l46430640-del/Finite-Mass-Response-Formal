import CauchyHorizon.Reduced.IntegralRegularity

/-! Quantitative dependence of the actual local integral solution on characteristic data. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {U V : ℝ}

theorem waveSeed_difference_bound (z z' : C(Icc 0 U, WaveVector))
    (v v' : C(Icc 0 V, WaveVector)) (u u' : Lp WaveVector 2 (volume.restrict (Icc 0 U))) :
    ‖waveSeed z v u - waveSeed z' v' u'‖ ≤ ‖z - z'‖ + ‖v - v'‖ + ‖u - u'‖ := by
  have hz : ‖incomingField (V := V) z - incomingField z'‖ ≤ ‖z - z'‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg (z - z'))).2
    intro t
    exact (ContinuousMap.norm_le _ (norm_nonneg (z - z'))).2 (fun _ => (z - z').norm_coe_le_norm t)
  have hv : ‖(ContinuousMap.const (Icc 0 U) v - ContinuousMap.const _ v')‖ ≤ ‖v - v'‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg (v - v'))).2 (fun _ => le_rfl)
  have hu : ‖incomingTransverse (V := V) u - incomingTransverse u'‖ ≤ ‖u - u'‖ := by
    unfold incomingTransverse
    rw [← map_sub]
    exact incomingTransverse_norm_le (u - u')
  apply norm_prod_le_iff.2
  refine ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact hz.trans (by linarith [norm_nonneg (v - v'), norm_nonneg (u - u')])
  · exact hv.trans (by linarith [norm_nonneg (z - z'), norm_nonneg (u - u')])
  · exact hu.trans (by linarith [norm_nonneg (z - z'), norm_nonneg (v - v')])

theorem waveIteration_data_difference (hU : 0 ≤ U) (hV : 0 ≤ V) (e Λ : ℝ)
    (z z' : C(Icc 0 U, WaveVector)) (v v' : C(Icc 0 V, WaveVector))
    (u u' : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x : WaveState U V)
    (hx : ∀ s t, x.1 s t 0 ≠ 0) :
    waveIteration hU hV e Λ z v u x hx - waveIteration hU hV e Λ z' v' u' x hx =
      waveSeed z v u - waveSeed z' v' u' := by
  let I : WaveState U V := (longitudinalIntegral hV x.2.1,
    horizontalPrimitive hU (rectangleSource hU e Λ x hx), verticalPrimitive hV (rectangleSource hU e Λ x hx))
  change (waveSeed z v u + I) - (waveSeed z' v' u' + I) = _
  abel

theorem local_wave_stability {lo hi : WaveVector × WaveVector} (hr : 0 < lo.1 0) (e Λ M : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ 1 →
      B * (Real.sqrt U + V) ≤ 1 / 2 →
      ∀ (z z' : C(Icc 0 U, WaveVector)) (v v' : C(Icc 0 V, WaveVector))
        (u u' : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x y : WaveState U V),
        IsWaveIntegral hU hV e Λ z v u x → IsWaveIntegral hU hV e Λ z' v' u' y →
        waveRange lo hi x → waveRange lo hi y → ‖x.2.2‖ ≤ M →
        ‖x - y‖ ≤ 2 * (‖z - z'‖ + ‖v - v'‖ + ‖u - u'‖) := by
  obtain ⟨B, hB, hdiff⟩ := waveIteration_local_bound (hi := hi) hr e Λ M
  refine ⟨B, hB, ?_⟩
  intro U V hU hV hU1 hsmall z z' v v' u u' x y hx hy hxr hyr hxu
  obtain ⟨rx, hfixx⟩ := hx
  obtain ⟨ry, hfixy⟩ := hy
  have hd : ‖waveIteration hU hV e Λ z v u x rx - waveIteration hU hV e Λ z v u y ry‖ ≤
      (1 / 2) * ‖x - y‖ :=
    (hdiff hU hV hU1 z v u x y hxr hyr hxu).trans
      (mul_le_mul_of_nonneg_right hsmall (norm_nonneg (x - y)))
  have hdata : ‖waveIteration hU hV e Λ z v u y ry - waveIteration hU hV e Λ z' v' u' y ry‖ ≤
      ‖z - z'‖ + ‖v - v'‖ + ‖u - u'‖ := by
    rw [waveIteration_data_difference]
    exact waveSeed_difference_bound z z' v v' u u'
  have ht := (norm_add_le (waveIteration hU hV e Λ z v u x rx - waveIteration hU hV e Λ z v u y ry)
    (waveIteration hU hV e Λ z v u y ry - waveIteration hU hV e Λ z' v' u' y ry)).trans (add_le_add hd hdata)
  rw [sub_add_sub_cancel, hfixx, hfixy] at ht
  linarith

end CauchyHorizon
