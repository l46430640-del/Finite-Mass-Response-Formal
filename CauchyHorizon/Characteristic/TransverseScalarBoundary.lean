import CauchyHorizon.Characteristic.ScalarWave
import CauchyHorizon.Reduced.ScalarRegularity
import CauchyHorizon.Reduced.ScalarBoundary
import CauchyHorizon.Reduced.RegularRadius

/-! The full transverse scalar derivative, including its incoming term, has a compact trace. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

def IsTransverseScalarTrace {U ε : ℝ} (hU : 0 ≤ U)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (χ : ℝ → ℝ)
    (D : ℝ → C(Icc ε U, ℝ)) (Dh : C(Icc ε U, ℝ)) : Prop :=
  (∀ (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U),
    HasDerivWithinAt (fun x => intervalExtension hU (X T).1 x ⟨t, ht, htT⟩ 1)
      (D t u) (Icc 0 U) u) ∧
  Tendsto D atTop (𝓝 Dh) ∧
  Tendsto (fun w => D (χ w)) (𝓝[<] (0 : ℝ)) (𝓝 Dh) ∧
  ∃ T C : ℝ, 0 ≤ T ∧ 0 < C ∧ ∀ t, T ≤ t → ‖D t‖ ≤ C

set_option maxHeartbeats 800000 in
theorem incoming_transverse_scalar_boundary {U ε R e Λ φ₀ k : ℝ}
    (hU : 0 ≤ U) (hε : 0 < ε) (hUR : U < R)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Icc 0 U))) (hc : ContinuousOn f (Ioi 0))
    (vOut : (T : Ici (0 : ℝ)) → C(Icc 0 (T : ℝ), WaveVector))
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hX : ∀ T, IsWaveIntegral hU T.property e Λ (incomingWaveCurve hU hUR hp hf φ₀)
      (vOut T) (incomingWaveVelocity hUR hp hf) (X T))
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hr : ∀ (T : Ici (0 : ℝ)) u v, (X T).1 u v 0 ≠ 0)
    (Z : C(Icc ε U, WaveVector)) (Sh : C(Icc ε U, ℝ))
    (hZ : Tendsto (renormalizedWaveRow hε.le k X) atTop (𝓝 Z))
    (hS : Tendsto (scalarBoundaryRow hε.le (fun T => scalarTransportCorrection T.property
      (radialNuField T.property e Λ (incomingWaveCurve hU hUR hp hf φ₀) (X T).1 (hr T))
      (X T).2.1)) atTop (𝓝 Sh))
    (hR : ∀ u, Z u 0 ≠ 0) {χ : ℝ → ℝ} (hχ : Tendsto χ (𝓝[<] (0 : ℝ)) atTop) :
    ∃ D : ℝ → C(Icc ε U, ℝ), ∃ Dh : C(Icc ε U, ℝ),
      IsTransverseScalarTrace hU X χ D Dh ∧
      (∀ u, Dh u = ((R - u) * f u + Sh u) / Z u 0) ∧
      ∀ (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U),
        D t u = ((R - u) * f u + scalarTransportCorrection T.property
          (radialNuField T.property e Λ (incomingWaveCurve hU hUR hp hf φ₀) (X T).1 (hr T))
          (X T).2.1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht, htT⟩) /
          (X T).1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht, htT⟩ 0 := by
  let I : C(Icc ε U, ℝ) := ⟨fun u => (R - u) * f u,
    (continuous_const.sub continuous_subtype_val).mul
      (hc.comp_continuous continuous_subtype_val (fun u => hε.trans_le u.property.1))⟩
  let N := fun T => radialNuField T.property e Λ (incomingWaveCurve hU hUR hp hf φ₀) (X T).1 (hr T)
  let S := fun T => scalarTransportCorrection T.property (N T) (X T).2.1
  let D := fun t => (I + scalarBoundaryRow hε.le S t) * Ring.inverse (waveRadius (renormalizedWaveRow hε.le k X t))
  let Dh := (I + Sh) * Ring.inverse (waveRadius Z)
  have hfield (S T : Ici (0 : ℝ)) (hST : S ≤ T) (u : Icc 0 U) (v : Icc 0 (S : ℝ)) :
      (X S).1 u v = (X T).1 u ⟨v, v.property.1, v.property.2.trans hST⟩ := by
    have he := congrArg (fun x : WaveState U (S : ℝ) => x.1 u v) (hcompat S T hST)
    change (X T).1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X S).1 u v at he
    simpa only [zero_add] using he.symm
  have hvel (S T : Ici (0 : ℝ)) (hST : S ≤ T) (u : Icc 0 U) (v : Icc 0 (S : ℝ)) :
      (X S).2.1 u v = (X T).2.1 u ⟨v, v.property.1, v.property.2.trans hST⟩ := by
    have he := congrArg (fun x : WaveState U (S : ℝ) => x.2.1 u v) (hcompat S T hST)
    change (X T).2.1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X S).2.1 u v at he
    simpa only [zero_add] using he.symm
  have hSc (A T : Ici (0 : ℝ)) (hAT : A ≤ T) u v :
      S A u v = S T u ⟨v, v.property.1, v.property.2.trans hAT⟩ :=
    scalarTransportCorrection_prefix_eq A.property T.property hAT _ _ _ _
      (radialNuField_prefix_eq A.property T.property hAT e Λ _ _ _ (hr T) (hr A) (hfield A T hAT))
      (hvel A T hAT) u v
  have hfinite (T : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U) :
      D t u = ((R - u) * f u + S T ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht, htT⟩) /
        (X T).1 ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht, htT⟩ 0 := by
    have hr0 (u : Icc ε U) : waveRadius (renormalizedWaveRow hε.le k X t) u ≠ 0 := by
      change renormalizedWaveRow hε.le k X t u 0 ≠ 0
      simpa only [renormalizedWaveRow_apply hε.le X hcompat T ht htT, if_neg (by decide : (0 : Fin 3) ≠ 2),
        add_zero] using hr T ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨t, ht, htT⟩
    simp only [D, ContinuousMap.mul_apply, ContinuousMap.add_apply, continuousMap_inverse_apply _ hr0,
      scalarBoundaryRow_apply hε.le S hSc T ht htT]
    change (_ + _) * (renormalizedWaveRow hε.le k X t u 0)⁻¹ = _
    rw [renormalizedWaveRow_apply hε.le X hcompat T ht htT u 0]
    simp only [if_neg (by decide : (0 : Fin 3) ≠ 2), add_zero, div_eq_mul_inv]
    rfl
  have hu := ((waveRadius Z).isUnit_iff_forall_ne_zero).2 hR
  have hi := (contDiffAt_ringInverse ℝ (n := 1) hu.unit).continuousAt
  rw [hu.unit_spec] at hi
  have hI := hi.tendsto.comp ((waveRadius.continuous.tendsto Z).comp hZ)
  have hD : Tendsto D atTop (𝓝 Dh) := (tendsto_const_nhds.add hS).mul hI
  refine ⟨D, Dh, ⟨?_, hD, hD.comp hχ, ?_⟩, ?_, hfinite⟩
  · intro T t ht htT u
    have hinu : ∀ᵐ x ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf x 0 = -1 := by
      filter_upwards [incomingWaveVelocity_ae hUR hp hf] with x hx
      rw [hx]
      rfl
    have hif : ∀ᵐ x ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf x 1 = f x := by
      filter_upwards [incomingWaveVelocity_ae hUR hp hf] with x hx
      rw [hx]
      rfl
    have hd := (hX T).scalar_hasDerivWithinAt_of_continuous rfl hinu hc hif
      (show (u : ℝ) ∈ Ioc 0 U from ⟨hε.trans_le u.property.1, u.property.2⟩) ⟨t, ht, htT⟩
    rw [hfinite T t ht htT u]
    simpa only [incomingWaveCurve_apply, incomingRadius, Matrix.cons_val_zero] using hd
  · obtain ⟨T, hT⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hD 1 (by norm_num))
    refine ⟨max 0 T, ‖Dh‖ + 1, le_max_left _ _, by positivity, fun t ht => ?_⟩
    have hb := (hT t ((le_max_right _ _).trans ht)).le
    rw [dist_eq_norm] at hb
    exact (norm_le_norm_sub_add (D t) Dh).trans (by linarith only [hb])
  · intro u
    simp only [Dh, ContinuousMap.mul_apply, ContinuousMap.add_apply,
      continuousMap_inverse_apply (waveRadius Z) hR]
    rfl

end CauchyHorizon
