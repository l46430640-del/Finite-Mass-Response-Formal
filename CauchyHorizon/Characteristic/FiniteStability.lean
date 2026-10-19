import CauchyHorizon.Characteristic.FiniteState
import CauchyHorizon.Reduced.FiniteStability

/-! Physical finite-time convergence from the scalar incoming data and a common radius floor. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

theorem IsWaveIntegral.horizon_tendsto {ι : Type*} {l : Filter ι} {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) {p : ℝ≥0∞} (hp : 4 ≤ p)
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) p (volume.restrict (Icc 0 U)))
    (hg : MemLp g p (volume.restrict (Icc 0 U)))
    (hfn : ∀ i, (eLpNorm (f i) p (volume.restrict (Icc 0 U))).toReal ≤ J)
    (hgn : (eLpNorm g p (volume.restrict (Icc 0 U))).toReal ≤ J)
    (hlim : Tendsto (fun i => ((hf i).mono_exponent hp).toLp (f i)) l
      (𝓝 ((hg.mono_exponent hp).toLp g)))
    {x : ι → WaveState U V} {y : WaveState U V}
    (hx : ∀ i, IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp (hf i) (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp (hf i)) (x i))
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hg (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hg) y)
    (hxr : ∀ i s t, ρ ≤ (x i).1 s t 0) (hyr : ∀ s t, ρ ≤ y.1 s t 0) :
    Tendsto x l (𝓝 y) := by
  obtain ⟨T, _hT, hbound⟩ := exists_uniform_finite_state hU hU1 hV hUR hc hi hrc hr0 hφ hrd hρ hJ
  have hu : Tendsto (fun i => incomingWaveVelocity hUR hp (hf i)) l
      (𝓝 (incomingWaveVelocity hUR hp hg)) := by
    have heq (i : ι) := incomingL4Map_eq_velocity hU hUR hp (hf i)
    have heqg := incomingL4Map_eq_velocity hU hUR hp hg
    simpa only [Function.comp_def, heq, heqg] using
      (incomingL4Map_continuous hU (r 0)).tendsto _ |>.comp hlim
  have hz : Tendsto (fun i => incomingWaveCurve hU hUR hp (hf i) (horizonPhi h r 0)) l
      (𝓝 (incomingWaveCurve hU hUR hp hg (horizonPhi h r 0))) :=
    tendsto_const_nhds.add ((horizontalPrimitive_lipschitz hU).continuous.tendsto _ |>.comp hu)
  exact IsWaveIntegral.tendsto_of_bounds hx hy hρ hxr hyr
    (fun i => (hbound hp (hf i) (hfn i) (hx i) (hxr i)).1)
    (hbound hp hg hgn hy hyr).1 hz tendsto_const_nhds hu

theorem IsWaveIntegral.horizon_tendsto_zero_incoming {ι : Type*} {l : Filter ι}
    {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) {p : ℝ≥0∞} (hp : 4 ≤ p)
    {f : ι → ℝ → ℝ} (hf : ∀ i, MemLp (f i) p (volume.restrict (Icc 0 U)))
    (hfn : ∀ i, (eLpNorm (f i) p (volume.restrict (Icc 0 U))).toReal ≤ J)
    (hlim : Tendsto (fun i => (eLpNorm (f i) p (volume.restrict (Icc 0 U))).toReal) l (𝓝 0))
    {x : ι → WaveState U V} {y : WaveState U V}
    (hx : ∀ i, IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp (hf i) (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp (hf i)) (x i))
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp (f := 0) MemLp.zero (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp (f := 0) MemLp.zero) y)
    (hxr : ∀ i s t, ρ ≤ (x i).1 s t 0) (hyr : ∀ s t, ρ ≤ y.1 s t 0) :
    Tendsto x l (𝓝 y) := by
  apply IsWaveIntegral.horizon_tendsto hU hU1 hV hUR hc hi hrc hr0 hφ hrd hρ hJ hp hf MemLp.zero hfn
    (by simpa only [eLpNorm_zero, ENNReal.toReal_zero] using hJ) _ hx hy hxr hyr
  simp only [MemLp.toLp_zero]
  apply (tendsto_iff_norm_sub_tendsto_zero (f := fun i => ((hf i).mono_exponent hp).toLp (f i)) (b := 0)).2
  simp only [sub_zero]
  exact squeeze_zero (fun i => norm_nonneg _) (fun i => incomingL4_norm_le_lp hU1 hp (hf i)) hlim

end CauchyHorizon
