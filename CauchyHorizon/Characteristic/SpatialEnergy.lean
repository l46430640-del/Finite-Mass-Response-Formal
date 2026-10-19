import CauchyHorizon.Characteristic.TwoAxisWave
import CauchyHorizon.Characteristic.ConstraintWave
import CauchyHorizon.Reduced.SpatialRadiation
import CauchyHorizon.Analysis.LogarithmicEnergy

/-! Uniform radiation energy on a shrinking domain with controlled geometry. -/

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace CauchyHorizon

set_option maxHeartbeats 1000000 in
theorem IsWaveIntegral.horizon_moving_spatial_energy
    {U V m e Λ a b k s ρ N L σ D H : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) (hcrit : k = a * b) (hks : k < s)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hσ : 0 < σ) (hD : 0 < D) (hH : 0 ≤ H)
    (hsmall : L * N / (σ * ρ ^ 2) ≤ (a - k) / 2)
    (hout : ∀ t ∈ Ici (0 : ℝ), |h t| ≤ H * Real.exp (-s * t))
    (w : C(Icc 0 V, ℝ)) (hw0 : ∀ v, 0 ≤ w v) (hw : Antitone w)
    (hwD : ∀ v, w v ≤ D * Real.exp (-a * v))
    {p : ℝ≥0∞} (hp : 4 ≤ p) (ℓ : ℝ) (B : ℝ →ᵇ ℝ)
    (hB : Integrable (fun t => B t ^ 2))
    (hf : MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hlo : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ w v → ρ ≤ x.1 u v 0)
    (hν : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ w v →
      |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        x.1 hx.choose u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ w v → |x.2.1 u v 0| ≤ L) :
    let M := movingSpatialRadiationEnvelope w hw0 a k σ x
    let E := 4 * H ^ 2 / (s - k) + 8 * (L * r 0 / ρ) ^ 2 * D ^ (2 * b) / a * ∫ t, B t ^ 2
    ((∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤ E) ∧
      ((∫ t in (0 : ℝ)..V,
        (movingSpatialRadiationEnvelope w hw0 a k 0 x (projIcc 0 V hV t)) ^ 2) ≤
          Real.exp (σ * D) ^ 2 * E) ∧
      ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ w v →
        (u : ℝ) * Real.exp (k * v) * |scalarTransportCorrection hV
          (radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            x.1 hx.choose) x.2.1 u v| ≤
          (N * D / ρ) * Real.exp (σ * D) * causalExpIntegral hV (a - k) M v := by
  let M := movingSpatialRadiationEnvelope w hw0 a k σ x
  let C := L * r 0 / ρ
  let O := fun t => Real.exp (k * t) * |h t|
  let G := fun t => Real.exp (k * t) *
    (∫ u in (0 : ℝ)..min U (D * Real.exp (-a * t)), |logarithmicIncoming b ℓ B u|)
  let E := 4 * H ^ 2 / (s - k) + 8 * C ^ 2 * D ^ (2 * b) / a * ∫ t, B t ^ 2
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hL (hU.trans_lt hUR).le) hρ.le
  have hka : k < a := by rw [hcrit]; nlinarith only [ha, hb1]
  have hM0 (v : Icc 0 V) : 0 ≤ M v := norm_nonneg (movingSpatialRadiationRows w hw0 a k σ x v)
  have hM := fun v => (movingSpatialRadiationEnvelope_le_iff (a := a) (k := k) (σ := σ)
    hU w hw0 x v).1 le_rfl
  have hin (u : Icc 0 U) : |incomingWaveCurve hU hUR hp hf (horizonPhi h r 0) u 0| ≤ r 0 := by
    rw [incomingWaveCurve_apply]
    change |r 0 - (u : ℝ)| ≤ r 0
    rw [abs_of_pos (sub_pos.2 (u.property.2.trans_lt hUR))]
    linarith only [u.property.1]
  have hkern := hx.outer_radiation_spatial_kernel_on hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1
    ha.le hρ hN hL hσ w hw0 hw hlo hin hν hlam M (fun u v hu => hM v u hu)
  have he (v : Icc 0 V) :
      x.1 ⟨0, le_rfl, hU⟩ v 0 * horizonWaveVelocity m e Λ V hc hi hrc hr0 v 1 = h v := by
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v]
    change r v * (h v / r v) = h v
    field_simp [hr0 v]
  have hinput (u : Icc 0 U) :
      (∫ t in (0 : ℝ)..u, |incomingWaveVelocity hUR hp hf t 1|) =
        ∫ t in (0 : ℝ)..u, |logarithmicIncoming b ℓ B t| := by
    simp only [intervalIntegral.integral_of_le u.property.1]
    apply integral_congr_ae
    have hs : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
    filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) (incomingWaveVelocity_ae hUR hp hf)] with t ht
    rw [ht]
    rfl
  have hfi := (logarithmicIncoming_primitive hb hU ℓ B).1.abs
  have hpc : ContinuousOn (fun u => ∫ t in (0 : ℝ)..u, |logarithmicIncoming b ℓ B t|)
      (Icc 0 U) := by
    simpa only [uIcc_of_le hU] using intervalIntegral.continuousOn_primitive_interval' hfi left_mem_uIcc
  let S : ℝ → Icc 0 U := fun t => ⟨min U (D * Real.exp (-a * t)),
    le_min hU (mul_nonneg hD.le (Real.exp_pos _).le), min_le_left _ _⟩
  have hSc : Continuous S := by fun_prop
  have hGc : Continuous G := by
    have hh := hpc.domRestrict.comp hSc
    change Continuous (fun t => ∫ u in (0 : ℝ)..min U (D * Real.exp (-a * t)),
      |logarithmicIncoming b ℓ B u|) at hh
    unfold G
    fun_prop
  have hOc : Continuous O := by unfold O; fun_prop
  have hFc : Continuous (fun t => O t + C * G t) := by fun_prop
  have hkernel (v : Icc 0 V) :
      M v ≤ O v + C * G v + (L * N / (σ * ρ ^ 2)) * causalExpIntegral hV (a - k) M v := by
    apply (movingSpatialRadiationEnvelope_le_iff hU w hw0 x v).2
    intro u hu
    have huS : (u : ℝ) ≤ S v := le_min u.property.2 (hu.trans (hwD v))
    have hint := intervalIntegral.integral_mono_interval le_rfl u.property.1 huS
      (Filter.Eventually.of_forall (fun t => abs_nonneg (logarithmicIncoming b ℓ B t)))
      (hfi.mono_set (by
        rw [uIcc_of_le (S v).property.1, uIcc_of_le hU]
        exact Icc_subset_Icc le_rfl (S v).property.2))
    have hh := hkern.2 u v hu
    rw [he, hinput] at hh
    have hsrc := mul_le_mul_of_nonneg_left hint
      (mul_nonneg hC (Real.exp_pos (k * v)).le)
    dsimp only [O, G, C, S] at hsrc ⊢
    nlinarith only [hh, hsrc]
  have hactual := causalExpIntegral_absorb_sq hV (sub_pos.2 hka)
    (show 0 ≤ L * N / (σ * ρ ^ 2) by positivity) hsmall M hM0
    ((hFc.pow 2).intervalIntegrable _ _) hkernel
  have hOi := weighted_exponential_energy hV hks hH hc hout
  have hGi := logarithmicIncoming_outer_energy_bound hU hV hD ha hb hcrit ℓ B hB
  have hsum : (∫ t in (0 : ℝ)..V, (O t + C * G t) ^ 2) ≤
      2 * (∫ t in (0 : ℝ)..V, O t ^ 2) + 2 * C ^ 2 * ∫ t in (0 : ℝ)..V, G t ^ 2 := by
    have hF2c : Continuous (fun t => (O t + C * G t) ^ 2) := by fun_prop
    have hRc : Continuous (fun t => 2 * O t ^ 2 + 2 * C ^ 2 * G t ^ 2) := by fun_prop
    have hh := intervalIntegral.integral_mono_on (μ := volume) hV
      (hF2c.intervalIntegrable _ _) (hRc.intervalIntegrable _ _)
      (fun t _ => by nlinarith only [sq_nonneg (O t - C * G t)])
    have hiO : IntervalIntegrable (fun t => 2 * O t ^ 2) volume 0 V :=
      ((hOc.pow 2).const_mul 2).intervalIntegrable _ _
    have hiG : IntervalIntegrable (fun t => 2 * C ^ 2 * G t ^ 2) volume 0 V :=
      ((hGc.pow 2).const_mul (2 * C ^ 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hiO hiG,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hh
    exact hh
  have henergy : (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤ E := by
    have hin' := mul_le_mul_of_nonneg_left hGi (by positivity : 0 ≤ 2 * C ^ 2)
    have hout' := mul_le_mul_of_nonneg_left hOi (by norm_num : (0 : ℝ) ≤ 2)
    have hs := hsum.trans (add_le_add hout' hin')
    exact (hactual.trans (mul_le_mul_of_nonneg_left hs (by norm_num))).trans_eq
      (by dsimp only [E]; field_simp; ring)
  have hscale (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ w v) :
      (u : ℝ) * Real.exp (a * v) ≤ D := by
    have hh := mul_le_mul_of_nonneg_right (hu.trans (hwD v)) (Real.exp_pos (a * v)).le
    simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] using hh
  have hweight (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ w v) :
      Real.exp (σ * u * Real.exp (a * v)) ≤ Real.exp (σ * D) := by
    apply Real.exp_le_exp.2
    have hh := mul_le_mul_of_nonneg_left (hscale u v hu) hσ.le
    nlinarith only [hh]
  have hcancel (u : Icc 0 U) (v : Icc 0 V) :
      Real.exp (σ * u * Real.exp (a * v)) *
        Real.exp (k * v - σ * u * Real.exp (a * v)) = Real.exp (k * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hunweight (v : Icc 0 V) : movingSpatialRadiationEnvelope w hw0 a k 0 x v ≤
      Real.exp (σ * D) * M v := by
    apply (movingSpatialRadiationEnvelope_le_iff hU w hw0 x v).2
    intro u hu
    have hh := mul_le_mul (hweight u v hu) (hM v u hu)
      (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (Real.exp_pos _).le
    rw [← mul_assoc, hcancel] at hh
    simpa only [zero_mul, sub_zero] using hh
  refine ⟨henergy, ?_, ?_⟩
  · have hMc : Continuous (fun t => M (projIcc 0 V hV t)) := by fun_prop
    have hTc : Continuous (fun t => movingSpatialRadiationEnvelope w hw0 a k 0 x
        (projIcc 0 V hV t)) := by fun_prop
    have hh := intervalIntegral.integral_mono_on (μ := volume) hV
      (f := fun t => movingSpatialRadiationEnvelope w hw0 a k 0 x (projIcc 0 V hV t) ^ 2)
      (g := fun t => Real.exp (σ * D) ^ 2 * M (projIcc 0 V hV t) ^ 2)
      ((hTc.pow 2).intervalIntegrable _ _) (((hMc.pow 2).const_mul (Real.exp (σ * D) ^ 2)).intervalIntegrable _ _)
      (fun t _ => by
        have h0 : 0 ≤ movingSpatialRadiationEnvelope w hw0 a k 0 x (projIcc 0 V hV t) :=
          norm_nonneg (movingSpatialRadiationRows w hw0 a k 0 x _)
        have hh := (sq_le_sq₀ h0
          (mul_nonneg (Real.exp_pos _).le (hM0 _))).2 (hunweight (projIcc 0 V hV t))
        simpa only [mul_pow] using hh)
    rw [intervalIntegral.integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg _))
  · intro u v hu
    have hQ : 0 ≤ causalExpIntegral hV (a - k) M v := intervalIntegral.integral_nonneg
      v.property.1 (fun t _ => mul_nonneg (Real.exp_pos _).le (hM0 _))
    have hh := mul_le_mul_of_nonneg_left (hkern.1 u v hu)
      (mul_nonneg u.property.1 (Real.exp_pos (σ * u * Real.exp (a * v))).le)
    have hcanc := hcancel u v
    have hbnd := mul_le_mul (hscale u v hu) (hweight u v hu) (Real.exp_pos _).le hD.le
    have hbnd' := mul_le_mul_of_nonneg_left hbnd (mul_nonneg (div_nonneg hN hρ.le) hQ)
    have he' := congrArg (fun q => (u : ℝ) *
      |scalarTransportCorrection hV (radialNuField hV e Λ
        (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose) x.2.1 u v| * q) hcanc
    ring_nf at hh hbnd' he' ⊢
    nlinarith only [hh, hbnd', he']

end CauchyHorizon
