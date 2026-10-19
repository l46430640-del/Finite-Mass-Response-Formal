import CauchyHorizon.Characteristic.FiniteKappa
import CauchyHorizon.Reduced.ConformalRegularity
import CauchyHorizon.Reduced.FiniteSource
import CauchyHorizon.Reduced.FiniteState

/-! Uniform finite-rectangle bounds for every component of the actual mixed state. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem exists_uniform_finite_state_on_subrectangles {M e Λ Vmax : ℝ} {h r : ℝ → ℝ}
    (hVmax0 : 0 ≤ Vmax) (hrp : 0 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ T : ℝ, 0 < T ∧
      ∀ {U V : ℝ} (hU : 0 ≤ U) (_hU1 : U ≤ 1) (hV : 0 ≤ V), V ≤ Vmax → ∀ hUR : U < r 0,
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ J →
      ∀ {x : WaveState U V}
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ u v, ρ ≤ x.1 u v 0) →
        ‖x‖ ≤ T ∧ ‖rectangleSource hU e Λ x hx.choose‖ ≤ T ∧
        ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
          |x.2.2 u v 2| ≤ r 0 * (f u) ^ 2 + T * (|f u| + 1) := by
  obtain ⟨R, A, C, _hR, hA, hC, hgeom⟩ :=
    exists_uniform_finite_geometry_on_subrectangles (Vmax := Vmax) hc hi hrc hr0 hφ hrd hρ
  obtain ⟨B, hB, hscalar⟩ := exists_uniform_finite_scalar_on_subrectangles hVmax0 hrp hc hi hrc hr0 hφ hrd hρ hJ
  obtain ⟨_k, w, _hk, hw, hkappa⟩ := exists_uniform_finite_kappa_on_subrectangles hVmax0 hrp hc hi hrc hr0 hφ hrd hρ hJ
  let N := Real.exp (C * Vmax)
  let O := 4 * N
  let L := |Real.log w| + |Real.log O|
  have hN : 0 ≤ N := (Real.exp_pos _).le
  obtain ⟨S, hS, hsource⟩ := exists_waveSource_bound e Λ (R := R) (L := L) hρ (add_nonneg hA hB.le) hN
  let S₀ := S * (B + 1)
  let D := 1 + J + r 0 * J ^ 2
  let Z := ‖(![r 0, horizonPhi h r 0, Real.log 4] : WaveVector)‖ + D
  let H := ‖horizonWaveVelocity M e Λ Vmax hc hi hrc hr0‖
  let F := S₀ * (D + 1)
  let X := (Z + Vmax * (H + F)) + (H + F) + (D + Vmax * F)
  let T := 1 + X + F + Vmax * S₀
  have hS₀ : 0 ≤ S₀ := mul_nonneg hS (by positivity)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hZ : 0 ≤ Z := add_nonneg (norm_nonneg _) hD
  have hH : 0 ≤ H := norm_nonneg _
  have hF : 0 ≤ F := mul_nonneg hS₀ (by positivity)
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hTX : X ≤ T := by dsimp only [T]; linarith [mul_nonneg hVmax0 hS₀]
  have hTF : F ≤ T := by dsimp only [T]; linarith [mul_nonneg hVmax0 hS₀]
  have hTS : Vmax * S₀ ≤ T := by dsimp only [T]; linarith
  refine ⟨T, by dsimp only [T]; positivity, ?_⟩
  intro U V hU hU1 hV hVmax hUR p hp f hf hfn x hx hlo
  have hg := hgeom hU hV hVmax hUR hp hf hx hlo
  have hs := hscalar hU hU1 hV hVmax hUR hp hf hfn hx hlo
  have hk := hkappa hU hU1 hV hVmax hUR hp hf hfn hx hlo
  have hn (u : Icc 0 U) (v : Icc 0 V) :
      |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v| ≤ N := by
    have hneg := neg_pos.1 ((Real.exp_pos _).trans_le (hg u v).2.2.2.1)
    rw [abs_of_neg hneg]
    exact (hg u v).2.2.2.2.1.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (v.property.2.trans hVmax) hC))
  have hell (u : Icc 0 U) (v : Icc 0 V) : |x.1 u v 2| ≤ L := by
    have hl := Real.log_le_log hw (hk u v).2
    rw [Real.log_exp] at hl
    have ho : Real.exp (x.1 u v 2) ≤ O :=
      (hg u v).2.2.2.2.2.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (v.property.2.trans hVmax) hC)) (by norm_num))
    have hu := Real.log_le_log (Real.exp_pos _) ho
    rw [Real.log_exp] at hu
    apply abs_le.2
    dsimp only [L]
    constructor <;> linarith [neg_abs_le (Real.log w), le_abs_self (Real.log O),
      abs_nonneg (Real.log w), abs_nonneg (Real.log O)]
  have hinu := (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1
  have hbound : ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      ‖rectangleSource hU e Λ x hx.choose u v‖ ≤ S₀ * (|f u| + 1) := by
    filter_upwards [rectangleSource_ae hU e Λ x hx.choose, hx.radialNu_ae hx.choose hinu, hs.2.1]
      with u he hnu hphi
    intro v
    let a := projIcc 0 U hU u
    have hd : |x.2.2 u v 0| ≤ N := by rw [hnu v]; exact hn a v
    have hv1 : |x.2.1 a v 1| ≤ B := ((waveCoordinateField 1 x.2.1 a).norm_coe_le_norm v).trans (hs.1 a)
    rw [he v]
    have hb := hsource (x.1 a v) (x.2.2 u v) (x.2.1 a v) (hlo a v) (hg a v).1 (hell a v)
      ((hg a v).2.2.1.trans (le_add_of_nonneg_right hB.le)) (hv1.trans (le_add_of_nonneg_left hA)) hd
    calc
      _ ≤ S * (|x.2.2 u v 1| + 1) := hb
      _ ≤ S * (B * (|f u| + 1) + 1) := mul_le_mul_of_nonneg_left (add_le_add_left (hphi v) 1) hS
      _ ≤ _ := by dsimp only [S₀]; nlinarith only [mul_nonneg hS (abs_nonneg (f u))]
  have hinput : ‖incomingWaveVelocity hUR hp hf‖ ≤ D := incomingWaveVelocity_norm_le hU hU1 hUR hp hf hfn
  have hFn : ‖rectangleSource hU e Λ x hx.choose‖ ≤ F := by
    have hb : ∀ᵐ u ∂volume.restrict (Icc 0 U),
        ‖rectangleSource hU e Λ x hx.choose u‖ ≤ S₀ * (‖incomingWaveVelocity hUR hp hf u‖ + 1) := by
      filter_upwards [hbound, incomingWaveVelocity_ae hUR hp hf] with u hu hfEq
      have hcoord : |f u| ≤ ‖incomingWaveVelocity hUR hp hf u‖ := by
        have hh := norm_le_pi_norm (incomingWaveVelocity hUR hp hf u) (1 : Fin 3)
        rw [hfEq] at hh ⊢
        exact hh
      apply (ContinuousMap.norm_le _ (mul_nonneg hS₀ (by positivity))).2
      intro v
      exact (hu v).trans (mul_le_mul_of_nonneg_left (add_le_add_left hcoord 1) hS₀)
    exact (l2_norm_le_affine_majorant hU hS₀ _ _ hb).trans
      (mul_le_mul_of_nonneg_left (add_le_add hinput (Real.sqrt_le_one.2 hU1)) hS₀)
  have hzIn : ‖incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)‖ ≤ Z := by
    refine (incomingWaveCurve_norm_le hU hUR hp hf (horizonPhi h r 0)).trans (add_le_add_right ?_ _)
    exact (mul_le_mul_of_nonneg_left hinput (Real.sqrt_nonneg U)).trans
      (mul_le_of_le_one_left hD (Real.sqrt_le_one.2 hU1))
  obtain ⟨hv, hd, hz⟩ := hx.finite_state_bound hx.choose hFn
  have hHloc : ‖horizonWaveVelocity M e Λ V hc hi hrc hr0‖ ≤ H := horizonWaveVelocity_norm_mono hc hi hrc hr0 hVmax
  have hv' : ‖x.2.1‖ ≤ H + F := hv.trans (add_le_add hHloc
    (mul_le_of_le_one_left hF (Real.sqrt_le_one.2 hU1)))
  have hd' : ‖x.2.2‖ ≤ D + Vmax * F := hd.trans (add_le_add hinput (mul_le_mul_of_nonneg_right hVmax hF))
  have hz' : ‖x.1‖ ≤ Z + Vmax * (H + F) := hz.trans (add_le_add hzIn
    (mul_le_mul hVmax (add_le_add hHloc (mul_le_of_le_one_left hF (Real.sqrt_le_one.2 hU1)))
      (by positivity) hVmax0))
  have hxnorm : ‖x‖ ≤ X := (waveState_norm_equivalence x).1.trans (add_le_add (add_le_add hz' hv') hd')
  refine ⟨hxnorm.trans hTX, hFn.trans hTF, ?_⟩
  filter_upwards [hx.transverse_coordinate_primitive hx.choose 2, hbound,
    incomingWaveVelocity_ae hUR hp hf, ae_restrict_mem measurableSet_Icc] with u hu hsrc hfEq hum
  intro v
  have he := congrArg (fun z : C(Icc 0 V, ℝ) => z v) hu
  change x.2.2 u v 2 = incomingWaveVelocity hUR hp hf u 2 +
    ∫ t in (0 : ℝ)..v, rectangleSource hU e Λ x hx.choose u (projIcc 0 V hV t) 2 at he
  have hcorr := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (v : ℝ)) (C := S₀ * (|f u| + 1))
    (fun t _ => (norm_le_pi_norm (rectangleSource hU e Λ x hx.choose u (projIcc 0 V hV t)) 2).trans (hsrc _))
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg v.property.1] at hcorr
  have hin : |incomingWaveVelocity hUR hp hf u 2| ≤ r 0 * (f u) ^ 2 := by
    rw [hfEq]
    change |-(r 0 - u) * (f u) ^ 2| ≤ r 0 * (f u) ^ 2
    rw [abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.2 (hum.2.trans hUR.le)), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right (by linarith [hum.1]) (sq_nonneg _)
  have hc' := mul_le_mul_of_nonneg_left (v.property.2.trans hVmax) (mul_nonneg hS₀ (by positivity : 0 ≤ |f u| + 1))
  rw [he]
  refine (abs_add_le _ _).trans (add_le_add hin (hcorr.trans ?_))
  nlinarith only [hc', mul_le_mul_of_nonneg_right hTS (by positivity : 0 ≤ |f u| + 1)]

theorem exists_uniform_finite_state {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ T : ℝ, 0 < T ∧
      ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ J →
      ∀ {x : WaveState U V}
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (∀ u v, ρ ≤ x.1 u v 0) →
        ‖x‖ ≤ T ∧ ‖rectangleSource hU e Λ x hx.choose‖ ≤ T ∧
        ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
          |x.2.2 u v 2| ≤ r 0 * (f u) ^ 2 + T * (|f u| + 1) := by
  obtain ⟨T, hT, hb⟩ := exists_uniform_finite_state_on_subrectangles hV (hU.trans_lt hUR) hc hi hrc hr0 hφ hrd hρ hJ
  exact ⟨T, hT, hb hU hU1 hV le_rfl hUR⟩

end CauchyHorizon
