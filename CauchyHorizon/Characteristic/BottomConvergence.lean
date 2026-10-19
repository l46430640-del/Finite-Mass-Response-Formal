import CauchyHorizon.Characteristic.FiniteStability
import CauchyHorizon.Characteristic.ConstraintWave
import CauchyHorizon.Reduced.RadialConvergence
import CauchyHorizon.Reduced.RadialLevel
import CauchyHorizon.Analysis.InverseConvergence
import CauchyHorizon.Radial.CriticalWeight

/-! Actual finite-time bottom traces on independently selected radius charts. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon

set_option maxHeartbeats 3000000 in
theorem IsWaveIntegral.horizon_bottom_tendsto {ι : Type*} {l : Filter ι}
    (B : Background) {U V Y Z : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) {p : ℝ≥0∞} (hp : 4 ≤ p)
    {f : ι → ℝ → ℝ} (hf : ∀ i, MemLp (f i) p (volume.restrict (Icc 0 U)))
    (hfn : ∀ i, (eLpNorm (f i) p (volume.restrict (Icc 0 U))).toReal ≤ J)
    (hlim : Tendsto (fun i => (eLpNorm (f i) p (volume.restrict (Icc 0 U))).toReal) l (𝓝 0))
    (hsupport : ∀ η : ℝ, 0 < η → ∀ᶠ i in l, ∀ u ∈ Icc η U, f i u = 0)
    {x : ι → WaveState U V} {y : WaveState U V}
    (hx : ∀ i, IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp (hf i) (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR hp (hf i)) (x i))
    (hy : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp (f := 0) MemLp.zero (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR hp (f := 0) MemLp.zero) y)
    (hxr : ∀ i u v, ρ ≤ (x i).1 u v 0) (hyr : ∀ u v, ρ ≤ y.1 u v 0)
    (hY : B.inner < Y) (hYZ : Y < Z) (hZ : Z < B.event) (v : Icc 0 V)
    (χ : ι → C(Icc (0 : ℝ) (Z - Y), Icc (0 : ℝ) U))
    (χ₀ : C(Icc (0 : ℝ) (Z - Y), Icc (0 : ℝ) U))
    (hχ : ∀ i w, (x i).1 (χ i w) v 0 = Z - w)
    (hχ₀ : ∀ w, y.1 (χ₀ w) v 0 = Z - w)
    (hχpos : ∀ w, 0 < (χ₀ w : ℝ)) (hL₀ : ∀ w, y.2.1 (χ₀ w) v 0 ≠ 0)
    (W : C(Icc (0 : ℝ) (Z - Y), ℝ)) {A : ι → ℝ} (hA : Tendsto A l (𝓝 0)) :
    let ν := fun i => radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp (hf i) (horizonPhi h r 0)) (x i).1 (hx i).choose
    let ν₀ := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp (f := 0) MemLp.zero (horizonPhi h r 0)) y.1 hy.choose
    let ζ := fun i w => (r 0 - (χ i w : ℝ)) * f i (χ i w) +
      scalarTransportCorrection hV (ν i) (x i).2.1 (χ i w) v
    let q := fun i w => Real.exp (B.innerRate * v) * (χ i w : ℝ) * ζ i w /
      B.criticalWeight (Z - w) - W w * A i
    let q₀ := fun w => Real.exp (B.innerRate * v) * (χ₀ w : ℝ) *
      scalarTransportCorrection hV ν₀ y.2.1 (χ₀ w) v / B.criticalWeight (Z - w)
    let F := fun i w => (-1 / (x i).2.1 (χ i w) v 0) * q i w ^ 2
    let F₀ := fun w => (-1 / y.2.1 (χ₀ w) v 0) * q₀ w ^ 2
    Tendsto χ l (𝓝 χ₀) ∧ TendstoUniformly F F₀ l ∧
      Tendsto (fun i => ∫ w in (0 : ℝ)..(Z - Y), F i (projIcc 0 (Z - Y) (sub_nonneg.2 hYZ.le) w)) l
        (𝓝 (∫ w in (0 : ℝ)..(Z - Y), F₀ (projIcc 0 (Z - Y) (sub_nonneg.2 hYZ.le) w))) := by
  classical
  intro ν ν₀ ζ q q₀ F F₀
  let K := Icc (0 : ℝ) (Z - Y)
  have hw : 0 ≤ Z - Y := sub_nonneg.2 hYZ.le
  have hxlim := IsWaveIntegral.horizon_tendsto_zero_incoming hU hU1 hV hUR
    hc hi hrc hr0 hφ hrd hρ hJ hp hf hfn hlim hx hy hxr hyr
  let E : Fin 3 → WaveRectangle U V →L[ℝ] C(Icc 0 U, ℝ) := fun j =>
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
    ((ContinuousLinearMap.proj j).comp (ContinuousMap.evalCLM ℝ v))
  have hRlim := (E 0).continuous.tendsto y.1 |>.comp hxlim.fst_nhds
  have hanti := hy.radial_strictAnti hy.choose rfl
    (incomingWave_constraint_data hU hUR hp (f := 0) MemLp.zero (horizonPhi h r 0)).1 v
    (fun u => (hy.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp MemLp.zero u v).2.2.1)
  have hχlim : Tendsto χ l (𝓝 χ₀) := continuous_inverse_coordinates_tendsto hanti.injective hRlim
    (fun i w => (hχ i w).trans (hχ₀ w).symm)
  let val : C(Icc (0 : ℝ) U, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  let u := fun i => val.comp (χ i)
  let u₀ := val.comp χ₀
  have hulim : Tendsto u l (𝓝 u₀) := tendsto_const_nhds.compCM hχlim
  obtain ⟨w₀, _hw₀, hmin⟩ := isCompact_univ.exists_isMinOn
    ⟨(⟨0, le_rfl, hw⟩ : K), mem_univ _⟩ u₀.continuous.continuousOn
  let η := u₀ w₀ / 2
  have hη : 0 < η := half_pos (hχpos w₀)
  have humin (w : K) : 2 * η ≤ u₀ w := by
    calc
      2 * η = u₀ w₀ := by dsimp only [η]; ring
      _ ≤ u₀ w := hmin (mem_univ w)
  have hdiff : Tendsto (fun i => ‖u i - u₀‖) l (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hulim
  have hvanish : ∀ᶠ i in l, ∀ w : K, f i (χ i w) = 0 := by
    filter_upwards [hdiff.eventually_lt_const hη, hsupport η hη] with i hi hs w
    apply hs _ ⟨?_, (χ i w).property.2⟩
    have he := (ContinuousMap.norm_coe_le_norm (u i - u₀) w).trans_lt hi
    change |u i w - u₀ w| < η at he
    have hh := (abs_lt.1 he).1
    change η ≤ u i w
    linarith only [hh, humin w]
  have hnlim : Tendsto ν l (𝓝 ν₀) :=
    (IsWaveIntegral.radial_tendsto hx hy (fun i => (hx i).choose) hy.choose hxlim.fst_nhds).1
  let P : WaveRectangle U V →L[ℝ] C(Icc 0 U, C(Icc 0 V, ℝ)) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
      (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj (1 : Fin 3)))
  let I : C(Icc 0 U, C(Icc 0 V, ℝ)) →L[ℝ] C(Icc 0 U, C(Icc 0 V, ℝ)) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (continuousPrimitiveL hV)
  have hcor : Tendsto (fun i => scalarTransportCorrection hV (ν i) (x i).2.1) l
      (𝓝 (scalarTransportCorrection hV ν₀ y.2.1)) :=
    I.continuous.tendsto _ |>.comp (hnlim.neg.mul (P.continuous.tendsto _ |>.comp hxlim.snd_nhds.fst_nhds))
  let Ev : C(Icc 0 U, C(Icc 0 V, ℝ)) →L[ℝ] C(Icc 0 U, ℝ) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (ContinuousMap.evalCLM ℝ v)
  let S := fun i => (Ev (scalarTransportCorrection hV (ν i) (x i).2.1)).comp (χ i)
  let S₀ := (Ev (scalarTransportCorrection hV ν₀ y.2.1)).comp χ₀
  have hSlim : Tendsto S l (𝓝 S₀) := (Ev.continuous.tendsto _ |>.comp hcor).compCM hχlim
  let Lm := fun i => (E 0 (x i).2.1).comp (χ i)
  let L₀ := (E 0 y.2.1).comp χ₀
  have hLlim : Tendsto Lm l (𝓝 L₀) :=
    ((E 0).continuous.tendsto _ |>.comp hxlim.snd_nhds.fst_nhds).compCM hχlim
  have hunit : IsUnit L₀ := L₀.isUnit_iff_forall_ne_zero.2 hL₀
  have hinv : ContinuousAt (Ring.inverse : C(K, ℝ) → C(K, ℝ)) L₀ := by
    simpa only [hunit.unit_spec] using NormedRing.inverse_continuousAt hunit.unit
  have hLn : ∀ᶠ i in l, ∀ w, Lm i w ≠ 0 :=
    (hLlim.eventually (Units.isOpen.mem_nhds hunit)).mono (fun i hi => (Lm i).isUnit_iff_forall_ne_zero.1 hi)
  have hband (w : K) : Z - (w : ℝ) ∈ Ioo B.inner B.event := by
    constructor <;> linarith only [hY, hZ, w.property.1, w.property.2]
  let Q : C(K, ℝ) := ⟨fun w => (B.criticalWeight (Z - w))⁻¹,
    ((B.criticalWeight_continuousOn.comp_continuous (continuous_const.sub continuous_subtype_val) hband).inv₀
      (fun w => (B.criticalWeight_pos (hband w)).ne'))⟩
  let Qn := fun i => Real.exp (B.innerRate * v) • (u i * S i * Q) - A i • W
  let Q₀ := Real.exp (B.innerRate * v) • (u₀ * S₀ * Q)
  have hQlim : Tendsto Qn l (𝓝 Q₀) := by
    simpa only [zero_smul, sub_zero] using
      ((hulim.mul hSlim).mul tendsto_const_nhds).const_smul (Real.exp (B.innerRate * v)) |>.sub
        (hA.smul tendsto_const_nhds)
  let G := fun i => -Ring.inverse (Lm i) * Qn i ^ 2
  let G₀ := -Ring.inverse L₀ * Q₀ ^ 2
  have hGlim : Tendsto G l (𝓝 G₀) := (hinv.tendsto.comp hLlim).neg.mul (hQlim.pow 2)
  have heq₀ (w : K) : G₀ w = F₀ w := by
    simp only [G₀, Q₀, ContinuousMap.mul_apply, ContinuousMap.neg_apply, ContinuousMap.pow_apply,
      ContinuousMap.smul_apply, continuousMap_inverse_apply L₀ hL₀, smul_eq_mul]
    change -(y.2.1 (χ₀ w) v 0)⁻¹ *
      (Real.exp (B.innerRate * v) * ((χ₀ w : ℝ) *
        scalarTransportCorrection hV ν₀ y.2.1 (χ₀ w) v * (B.criticalWeight (Z - w))⁻¹)) ^ 2 = _
    dsimp only [F₀, q₀]
    simp only [div_eq_mul_inv]
    ring
  have heq : ∀ᶠ i in l, ∀ w : K, G i w = F i w := by
    filter_upwards [hvanish, hLn] with i hi hni w
    simp only [G, Qn, ContinuousMap.mul_apply, ContinuousMap.neg_apply, ContinuousMap.pow_apply,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, continuousMap_inverse_apply (Lm i) hni, smul_eq_mul]
    change -((x i).2.1 (χ i w) v 0)⁻¹ *
      (Real.exp (B.innerRate * v) * ((χ i w : ℝ) *
        scalarTransportCorrection hV (ν i) (x i).2.1 (χ i w) v * (B.criticalWeight (Z - w))⁻¹) - A i * W w) ^ 2 = _
    dsimp only [F, q, ζ]
    rw [hi w]
    simp only [mul_zero, zero_add, div_eq_mul_inv]
    ring
  refine ⟨hχlim, ?_, ?_⟩
  · have hh := ContinuousMap.tendsto_iff_tendstoUniformly.1 hGlim
    change TendstoUniformly (fun i w => G i w) (fun w => G₀ w) l at hh
    simp only [heq₀] at hh
    exact (tendstoUniformly_congr (heq.mono (fun _ hi => funext hi))).1 hh
  · let J : C(K, ℝ) →L[ℝ] ℝ :=
      (ContinuousMap.evalCLM ℝ (⟨Z - Y, hw, le_rfl⟩ : K)).comp (continuousPrimitiveL hw)
    have hh := J.continuous.tendsto G₀ |>.comp hGlim
    change Tendsto (fun i => ∫ w in (0 : ℝ)..(Z - Y), G i (projIcc 0 (Z - Y) hw w)) l
      (𝓝 (∫ w in (0 : ℝ)..(Z - Y), G₀ (projIcc 0 (Z - Y) hw w))) at hh
    simp only [heq₀] at hh
    apply hh.congr'
    filter_upwards [heq] with i hi
    exact intervalIntegral.integral_congr (fun w _ => hi _)

end CauchyHorizon
