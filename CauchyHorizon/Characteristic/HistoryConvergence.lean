import CauchyHorizon.Characteristic.BottomConvergence

/-! Actual scalar histories on moving fixed-radius curves. -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon

set_option maxHeartbeats 3000000 in
theorem IsWaveIntegral.horizon_scalar_history_tendsto {ι : Type*} {L : Filter ι}
    (B : Background) {U V Y a b : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbV : b ≤ V)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) {p : ℝ≥0∞} (hp : 4 ≤ p)
    {f : ι → ℝ → ℝ} (hf : ∀ i, MemLp (f i) p (volume.restrict (Icc 0 U)))
    (hfn : ∀ i, (eLpNorm (f i) p (volume.restrict (Icc 0 U))).toReal ≤ J)
    (hlim : Tendsto (fun i => (eLpNorm (f i) p (volume.restrict (Icc 0 U))).toReal) L (𝓝 0))
    (hsupport : ∀ η : ℝ, 0 < η → ∀ᶠ i in L, ∀ u ∈ Icc η U, f i u = 0)
    {x : ι → WaveState U V} {y : WaveState U V}
    (hx : ∀ i, IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp (hf i) (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR hp (hf i)) (x i))
    (hy : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp (f := 0) MemLp.zero (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR hp (f := 0) MemLp.zero) y)
    (hxr : ∀ i u v, ρ ≤ (x i).1 u v 0) (hyr : ∀ u v, ρ ≤ y.1 u v 0) :
    let v := fun t : Icc a b => (⟨t, ha.trans t.property.1, t.property.2.trans hbV⟩ : Icc 0 V)
    ∀ (χ : ι → C(Icc a b, Icc (0 : ℝ) U)) (χ₀ : C(Icc a b, Icc (0 : ℝ) U)),
      (∀ i t, (x i).1 (χ i t) (v t) 0 = Y) → (∀ t, y.1 (χ₀ t) (v t) 0 = Y) →
      (∀ t, 0 < (χ₀ t : ℝ)) →
      let ν := fun i => radialNuField hV B.charge B.cosmological
        (incomingWaveCurve hU hUR hp (hf i) (horizonPhi h r 0)) (x i).1 (hx i).choose
      let ν₀ := radialNuField hV B.charge B.cosmological
        (incomingWaveCurve hU hUR hp (f := 0) MemLp.zero (horizonPhi h r 0)) y.1 hy.choose
      let θ := fun i (t : Icc a b) => Real.exp (B.innerRate * (t : ℝ)) * (Y * (x i).2.1 (χ i t) (v t) 1)
      let θ₀ := fun t : Icc a b => Real.exp (B.innerRate * (t : ℝ)) * (Y * y.2.1 (χ₀ t) (v t) 1)
      let ζ := fun i (t : Icc a b) => Real.exp (B.innerRate * (t : ℝ)) * (χ i t : ℝ) *
        ((r 0 - (χ i t : ℝ)) * f i (χ i t) +
          scalarTransportCorrection hV (ν i) (x i).2.1 (χ i t) (v t)) / B.criticalWeight Y
      let ζ₀ := fun t : Icc a b => Real.exp (B.innerRate * (t : ℝ)) * (χ₀ t : ℝ) *
        scalarTransportCorrection hV ν₀ y.2.1 (χ₀ t) (v t) / B.criticalWeight Y
      Tendsto χ L (𝓝 χ₀) ∧ TendstoUniformly θ θ₀ L ∧ TendstoUniformly ζ ζ₀ L ∧
        (∀ᶠ i in L,
          MemLp (fun t => θ i (projIcc a b hab t)) 2 (volume.restrict (Icc a b)) ∧
          MemLp (fun t => ζ i (projIcc a b hab t)) 2 (volume.restrict (Icc a b))) ∧
        Tendsto (fun i => ∫ t in a..b,
          (θ i (projIcc a b hab t) - θ₀ (projIcc a b hab t)) ^ 2 +
            (ζ i (projIcc a b hab t) - ζ₀ (projIcc a b hab t)) ^ 2) L (𝓝 0) := by
  classical
  intro v χ χ₀ hχ hχ₀ hpos ν ν₀ θ θ₀ ζ ζ₀
  let K := Icc a b
  let D := Icc (0 : ℝ) U × Icc (0 : ℝ) V
  let vc : C(K, Icc (0 : ℝ) V) := ⟨v, continuous_subtype_val.subtype_mk _⟩
  let γ := fun i => (χ i).prodMk vc
  let γ₀ := χ₀.prodMk vc
  have hxlim := IsWaveIntegral.horizon_tendsto_zero_incoming hU hU1 hV hUR
    hc hi hrc hr0 hφ hrd hρ hJ hp hf hfn hlim hx hy hxr hyr
  let P : Fin 3 → WaveRectangle U V →L[ℝ] C(Icc 0 U, C(Icc 0 V, ℝ)) := fun j =>
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
      (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V) (ContinuousLinearMap.proj j))
  let E := fun j (z : WaveRectangle U V) => (P j z).uncurry
  have hEc (j : Fin 3) : Continuous (E j) := ContinuousMap.continuous_uncurry.comp (P j).continuous
  let time : C(D, ℝ) := ⟨fun z => z.2, continuous_subtype_val.comp continuous_snd⟩
  let R := fun z : WaveRectangle U V => (E 0 z).prodMk time
  have hRc : Continuous R := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((hEc 0 |>.comp continuous_fst).eval continuous_snd).prodMk (time.continuous.comp continuous_snd)
  have hanti (t : Icc 0 V) := hy.radial_strictAnti hy.choose rfl
    (incomingWave_constraint_data hU hUR hp (f := 0) MemLp.zero (horizonPhi h r 0)).1 t
    (fun u => (hy.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp MemLp.zero u t).2.2.1)
  have hinj : Function.Injective (R y.1) := by
    rintro ⟨u, t⟩ ⟨u', t'⟩ hh
    have ht : t = t' := Subtype.ext (congrArg Prod.snd hh)
    subst t'
    have hu : u = u' := (hanti t).injective (congrArg Prod.fst hh)
    subst u'
    rfl
  have hγlim : Tendsto γ L (𝓝 γ₀) := continuous_inverse_coordinates_tendsto hinj
    (hRc.tendsto _ |>.comp hxlim.fst_nhds) (fun i t => Prod.ext ((hχ i t).trans (hχ₀ t).symm) rfl)
  have hχlim : Tendsto χ L (𝓝 χ₀) :=
    (tendsto_const_nhds (x := (ContinuousMap.fst : C(D, Icc (0 : ℝ) U)))).compCM hγlim
  let val : C(Icc (0 : ℝ) U, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  let u := fun i => val.comp (χ i)
  let u₀ := val.comp χ₀
  have hulim : Tendsto u L (𝓝 u₀) := tendsto_const_nhds.compCM hχlim
  obtain ⟨t₀, _ht₀, hmin⟩ := isCompact_univ.exists_isMinOn
    ⟨(⟨a, le_rfl, hab⟩ : K), mem_univ _⟩ u₀.continuous.continuousOn
  let η := u₀ t₀ / 2
  have hη : 0 < η := half_pos (hpos t₀)
  have humin (t : K) : 2 * η ≤ u₀ t := by
    calc
      2 * η = u₀ t₀ := by dsimp only [η]; ring
      _ ≤ u₀ t := hmin (mem_univ t)
  have hdiff : Tendsto (fun i => ‖u i - u₀‖) L (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hulim
  have hvanish : ∀ᶠ i in L, ∀ t : K, f i (χ i t) = 0 := by
    filter_upwards [hdiff.eventually_lt_const hη, hsupport η hη] with i hi hs t
    apply hs _ ⟨?_, (χ i t).property.2⟩
    have he := (ContinuousMap.norm_coe_le_norm (u i - u₀) t).trans_lt hi
    change |u i t - u₀ t| < η at he
    have hh := (abs_lt.1 he).1
    change η ≤ u i t
    linarith only [hh, humin t]
  have hnlim : Tendsto ν L (𝓝 ν₀) :=
    (IsWaveIntegral.radial_tendsto hx hy (fun i => (hx i).choose) hy.choose hxlim.fst_nhds).1
  let I : C(Icc 0 U, C(Icc 0 V, ℝ)) →L[ℝ] C(Icc 0 U, C(Icc 0 V, ℝ)) :=
    ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (continuousPrimitiveL hV)
  have hcor : Tendsto (fun i => scalarTransportCorrection hV (ν i) (x i).2.1) L
      (𝓝 (scalarTransportCorrection hV ν₀ y.2.1)) :=
    I.continuous.tendsto _ |>.comp (hnlim.neg.mul ((P 1).continuous.tendsto _ |>.comp hxlim.snd_nhds.fst_nhds))
  let S := fun i => (scalarTransportCorrection hV (ν i) (x i).2.1).uncurry.comp (γ i)
  let S₀ := (scalarTransportCorrection hV ν₀ y.2.1).uncurry.comp γ₀
  have hSlim : Tendsto S L (𝓝 S₀) :=
    (ContinuousMap.continuous_uncurry.tendsto _ |>.comp hcor).compCM hγlim
  let A : C(K, ℝ) := ⟨fun t => Real.exp (B.innerRate * (t : ℝ)),
    (continuous_const.mul continuous_subtype_val).rexp⟩
  let F := fun i => A * (Y • ((E 1 (x i).2.1).comp (γ i)))
  let F₀ := A * (Y • ((E 1 y.2.1).comp γ₀))
  let G := fun i => (B.criticalWeight Y)⁻¹ • (A * u i * S i)
  let G₀ := (B.criticalWeight Y)⁻¹ • (A * u₀ * S₀)
  have hFlim : Tendsto F L (𝓝 F₀) := tendsto_const_nhds.mul
    ((((hEc 1).tendsto _ |>.comp hxlim.snd_nhds.fst_nhds).compCM hγlim).const_smul Y)
  have hGlim : Tendsto G L (𝓝 G₀) := ((tendsto_const_nhds.mul hulim).mul hSlim).const_smul _
  have hFeq (i : ι) (t : K) : F i t = θ i t := rfl
  have hFeq₀ (t : K) : F₀ t = θ₀ t := rfl
  have hGeq₀ (t : K) : G₀ t = ζ₀ t := by
    change (B.criticalWeight Y)⁻¹ *
      (Real.exp (B.innerRate * (t : ℝ)) * (χ₀ t : ℝ) * scalarTransportCorrection hV ν₀ y.2.1 (χ₀ t) (v t)) = _
    dsimp only [ζ₀]
    rw [div_eq_mul_inv, mul_comm]
  have hGeq : ∀ᶠ i in L, ∀ t : K, G i t = ζ i t := by
    filter_upwards [hvanish] with i hi t
    change (B.criticalWeight Y)⁻¹ *
      (Real.exp (B.innerRate * (t : ℝ)) * (χ i t : ℝ) *
        scalarTransportCorrection hV (ν i) (x i).2.1 (χ i t) (v t)) = _
    dsimp only [ζ]
    rw [hi t, mul_zero, zero_add, div_eq_mul_inv, mul_comm]
  refine ⟨hχlim, ?_, ?_, ?_, ?_⟩
  · exact ContinuousMap.tendsto_iff_tendstoUniformly.1 hFlim
  · have hh := ContinuousMap.tendsto_iff_tendstoUniformly.1 hGlim
    change TendstoUniformly (fun i t => G i t) (fun t => G₀ t) L at hh
    simp only [hGeq₀] at hh
    exact (tendstoUniformly_congr (hGeq.mono (fun _ hi => funext hi))).1 hh
  · filter_upwards [hGeq] with i hi
    constructor
    · exact (intervalExtension hab (F i)).memLp_top.mono_exponent le_top
    · have hh : MemLp (fun t => G i (projIcc a b hab t)) 2 (volume.restrict (Icc a b)) :=
        (intervalExtension hab (G i)).memLp_top.mono_exponent le_top
      simpa only [hi] using hh
  · let energy := fun i => (F i - F₀) ^ 2 + (G i - G₀) ^ 2
    have helim : Tendsto energy L (𝓝 (0 : C(K, ℝ))) := by
      simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
        ((hFlim.sub (tendsto_const_nhds (x := F₀))).pow 2).add
          ((hGlim.sub (tendsto_const_nhds (x := G₀))).pow 2)
    let J : C(K, ℝ) →L[ℝ] ℝ :=
      (ContinuousMap.evalCLM ℝ (⟨b, hab, le_rfl⟩ : K)).comp (continuousPrimitiveL hab)
    have hh : Tendsto (fun i => J (energy i)) L (𝓝 0) := by
      simpa only [map_zero, Function.comp_def] using J.continuous.tendsto 0 |>.comp helim
    apply hh.congr'
    filter_upwards [hGeq] with i hi
    apply intervalIntegral.integral_congr
    intro t _
    simp only [intervalExtension_apply, energy, ContinuousMap.add_apply, ContinuousMap.pow_apply, ContinuousMap.sub_apply,
      hFeq, hFeq₀, hi, hGeq₀]

end CauchyHorizon
