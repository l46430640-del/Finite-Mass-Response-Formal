import CauchyHorizon.Reduced.ScalarTransport

/-! A continuous incoming scalar profile identifies the actual transverse derivative away from zero. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem IsWaveIntegral.scalar_hasDerivWithinAt_of_continuous
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
    {u : ℝ} (hu : u ∈ Ioc 0 U) (v : Icc 0 V) :
    HasDerivWithinAt (fun t => intervalExtension hU x.1 t v 1)
      ((zIn ⟨u, hu.1.le, hu.2⟩ 0 * f u +
        scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hx.choose)
          x.2.1 ⟨u, hu.1.le, hu.2⟩ v) / x.1 ⟨u, hu.1.le, hu.2⟩ v 0) (Icc 0 U) u := by
  let T : C(Icc 0 V, WaveVector) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (1 : Fin 3)).comp (ContinuousMap.evalCLM ℝ v)
  let X := T.compLpL 2 (volume.restrict (Icc 0 U)) x.2.2
  let C := scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hx.choose) x.2.1
  let F := fun t => (zIn (projIcc 0 U hU t) 0 * f t + C (projIcc 0 U hU t) v) /
    x.1 (projIcc 0 U hU t) v 0
  have hae : X =ᵐ[volume.restrict (Icc 0 U)] F := by
    filter_upwards [T.coeFn_compLpL x.2.2, hx.zeta_transport hx.choose hinu, hif] with t ht hz hf
    change X t = T (x.2.2 t) at ht
    rw [ht]
    change x.2.2 t v 1 = F t
    apply (eq_div_iff (hx.choose _ _)).2
    have hh := hz v
    rw [hf] at hh
    simpa only [mul_comm] using hh
  have hi : IntervalIntegrable F volume 0 U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
      (((Lp.memLp X).integrable (by norm_num)).congr hae)
  have hFc : ContinuousOn F (Ioi 0) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t _
      exact hx.choose _ _
  have hiu : IntervalIntegrable F volume 0 u := hi.mono_set (by
    rw [uIcc_of_le hu.1.le, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl hu.2)
  have hdf := intervalIntegral.integral_hasDerivAt_right hiu
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hFc u hu.1)
    (hFc.continuousAt (isOpen_Ioi.mem_nhds hu.1))
  have he (t : ℝ) (ht : t ∈ Icc 0 U) :
      intervalExtension hU x.1 t v 1 = T (ContinuousMap.const _ c + continuousPrimitive hV vOut) +
        ∫ w in (0 : ℝ)..t, F w := by
    have hh := congrArg (fun z : WaveRectangle U V => T (z ⟨t, ht⟩)) (hx.horizontal_identity hzin)
    have hp := congrArg (fun z : C(Icc 0 U, ℝ) => z ⟨t, ht⟩)
      (horizontalPrimitive_compLp hU T x.2.2)
    change (∫ w in (0 : ℝ)..t, X w) = T (horizontalPrimitive hU x.2.2 ⟨t, ht⟩) at hp
    have hI : (∫ w in (0 : ℝ)..t, X w) = ∫ w in (0 : ℝ)..t, F w := by
      simp only [intervalIntegral.integral_of_le ht.1]
      exact integral_congr_ae (ae_mono (Measure.restrict_mono
        (fun w hw => (show w ∈ Icc 0 U from ⟨hw.1.le, hw.2.trans ht.2⟩)) le_rfl) hae)
    rw [hI] at hp
    simp only [ContinuousMap.add_apply, map_add] at hh
    rw [← hp] at hh
    rw [intervalExtension_apply, projIcc_of_mem hU ht]
    exact hh
  have hd := (hdf.const_add (T (ContinuousMap.const _ c + continuousPrimitive hV vOut))).hasDerivWithinAt
    (s := Icc 0 U)
  have hd' := hd.congr_of_mem he (show u ∈ Icc 0 U from ⟨hu.1.le, hu.2⟩)
  simpa only [F, projIcc_of_mem hU (show u ∈ Icc 0 U from ⟨hu.1.le, hu.2⟩)] using hd'

theorem IsWaveIntegral.scalar_curve_continuous
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
    {s : Set ℝ} {g v : ℝ → ℝ} (hg : ContinuousOn g s) (hv : ContinuousOn v s)
    (hgu : ∀ t ∈ s, g t ∈ Ioc 0 U) :
    ContinuousOn (fun t =>
      intervalExtension hV (intervalExtension hU x.1 (g t)) (v t) 0 *
        derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) (v t) 1)
          (Icc 0 U) (g t)) s := by
  let C := scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hx.choose) x.2.1
  have hfc : ContinuousOn (fun t => f (g t)) s := hc.comp hg (fun t ht => (hgu t ht).1)
  have hcont : ContinuousOn (fun t =>
      intervalExtension hU zIn (g t) 0 * f (g t) +
        intervalExtension hV (intervalExtension hU C (g t)) (v t)) s := by
    apply ContinuousOn.add
    · exact ((continuous_apply 0).comp_continuousOn
        ((intervalExtension hU zIn).continuous.comp_continuousOn hg)).mul hfc
    · simp only [intervalExtension_apply]
      have hgp : ContinuousOn (fun t => projIcc 0 U hU (g t)) s :=
        continuous_projIcc.comp_continuousOn hg
      have hvp : ContinuousOn (fun t => projIcc 0 V hV (v t)) s :=
        continuous_projIcc.comp_continuousOn hv
      exact C.uncurry.continuous.comp_continuousOn (hgp.prodMk hvp)
  apply hcont.congr
  intro t ht
  have hd := hx.scalar_hasDerivWithinAt_of_continuous hzin hinu hc hif (hgu t ht)
    (projIcc 0 V hV (v t))
  have hdd := hd.derivWithin ((uniqueDiffOn_Icc ((hgu t ht).1.trans_le (hgu t ht).2))
    _ ⟨(hgu t ht).1.le, (hgu t ht).2⟩)
  simp only [intervalExtension_apply, projIcc_of_mem hU
    (show g t ∈ Icc 0 U from ⟨(hgu t ht).1.le, (hgu t ht).2⟩)]
  simp only [intervalExtension_apply] at hdd
  rw [hdd, mul_div_cancel₀ _ (hx.choose _ _)]

theorem IsWaveIntegral.scalar_curve_energy
    {U V e Λ k l w A B : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
    (hlw : l ≤ w) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc l w))
    (hgu : ∀ t ∈ Icc l w, g t ∈ Ioc 0 U) :
    let C := scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hx.choose) x.2.1
    (∫ t in l..w, (g t * Real.exp (k * t) * zIn (projIcc 0 U hU (g t)) 0 * f (g t)) ^ 2) ≤ A →
    (∫ t in l..w, (g t * Real.exp (k * t) *
      intervalExtension hV (intervalExtension hU C (g t)) t) ^ 2) ≤ B →
    (∫ t in l..w, (g t * Real.exp (k * t) *
      (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
        derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
          (Icc 0 U) (g t))) ^ 2) ≤ 2 * A + 2 * B := by
  intro C hin hcorr
  let I := fun t => g t * Real.exp (k * t) * zIn (projIcc 0 U hU (g t)) 0 * f (g t)
  let Q := fun t => g t * Real.exp (k * t) * intervalExtension hV (intervalExtension hU C (g t)) t
  let Z := fun t => g t * Real.exp (k * t) *
    (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
      derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1) (Icc 0 U) (g t))
  have hIc : ContinuousOn I (Icc l w) := by
    have hfc := hc.comp hg (fun t ht => (hgu t ht).1)
    have hp : ContinuousOn (fun t => g t * Real.exp (k * t) * intervalExtension hU zIn (g t) 0)
        (Icc l w) := by fun_prop
    exact hp.mul hfc
  have hQc : ContinuousOn Q (Icc l w) := by dsimp only [Q]; fun_prop
  have he (t : ℝ) (ht : t ∈ Icc l w) : Z t = I t + Q t := by
    have hd := hx.scalar_hasDerivWithinAt_of_continuous hzin hinu hc hif (hgu t ht)
      (projIcc 0 V hV t)
    have hdd := hd.derivWithin ((uniqueDiffOn_Icc ((hgu t ht).1.trans_le (hgu t ht).2))
      _ ⟨(hgu t ht).1.le, (hgu t ht).2⟩)
    dsimp only [Z, I, Q, intervalExtension_apply]
    change g t * Real.exp (k * t) * (x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 *
      derivWithin (fun u => intervalExtension hU x.1 u (projIcc 0 V hV t) 1) (Icc 0 U) (g t)) = _
    rw [hdd, projIcc_of_mem hU (show g t ∈ Icc 0 U from ⟨(hgu t ht).1.le, (hgu t ht).2⟩)]
    dsimp only [C]
    field_simp [hx.choose ⟨g t, (hgu t ht).1.le, (hgu t ht).2⟩ (projIcc 0 V hV t)]
  have hZ : (∫ t in l..w, Z t ^ 2) = ∫ t in l..w, (I t + Q t) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlw] at ht
    dsimp only
    rw [he t ht]
  change (∫ t in l..w, Z t ^ 2) ≤ _
  rw [hZ]
  have hIi : IntervalIntegrable (fun t => I t ^ 2) volume l w :=
    (hIc.pow 2).intervalIntegrable_of_Icc hlw
  have hQi : IntervalIntegrable (fun t => Q t ^ 2) volume l w :=
    (hQc.pow 2).intervalIntegrable_of_Icc hlw
  have hs := intervalIntegral.integral_mono_on (μ := volume) hlw
    (((hIc.add hQc).pow 2).intervalIntegrable_of_Icc hlw)
    ((hIi.const_mul 2).add (hQi.const_mul 2))
    (fun t _ => by
      change (I t + Q t) ^ 2 ≤ 2 * I t ^ 2 + 2 * Q t ^ 2
      nlinarith only [sq_nonneg (I t - Q t)])
  rw [intervalIntegral.integral_add (hIi.const_mul 2) (hQi.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hs
  exact hs.trans (add_le_add (mul_le_mul_of_nonneg_left hin (by norm_num))
    (mul_le_mul_of_nonneg_left hcorr (by norm_num)))

theorem IsWaveIntegral.exists_curve_radiation_source
    {U V e Λ k : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
    (g : C(Icc 0 V, Icc 0 U)) (hg : ∀ v, 0 < (g v : ℝ)) :
    let Z := fun v : Icc 0 V => (g v : ℝ) * Real.exp (k * v) *
      (x.1 (g v) v 0 * derivWithin (fun u => intervalExtension hU x.1 u v 1) (Icc 0 U) (g v))
    ∃ A : C(Icc 0 V, ℝ), (∀ v, 0 ≤ A v) ∧ (∀ v, A v = |Z v|) ∧
      (∀ l w : ℝ, (∫ t in l..w, (A (projIcc 0 V hV t)) ^ 2) =
        ∫ t in l..w, (Z (projIcc 0 V hV t)) ^ 2) ∧
      ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, (g v : ℝ) = t →
        A v = t * Real.exp (k * v) *
          |x.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1| := by
  let ν := radialNuField hV e Λ zIn x.1 hx.choose
  let C := scalarTransportCorrection hV ν x.2.1
  have hfc : Continuous (fun v : Icc 0 V => f (g v)) :=
    hc.comp_continuous (by fun_prop) (fun v => hg v)
  let P : C(Icc 0 V, ℝ) := ⟨fun v => zIn (g v) 0 * f (g v) + C (g v) v,
    ((by fun_prop : Continuous (fun v : Icc 0 V => zIn (g v) 0)).mul hfc).add
      (C.uncurry.continuous.comp (g.continuous.prodMk continuous_id))⟩
  let Zc : C(Icc 0 V, ℝ) := ⟨fun v => (g v : ℝ) * Real.exp (k * v) * P v, by fun_prop⟩
  let A : C(Icc 0 V, ℝ) := ⟨fun v => |Zc v|, by fun_prop⟩
  dsimp only
  have hZ (v : Icc 0 V) : Zc v = (g v : ℝ) * Real.exp (k * v) *
      (x.1 (g v) v 0 * derivWithin (fun u => intervalExtension hU x.1 u v 1) (Icc 0 U) (g v)) := by
    have hd := hx.scalar_hasDerivWithinAt_of_continuous hzin hinu hc hif
      (show (g v : ℝ) ∈ Ioc 0 U from ⟨hg v, (g v).property.2⟩) v
    have hdd := hd.derivWithin ((uniqueDiffOn_Icc ((hg v).trans_le (g v).property.2)) _ (g v).property)
    rw [hdd]
    change (g v : ℝ) * Real.exp (k * v) * P v =
      (g v : ℝ) * Real.exp (k * v) * (x.1 (g v) v 0 * (P v / x.1 (g v) v 0))
    rw [mul_div_cancel₀ _ (hx.choose (g v) v)]
  refine ⟨A, fun v => abs_nonneg _, fun v => by
    change |Zc v| = _
    rw [hZ], ?_, ?_⟩
  · intro l w
    apply intervalIntegral.integral_congr
    intro t _
    change |Zc (projIcc 0 V hV t)| ^ 2 = _
    rw [hZ, sq_abs]
  · filter_upwards [hx.zeta_transport hx.choose hinu, hif, ae_restrict_mem measurableSet_Icc] with t hz hf ht
    intro v hgt
    have hgp : g v = projIcc 0 U hU t := by
      apply Subtype.ext
      rw [projIcc_of_mem hU ht]
      exact hgt
    have hP : P v = x.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1 := by
      have hh := (hz v).symm
      rw [hf] at hh
      simpa only [P, ContinuousMap.coe_mk, hgp, projIcc_of_mem hU ht, C, ν] using hh
    change |(g v : ℝ) * Real.exp (k * v) * P v| = _
    rw [hgt, hP, abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_pos (Real.exp_pos _)]

theorem IsWaveIntegral.exists_matching_radiation_source
    {U V e Λ k n : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
    (hn : 0 < n) (g : C(Icc 0 V, Icc 0 U)) (hg : ∀ v, 0 < (g v : ℝ)) :
    let ν := radialNuField hV e Λ zIn x.1 hx.choose
    let Z := fun v : Icc 0 V => (g v : ℝ) * Real.exp (k * v) *
      (x.1 (g v) v 0 * derivWithin (fun u => intervalExtension hU x.1 u v 1) (Icc 0 U) (g v))
    ∃ A : C(Icc 0 V, ℝ), (∀ v, 0 ≤ A v) ∧ (∀ v, A v = |Z v| / n) ∧
      (∀ l w : ℝ, (∫ t in l..w, (A (projIcc 0 V hV t)) ^ 2) =
        (1 / n ^ 2) * ∫ t in l..w, (Z (projIcc 0 V hV t)) ^ 2) ∧
      ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, (g v : ℝ) = t →
        n ≤ t * (-ν (projIcc 0 U hU t) v) →
        Real.exp (k * v) * |x.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1| ≤
          (-ν (projIcc 0 U hU t) v) * A v := by
  obtain ⟨S, hS0, hS, hSE, hsource⟩ := hx.exists_curve_radiation_source hzin hinu hc hif g hg
  let A : C(Icc 0 V, ℝ) := ⟨fun v => S v / n, by fun_prop⟩
  dsimp only
  refine ⟨A, fun v => div_nonneg (hS0 v) hn.le,
    fun v => by change S v / n = _; rw [hS], ?_, ?_⟩
  · intro l w
    calc
      _ = (1 / n ^ 2) * ∫ t in l..w, (S (projIcc 0 V hV t)) ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        change (S (projIcc 0 V hV t) / n) ^ 2 = _
        rw [div_pow]; ring
      _ = _ := by rw [hSE]
  · filter_upwards [hsource] with t ht
    intro v hgt hscale
    change _ ≤ _ * (S v / n)
    rw [ht v hgt, ← mul_div_assoc]
    apply (le_div_iff₀ hn).2
    have hh := mul_le_mul_of_nonneg_right hscale
      (mul_nonneg (Real.exp_pos (k * v)).le (abs_nonneg (x.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1)))
    nlinarith only [hh]

end CauchyHorizon
