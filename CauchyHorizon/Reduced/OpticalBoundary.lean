import CauchyHorizon.Reduced.MassCoefficient

/-! Radiation energy gives the continuous horizon limit of the actual optical flux. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def opticalField {U V : ℝ} (x : WaveState U V) :
    C(Icc 0 U, C(Icc 0 V, ℝ)) :=
  (⟨fun q : Icc 0 U × Icc 0 V => -x.2.1 q.1 q.2 0 / Real.exp (x.1 q.1 q.2 2),
    by fun_prop (disch := intro q; exact Real.exp_ne_zero _)⟩ : C(Icc 0 U × Icc 0 V, ℝ)).curry

noncomputable def opticalRow {U ε : ℝ} (hε : 0 ≤ ε)
    (X : (V : Ici (0 : ℝ)) → WaveState U V) : ℝ → C(Icc ε U, ℝ) :=
  scalarBoundaryRow hε (fun V => opticalField (X V))

theorem opticalRow_apply {U ε : ℝ} (hε : 0 ≤ ε)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (V : Ici (0 : ℝ)) {t : ℝ} (ht : 0 ≤ t) (htV : t ≤ V) (u : Icc ε U) :
    opticalRow hε X t u =
      -(X V).2.1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htV⟩ 0 /
        Real.exp ((X V).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htV⟩ 2) := by
  apply scalarBoundaryRow_apply hε (fun V => opticalField (X V)) _ V ht htV u
  intro S T hST w v
  have hz := congrArg (fun x : WaveState U S => x.1 w v) (hX S T hST)
  have hw := congrArg (fun x : WaveState U S => x.2.1 w v) (hX S T hST)
  change (X T).1 ⟨0 + (w : ℝ), by simpa using w.property.1, by simpa using w.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X S).1 w v at hz
  change (X T).2.1 ⟨0 + (w : ℝ), by simpa using w.property.1, by simpa using w.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X S).2.1 w v at hw
  simp only [zero_add] at hz hw
  change -(X S).2.1 w v 0 / Real.exp ((X S).1 w v 2) = _
  rw [← hz, ← hw]
  rfl

set_option maxHeartbeats 800000 in
theorem exists_optical_boundary_limit {U ε k ρ A T₀ : ℝ} (hε : 0 ≤ ε)
    (hρ : 0 < ρ) (hA : 0 < A) (hT₀ : 0 ≤ T₀)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hr : ∀ (V : Ici (0 : ℝ)) u v, ρ ≤ (X V).1 u v 0)
    (hamp : ∀ t, T₀ ≤ t → ∀ u, A ≤ waveAmplitude (renormalizedWaveRow hε k X t) u)
    (henergy : MemLp (radiationRow k X) 2 (volume.restrict (Ici 0)))
    (hflux : ∀ (V : Ici (0 : ℝ)) (u : Icc 0 U) (v : Icc 0 (V : ℝ)),
      (X V).2.1 u v 0 * Real.exp (-(X V).1 u v 2) =
        (X V).2.1 u ⟨0, le_rfl, V.property⟩ 0 * Real.exp (-(X V).1 u ⟨0, le_rfl, V.property⟩ 2) -
          ∫ t in (0 : ℝ)..v, intervalExtension V.property ((X V).1 u) t 0 *
            Real.exp (-intervalExtension V.property ((X V).1 u) t 2) *
              (intervalExtension V.property ((X V).2.1 u) t 1) ^ 2) :
    ∃ Dh : C(Icc ε U, ℝ), Tendsto (opticalRow hε X) atTop (𝓝 Dh) ∧
      (∀ t, T₀ ≤ t → ‖opticalRow hε X t - Dh‖ ≤
        (1 / (ρ * A)) * ∫ v in Ioi t, ‖radiationRow k X v‖ ^ 2) ∧
      ∀ t, 0 ≤ t → ∀ u, opticalRow hε X t u ≤ Dh u := by
  let J (u : Icc ε U) : Icc 0 U := ⟨u, hε.trans u.property.1, u.property.2⟩
  let F (V : Ici (0 : ℝ)) (u : Icc ε U) (t : ℝ) :=
    intervalExtension V.property ((X V).1 (J u)) t 0 *
      Real.exp (-intervalExtension V.property ((X V).1 (J u)) t 2) *
        (intervalExtension V.property ((X V).2.1 (J u)) t 1) ^ 2
  let R := fun t => ‖radiationRow k X t‖ ^ 2
  have hFc (V : Ici (0 : ℝ)) (u : Icc ε U) : Continuous (F V u) := by fun_prop
  have hRc : Continuous R := (continuous_radiationRow X hX).norm.pow 2
  have hRi : IntegrableOn R (Ici 0) := (memLp_two_iff_integrable_sq_norm henergy.1).1 henergy
  have hFpos (V : Ici (0 : ℝ)) (u : Icc ε U) (t : ℝ) : 0 ≤ F V u t :=
    mul_nonneg (mul_nonneg (hρ.le.trans (hr V (J u) _)) (Real.exp_pos _).le) (sq_nonneg _)
  have hinc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : Icc ε U) :
      opticalRow hε X b u - opticalRow hε X a u =
        ∫ t in a..b, F ⟨b, ha.trans hab⟩ u t := by
    let V : Ici (0 : ℝ) := ⟨b, ha.trans hab⟩
    rw [opticalRow_apply hε X hX V V.property le_rfl u, opticalRow_apply hε X hX V ha hab u]
    have hca := hflux V (J u) ⟨a, ha, hab⟩
    have hcb := hflux V (J u) ⟨b, V.property, le_rfl⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hFc V u).intervalIntegrable (0 : ℝ) a) ((hFc V u).intervalIntegrable a b)
    dsimp only [F] at hsplit ⊢
    simp only [neg_div, Real.exp_neg, ← div_eq_mul_inv] at hca hcb hsplit ⊢
    change -((X V).2.1 (J u) ⟨b, V.property, le_rfl⟩ 0 /
        Real.exp ((X V).1 (J u) ⟨b, V.property, le_rfl⟩ 2)) -
      -((X V).2.1 (J u) ⟨a, ha, hab⟩ 0 /
        Real.exp ((X V).1 (J u) ⟨a, ha, hab⟩ 2)) = _
    linarith only [hca, hcb, hsplit]
  have hmono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : Icc ε U) :
      opticalRow hε X a u ≤ opticalRow hε X b u := by
    apply sub_nonneg.1
    rw [hinc ha hab u]
    exact intervalIntegral.integral_nonneg hab (fun t _ => hFpos _ u t)
  have hpoint (V : Ici (0 : ℝ)) (u : Icc ε U) {t : ℝ}
      (ht : T₀ ≤ t) (htV : t ≤ V) : ‖F V u t‖ ≤ (1 / (ρ * A)) * R t := by
    have ht0 := hT₀.trans ht
    let v : Icc 0 (V : ℝ) := ⟨t, ht0, htV⟩
    have hrad : 0 < (X V).1 (J u) v 0 := hρ.trans_le (hr V (J u) v)
    have ha : A ≤ Real.exp ((X V).1 (J u) v 2 + 2 * k * t) := by
      have hh := hamp t ht u
      change A ≤ Real.exp (renormalizedWaveRow hε k X t u 2) at hh
      simpa only [renormalizedWaveRow_apply hε X hX V ht0 htV u 2, ite_true] using hh
    have hden := mul_le_mul (hr V (J u) v) ha hA.le hrad.le
    have he : F V u t = (radiationRow k X t (J u)) ^ 2 /
        ((X V).1 (J u) v 0 * Real.exp ((X V).1 (J u) v 2 + 2 * k * t)) := by
      change (X V).1 (J u) (projIcc 0 (V : ℝ) V.property t) 0 *
        Real.exp (-(X V).1 (J u) (projIcc 0 (V : ℝ) V.property t) 2) *
        ((X V).2.1 (J u) (projIcc 0 (V : ℝ) V.property t) 1) ^ 2 = _
      rw [projIcc_of_mem V.property (show t ∈ Icc 0 (V : ℝ) from ⟨ht0, htV⟩)]
      rw [radiationRow_eq X hX V htV]
      simp only [spatialRadiationRows, ContinuousMap.curry_apply,
        ContinuousMap.coe_mk, zero_mul, sub_zero, projIcc_of_mem V.property (show t ∈ Icc 0 (V : ℝ) from ⟨ht0, htV⟩)]
      change _ = (Real.exp (k * t) * ((X V).1 (J u) v 0 * (X V).2.1 (J u) v 1)) ^ 2 / _
      rw [Real.exp_add, show 2 * k * t = k * t + k * t by ring, Real.exp_add, Real.exp_neg]
      field_simp [hrad.ne']
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (hFpos V u t), he]
    have hsq : (radiationRow k X t (J u)) ^ 2 ≤ R t := by
      simpa only [Real.norm_eq_abs, sq_abs, R] using
        pow_le_pow_left₀ (norm_nonneg _) ((radiationRow k X t).norm_coe_le_norm (J u)) 2
    calc
      _ ≤ R t / (ρ * A) := div_le_div₀ (sq_nonneg _) hsq (mul_pos hρ hA) hden
      _ = _ := by ring
  have htail (a : ℝ) (ha : T₀ ≤ a) (b : ℝ) (hab : a ≤ b) :
      dist (opticalRow hε X a) (opticalRow hε X b) ≤
        (1 / (ρ * A)) * ∫ t in Ioi a, R t := by
    have ha0 := hT₀.trans ha
    have hc : 0 ≤ (1 / (ρ * A)) := by positivity
    rw [dist_comm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (mul_nonneg hc (integral_nonneg (fun _ => sq_nonneg _)))).2
    intro u
    rw [ContinuousMap.sub_apply, hinc ha0 hab u]
    calc
      _ ≤ ∫ t in a..b, (1 / (ρ * A)) * R t :=
        intervalIntegral.norm_integral_le_of_norm_le hab
          (Eventually.of_forall (fun t ht => hpoint ⟨b, ha0.trans hab⟩ u (ha.trans ht.1.le) ht.2))
          ((hRc.const_mul _).intervalIntegrable a b)
      _ = (1 / (ρ * A)) * ∫ t in a..b, R t := intervalIntegral.integral_const_mul _ _
      _ ≤ (1 / (ρ * A)) * ∫ t in Ioi a, R t := by
        apply mul_le_mul_of_nonneg_left _ hc
        rw [intervalIntegral.integral_of_le hab]
        exact setIntegral_mono_set (hRi.mono_set (fun _ ht => ha0.trans ht.le))
          (Eventually.of_forall (fun _ => sq_nonneg _)) (Eventually.of_forall (fun _ ht => ht.1))
  have hzero : Tendsto (fun a => (1 / (ρ * A)) * ∫ t in Ioi a, R t) atTop (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_integral_Ioi_zero (f := R) (μ := volume) tendsto_id).const_mul (1 / (ρ * A))
  obtain ⟨Dh, hDh, hbound⟩ := exists_limit_of_tail_bound hzero htail
  refine ⟨Dh, hDh, (fun t ht => by simpa only [dist_eq_norm] using hbound t ht), ?_⟩
  intro t ht u
  have he := (continuous_eval_const u).tendsto Dh |>.comp hDh
  exact ge_of_tendsto he ((eventually_ge_atTop t).mono (fun b hb => hmono ht hb u))

noncomputable def anchoredAmplitude {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (u₀ : K) : C(C(K, WaveVector), C(K, ℝ)) :=
  ⟨fun Z => Real.exp (-Z u₀ 2) • waveAmplitude Z, by
    have hc : Continuous (fun Z : C(K, WaveVector) => Z u₀ 2) :=
      (continuous_apply (2 : Fin 3)).comp (continuous_eval_const u₀)
    exact (Real.continuous_exp.comp hc.neg).smul waveAmplitude.continuous⟩

noncomputable def lapseNormalizedRadialRow {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (k : ℝ) (X : (V : Ici (0 : ℝ)) → WaveState U V) (t : ℝ) : C(Icc ε U, ℝ) :=
  -(anchoredAmplitude ⟨U, hεU, le_rfl⟩ (renormalizedWaveRow hε k X t)) * opticalRow hε X t

set_option maxHeartbeats 800000 in
theorem lapse_normalized_radial_limit {U ε k : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    {Z : C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, ℝ)}
    (hZ : Tendsto (renormalizedWaveRow hε k X) atTop (𝓝 Z))
    (hD : Tendsto (opticalRow hε X) atTop (𝓝 Dh)) :
    (∀ (V : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htV : t ≤ V) (u : Icc ε U),
      lapseNormalizedRadialRow hε hεU k X t u =
        (X V).2.1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htV⟩ 0 /
          Real.exp ((X V).1 ⟨U, hε.trans hεU, le_rfl⟩ ⟨t, ht, htV⟩ 2)) ∧
      Tendsto (lapseNormalizedRadialRow hε hεU k X) atTop
        (𝓝 (-(anchoredAmplitude ⟨U, hεU, le_rfl⟩ Z) * Dh)) := by
  constructor
  · intro V t ht htV u
    change -(Real.exp (-renormalizedWaveRow hε k X t ⟨U, hεU, le_rfl⟩ 2) *
      Real.exp (renormalizedWaveRow hε k X t u 2)) * opticalRow hε X t u = _
    rw [renormalizedWaveRow_apply hε X hX V ht htV ⟨U, hεU, le_rfl⟩ 2,
      renormalizedWaveRow_apply hε X hX V ht htV u 2, opticalRow_apply hε X hX V ht htV u]
    simp only [ite_true, Real.exp_neg, Real.exp_add]
    field_simp
  · let u₀ : Icc ε U := ⟨U, hεU, le_rfl⟩
    have hc : Continuous (anchoredAmplitude u₀) := (anchoredAmplitude u₀).continuous
    have hh := (hc.tendsto Z).comp hZ
    exact hh.neg.mul hD

end CauchyHorizon
