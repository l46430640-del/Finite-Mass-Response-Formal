import CauchyHorizon.Reduced.OuterScalar

/-! The outer radiation estimate retains its causal exponential time kernel. -/

open MeasureTheory Set

namespace CauchyHorizon

noncomputable def causalExpIntegral {V : ℝ} (hV : 0 ≤ V) (d : ℝ)
    (M : C(Icc 0 V, ℝ)) (v : Icc 0 V) : ℝ :=
  ∫ t in (0 : ℝ)..v, Real.exp (-d * ((v : ℝ) - t)) * M (projIcc 0 V hV t)

theorem causalExpIntegral_one {V d : ℝ} (hV : 0 ≤ V) (hd : d ≠ 0) (v : Icc 0 V) :
    causalExpIntegral hV d (ContinuousMap.const _ 1) v = (1 - Real.exp (-d * v)) / d := by
  have he (t : ℝ) : Real.exp (-d * ((v : ℝ) - t)) = Real.exp (-d * v) * Real.exp (d * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold causalExpIntegral
  simp only [ContinuousMap.const_apply, mul_one, he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hd,
    integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
  have hcancel : Real.exp (-d * v) * Real.exp (d * v) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  field_simp
  simp only [neg_mul] at hcancel
  nlinarith only [hcancel]

theorem IsWaveIntegral.outer_radiation_majorant_on {U V e Λ a k ρ R N L : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (B : Icc 0 V → ℝ) (hB : Antitone B)
    (hlo : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v → ρ ≤ x.1 u v 0)
    (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v → |x.2.1 u v 0| ≤ L)
    (Γ : C(Icc 0 U, C(Icc 0 V, ℝ))) (hΓ : ∀ u, Monotone (Γ u))
    (M : C(Icc 0 V, ℝ)) (hM0 : ∀ v, 0 ≤ M v)
    (hM : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ Γ u v * M v) :
    (∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
      Real.exp (k * v) *
          |scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 u v| ≤
        (N / ρ) * Real.exp (a * v) * Γ u v * causalExpIntegral hV (a - k) M v) ∧
      ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ B v →
        Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤
          Real.exp (k * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
          (L * R / ρ) * Real.exp (k * v) * (∫ t in (0 : ℝ)..u, |uIn t 1|) +
          (L * N / ρ ^ 2) * Real.exp (a * v) * causalExpIntegral hV (a - k) M v *
            (∫ t in (0 : ℝ)..u, Γ (projIcc 0 U hU t) v) := by
  let ν := radialNuField hV e Λ zIn x.1 hr
  let J := causalExpIntegral hV (a - k) M
  have hφ (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ B v) :
      |x.2.1 u v 1| ≤ Real.exp (-(k * v)) * (Γ u v * M v / ρ) := by
    have hm := hM u v hu
    rw [abs_mul, abs_of_pos (hρ.trans_le (hlo u v hu))] at hm
    have hh : Real.exp (k * v) * |x.2.1 u v 1| ≤ Γ u v * M v / ρ := by
      apply (le_div_iff₀ hρ).2
      nlinarith only [hm, mul_le_mul_of_nonneg_right (hlo u v hu)
        (mul_nonneg (Real.exp_pos (k * v)).le (abs_nonneg (x.2.1 u v 1)))]
    have hp := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-(k * v))).le
    simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] using hp
  have hcor (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ B v) :
      Real.exp (k * v) * |scalarTransportCorrection hV ν x.2.1 u v| ≤
        (N / ρ) * Real.exp (a * v) * Γ u v * J v := by
    let F := fun t => -ν u (projIcc 0 V hV t) * x.2.1 u (projIcc 0 V hV t) 1
    let G := fun t => Real.exp (-(a - k) * ((v : ℝ) - t)) * M (projIcc 0 V hV t)
    have hGc : Continuous G := by fun_prop
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) v.property.1
      (f := fun t => Real.exp (k * v) * F t)
      (g := fun t => ((N / ρ) * Real.exp (a * v) * Γ u v) * G t)
      (Filter.Eventually.of_forall (fun t ht => ?_))
      ((hGc.const_mul _).intervalIntegrable (0 : ℝ) v)
    · rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _), intervalIntegral.integral_const_mul] at hb
      exact hb
    · have htV : t ∈ Icc 0 V := ⟨ht.1.le, ht.2.trans v.property.2⟩
      have hut : (u : ℝ) ≤ B ⟨t, htV⟩ := hu.trans (hB ht.2)
      have hφ' : |x.2.1 u ⟨t, htV⟩ 1| ≤
          Real.exp (-(k * t)) * (Γ u v * M ⟨t, htV⟩ / ρ) :=
        (hφ u ⟨t, htV⟩ hut).trans (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hΓ u ht.2) (hM0 ⟨t, htV⟩)) hρ.le)
          (Real.exp_pos _).le)
      simp only [F, G, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
        projIcc_of_mem hV htV]
      calc
        _ ≤ Real.exp (k * v) *
            ((N * Real.exp (a * t)) * (Real.exp (-(k * t)) * (Γ u v * M ⟨t, htV⟩ / ρ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hν u ⟨t, htV⟩ hut) hφ' (abs_nonneg _)
              (mul_nonneg hN (Real.exp_pos _).le)) (Real.exp_pos _).le
        _ = _ := by
          have he : Real.exp (k * v) * Real.exp (a * t) * Real.exp (-(k * t)) =
              Real.exp (a * v) * Real.exp (-(a - k) * ((v : ℝ) - t)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
          calc
            _ = (N / ρ) * Γ u v * M ⟨t, htV⟩ *
                (Real.exp (k * v) * Real.exp (a * t) * Real.exp (-(k * t))) := by ring
            _ = _ := by rw [he]; ring
  refine ⟨hcor, ?_⟩
  intro u v hu
  let P := fun t => (N / ρ) * Real.exp (a * v) * J v * Γ (projIcc 0 U hU t) v
  have hBc : Continuous P := by fun_prop
  have htrans : ∀ᵐ t ∂volume.restrict (Icc 0 U),
      (projIcc 0 U hU t : ℝ) ≤ B v →
      Real.exp (k * v) * |x.2.2 t v 1| ≤
        (R / ρ) * Real.exp (k * v) * |uIn t 1| + P t / ρ := by
    filter_upwards [hx.zeta_transport hr hinu] with t ht
    intro htB
    let q := projIcc 0 U hU t
    have hh := (abs_add_le (zIn q 0 * uIn t 1)
      (scalarTransportCorrection hV ν x.2.1 q v))
    rw [← ht v, abs_mul, abs_of_pos (hρ.trans_le (hlo q v htB))] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (k * v)).le
    have hin' := mul_le_mul_of_nonneg_right (hin q)
      (mul_nonneg (Real.exp_pos (k * v)).le (abs_nonneg (uIn t 1)))
    rw [abs_mul] at hh'
    have hlo' := mul_le_mul_of_nonneg_right (hlo q v htB)
      (mul_nonneg (Real.exp_pos (k * v)).le (abs_nonneg (x.2.2 t v 1)))
    have hb : Real.exp (k * v) * |x.2.2 t v 1| ≤
        (R * Real.exp (k * v) * |uIn t 1| + P t) / ρ := by
      apply (le_div_iff₀ hρ).2
      dsimp only [P]
      nlinarith only [hh', hin', hlo', hcor q v htB]
    exact hb.trans_eq (by ring)
  have hfi : IntervalIntegrable (fun t => uIn t 1) volume 0 U := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hU).2
    exact (ContinuousLinearMap.proj (1 : Fin 3) : WaveVector →L[ℝ] ℝ).integrable_comp
      ((Lp.memLp uIn).integrable (by norm_num))
  have hfu := hfi.abs.mono_set (show uIcc (0 : ℝ) u ⊆ uIcc (0 : ℝ) U by
    rw [uIcc_of_le u.property.1, uIcc_of_le hU]
    exact Icc_subset_Icc le_rfl u.property.2)
  have hBi : IntervalIntegrable (fun t => P t / ρ) volume 0 u :=
    ((hBc.intervalIntegrable _ _).div_const ρ)
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) u.property.1
    (f := fun t => Real.exp (k * v) * (-x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1))
    (g := fun t => L * ((R / ρ) * Real.exp (k * v) * |uIn t 1| + P t / ρ))
    (by
      apply (ae_restrict_iff' measurableSet_Ioc).1
      have hs : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
      filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) htrans,
        ae_restrict_mem measurableSet_Ioc] with t ht htu
      have htB : (projIcc 0 U hU t : ℝ) ≤ B v := by
        rw [projIcc_of_mem hU (hs htu)]
        exact htu.2.trans hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_neg]
      have hh := mul_le_mul (hlam (projIcc 0 U hU t) v htB) (ht htB)
        (mul_nonneg (Real.exp_pos (k * v)).le (abs_nonneg (x.2.2 t v 1))) hL
      calc
        _ = |x.2.1 (projIcc 0 U hU t) v 0| * (Real.exp (k * v) * |x.2.2 t v 1|) := by ring
        _ ≤ _ := hh)
    (((hfu.const_mul ((R / ρ) * Real.exp (k * v))).add hBi).const_mul L)
  rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hfu.const_mul _) hBi,
    intervalIntegral.integral_const_mul] at hb
  simp only [P, intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at hb
  have hh := mul_le_mul_of_nonneg_left
    (abs_add_le (x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1)
      (∫ t in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1))
    (Real.exp_pos (k * v)).le
  rw [← hx.theta_integral hzin u v] at hh
  dsimp only [J] at hb
  ring_nf at hh hb ⊢
  nlinarith only [hh, hb]

theorem IsWaveIntegral.outer_radiation_majorant {U V e Λ a k ρ R N L : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (Γ : C(Icc 0 U, C(Icc 0 V, ℝ))) (hΓ : ∀ u, Monotone (Γ u))
    (M : C(Icc 0 V, ℝ)) (hM0 : ∀ v, 0 ≤ M v)
    (hM : ∀ (u : Icc 0 U) (v : Icc 0 V),
      Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ Γ u v * M v) :
    (∀ (u : Icc 0 U) (v : Icc 0 V),
      Real.exp (k * v) *
          |scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 u v| ≤
        (N / ρ) * Real.exp (a * v) * Γ u v * causalExpIntegral hV (a - k) M v) ∧
      ∀ (u : Icc 0 U) (v : Icc 0 V),
        Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤
          Real.exp (k * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
          (L * R / ρ) * Real.exp (k * v) * (∫ t in (0 : ℝ)..u, |uIn t 1|) +
          (L * N / ρ ^ 2) * Real.exp (a * v) * causalExpIntegral hV (a - k) M v *
            (∫ t in (0 : ℝ)..u, Γ (projIcc 0 U hU t) v) := by
  have hh := hx.outer_radiation_majorant_on hr hzin hinu hρ hN hL (fun _ => U) antitone_const
    (fun u v _ => hlo u v) hin (fun u v _ => hν u v) (fun u v _ => hlam u v)
    Γ hΓ M hM0 (fun u v _ => hM u v)
  exact ⟨fun u v => hh.1 u v u.property.2, fun u v => hh.2 u v u.property.2⟩

theorem IsWaveIntegral.outer_radiation_kernel {U V e Λ a k ρ R N L δ : ℝ}
    {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (ha : 0 ≤ a) (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L) (hwidth : U * Real.exp (a * V) ≤ δ)
    (M : C(Icc 0 V, ℝ))
    (hM : ∀ (u : Icc 0 U) (v : Icc 0 V), Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v) :
    (∀ (u : Icc 0 U) (v : Icc 0 V),
      (u : ℝ) * Real.exp (k * v) *
          |scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hr) x.2.1 u v| ≤
        (N * δ / ρ) * causalExpIntegral hV (a - k) M v) ∧
      ∀ (u : Icc 0 U) (v : Icc 0 V),
        Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤
          Real.exp (k * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| +
          (L * R / ρ) * Real.exp (k * v) * (∫ t in (0 : ℝ)..u, |uIn t 1|) +
          (L * N * δ / ρ ^ 2) * causalExpIntegral hV (a - k) M v := by
  have hM0 (v : Icc 0 V) : 0 ≤ M v :=
    (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)).trans (hM ⟨0, le_rfl, hU⟩ v)
  have hJ0 (v : Icc 0 V) : 0 ≤ causalExpIntegral hV (a - k) M v :=
    intervalIntegral.integral_nonneg v.property.1
      (fun t _ => mul_nonneg (Real.exp_pos _).le (hM0 _))
  obtain ⟨hcor, hlong⟩ := hx.outer_radiation_majorant hr hzin hinu hρ hN hL hlo hin hν hlam
    (ContinuousMap.const _ (ContinuousMap.const _ 1)) (fun _ => monotone_const) M hM0
    (fun u v => by simpa using hM u v)
  have hscale (u : Icc 0 U) (v : Icc 0 V) : (u : ℝ) * Real.exp (a * v) ≤ δ :=
    (mul_le_mul u.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 ha))
      (Real.exp_pos _).le hU).trans hwidth
  simp only [ContinuousMap.const_apply, mul_one, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hcor hlong
  constructor
  · intro u v
    have hh := mul_le_mul_of_nonneg_left (hcor u v) u.property.1
    have hw := mul_le_mul_of_nonneg_right (hscale u v)
      (mul_nonneg (div_nonneg hN hρ.le) (hJ0 v))
    ring_nf at hh hw ⊢
    nlinarith only [hh, hw]
  · intro u v
    have hw := mul_le_mul_of_nonneg_right (hscale u v)
      (mul_nonneg (div_nonneg (mul_nonneg hL hN) (sq_nonneg ρ)) (hJ0 v))
    have hh := hlong u v
    ring_nf at hw hh ⊢
    nlinarith only [hw, hh]

end CauchyHorizon
