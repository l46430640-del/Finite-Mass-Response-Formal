import CauchyHorizon.Characteristic.MassDensityComparison
import CauchyHorizon.Reduced.MassRows

/-! One L1 density error controls all mass endpoints, including the horizon. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

def MassResponseLimit {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (C H M : ℕ → ℝ → C(K, ℝ)) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧ ∃ Q : C(K, ℝ), Tendsto (C 0) atTop (𝓝 Q) ∧
    ∃ Z : ℕ → C(K, ℝ), (∀ n, Tendsto (M n) atTop (𝓝 (Z n))) ∧
      ∀ d > (0 : ℝ), ∀ᶠ n in atTop,
        (∀ t, T ≤ t → ‖M n t - M 0 t - ∫ s in T..t, Q * H n s ^ 2‖ < d) ∧
        ‖Z n - Z 0 - ∫ s in Ici T, Q * H n s ^ 2‖ < d

def RadiationMassResponse {U ε : ℝ} (hε : 0 ≤ ε) (k c e Λ : ℝ)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (n : ℕ) → (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)))
    (hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0) (P : ℕ → ℝ → ℝ) : Prop :=
  MassResponseLimit (fun n => massCoefficientRow hε k (X n) (N n))
    (fun n t => ContinuousMap.const _ (c * P n t)) (fun n => massRow hε e Λ (X n) (N n) (hr n))

theorem mass_cumulative_limit {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {C R H M : ℕ → ℝ → C(K, ℝ)} (hdensity : MassDensityLimit C R H)
    (hflux : ∀ n a b, 0 ≤ a → a ≤ b → M n b = M n a + ∫ t in a..b, C n t * R n t ^ 2)
    (hstart : ∀ t, 0 ≤ t → Tendsto (fun n => M n t) atTop (𝓝 (M 0 t))) :
    MassResponseLimit C H M := by
  obtain ⟨T, hT, Q, hQ, hi, hlim⟩ := hdensity
  let F := fun n t => C n t * R n t ^ 2
  let G := fun n t => Q * H n t ^ 2
  let D := fun n t => F n t - F 0 t - G n t
  have hFi (n : ℕ) : IntegrableOn (F n) (Ici T) := (hi n).1
  have hDi (n : ℕ) : IntegrableOn (D n) (Ici T) := (hi n).2
  have hGi (n : ℕ) : IntegrableOn (G n) (Ici T) := by
    apply (((hFi n).sub (hFi 0)).sub (hDi n)).congr
    exact Eventually.of_forall (fun t => by
      change F n t - F 0 t - (F n t - F 0 t - G n t) = G n t
      abel)
  have hint {f : ℝ → C(K, ℝ)} (hf : IntegrableOn f (Ici T)) {t : ℝ} (ht : T ≤ t) :
      IntervalIntegrable f volume T t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact hf.mono_set (fun _ hs => hs.1.le)
  let Z := fun n => M n T + ∫ t in Ici T, F n t
  have hZ (n : ℕ) : Tendsto (M n) atTop (𝓝 (Z n)) := by
    have hh := (intervalIntegral_tendsto_integral_Ioi T
      ((hFi n).mono_set Ioi_subset_Ici_self) tendsto_id).const_add (M n T)
    rw [← integral_Ici_eq_integral_Ioi] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (hflux n T t hT ht).symm
  let B := fun n => ‖M n T - M 0 T‖ + ∫ t in Ici T, ‖D n t‖
  have hB : Tendsto B atTop (𝓝 0) := by
    have hh := ((hstart T hT).sub_const (M 0 T)).norm
    simpa only [sub_self, norm_zero, zero_add] using hh.add hlim
  have hfinite (n : ℕ) (t : ℝ) (ht : T ≤ t) :
      ‖M n t - M 0 t - ∫ s in T..t, G n s‖ ≤ B n := by
    have heq : M n t - M 0 t - (∫ s in T..t, G n s) =
        M n T - M 0 T + ∫ s in T..t, D n s := by
      rw [hflux n T t hT ht, hflux 0 T t hT ht]
      simp only [D, intervalIntegral.integral_sub ((hint (hFi n) ht).sub (hint (hFi 0) ht)) (hint (hGi n) ht),
        intervalIntegral.integral_sub (hint (hFi n) ht) (hint (hFi 0) ht)]
      abel
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add le_rfl
    rw [intervalIntegral.integral_of_le ht]
    exact (norm_integral_le_integral_norm _).trans
      (setIntegral_mono_set (hDi n).norm (Eventually.of_forall (fun _ => norm_nonneg _))
        (Eventually.of_forall (fun _ hs => hs.1.le)))
  have hterminal (n : ℕ) : ‖Z n - Z 0 - ∫ s in Ici T, G n s‖ ≤ B n := by
    have hdiff : IntegrableOn (fun t => F n t - F 0 t) (Ici T) := (hFi n).sub (hFi 0)
    have heq : Z n - Z 0 - (∫ s in Ici T, G n s) = M n T - M 0 T + ∫ s in Ici T, D n s := by
      simp only [Z, D, integral_sub hdiff (hGi n), integral_sub (hFi n) (hFi 0)]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_integral_le_integral_norm _))
  refine ⟨T, hT, Q, hQ, Z, hZ, ?_⟩
  intro d hd
  filter_upwards [hB.eventually_lt_const hd] with n hn
  exact ⟨fun t ht => (hfinite n t ht).trans_lt hn, (hterminal n).trans_lt hn⟩

theorem mass_profile_integrals {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {a : ℝ} (ha : 0 < a) (Q : C(K, ℝ)) (P : ℝ → ℝ) (c ℓ T t : ℝ) :
    (∫ s in T..t, Q * (ContinuousMap.const K (c * P (a * s + ℓ))) ^ 2) =
      (c ^ 2 / a * ∫ s in a * T + ℓ..a * t + ℓ, P s ^ 2) • Q ∧
    (∫ s in Ici T, Q * (ContinuousMap.const K (c * P (a * s + ℓ))) ^ 2) =
      (c ^ 2 / a * ∫ s in Ici (a * T + ℓ), P s ^ 2) • Q := by
  have he (s : ℝ) : Q * (ContinuousMap.const K (c * P (a * s + ℓ))) ^ 2 =
      (c ^ 2 * P (a * s + ℓ) ^ 2) • Q := by
    ext u
    simp only [ContinuousMap.mul_apply, ContinuousMap.pow_apply, ContinuousMap.const_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    ring
  simp_rw [he]
  constructor
  · rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add (fun s => P s ^ 2) ha.ne' ℓ]
    congr 1
    simp only [smul_eq_mul, div_eq_mul_inv, mul_assoc]
  · have himage : (fun s : ℝ => a * s + ℓ) '' Ici T = Ici (a * T + ℓ) := by
      ext y
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact add_le_add (mul_le_mul_of_nonneg_left hs ha.le) le_rfl
      · intro hy
        refine ⟨(y - ℓ) / a, ?_, ?_⟩
        · apply (le_div_iff₀ ha).2
          change a * T + ℓ ≤ y at hy
          nlinarith only [hy]
        · field_simp
          ring
    have hc := integral_image_eq_integral_abs_deriv_smul measurableSet_Ici
      (fun s (_hs : s ∈ Ici T) => show HasDerivWithinAt (fun w => a * w + ℓ) a (Ici T) s from by
        simpa only [id_eq, mul_one] using (((hasDerivAt_id s).const_mul a).add_const ℓ).hasDerivWithinAt)
      (fun _ _ _ _ hst => mul_left_cancel₀ ha.ne' (add_right_cancel hst)) (fun s => P s ^ 2)
    rw [himage] at hc
    simp only [abs_of_pos ha, smul_eq_mul, integral_const_mul] at hc
    rw [integral_smul_const, integral_const_mul, hc]
    congr 1
    field_simp

end CauchyHorizon
