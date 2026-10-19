import CauchyHorizon.Reduced.MassCoefficient

open Set Filter
open scoped Topology

namespace CauchyHorizon

theorem continuousOn_massCoefficientRow {U ε k : ℝ} (hε : 0 ≤ ε)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)))
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hN : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      N S u v = N T u ⟨v, v.property.1, v.property.2.trans hST⟩) :
    ContinuousOn (massCoefficientRow hε k X N) (Ici 0) := by
  intro t ht
  let V : Ici (0 : ℝ) := ⟨t + 1, by
    change 0 ≤ t + 1
    exact add_nonneg (show 0 ≤ t from ht) zero_le_one⟩
  let J : C(Icc ε U, Icc 0 U) := ⟨fun u => ⟨u, hε.trans u.property.1, u.property.2⟩, by fun_prop⟩
  let F : C(ℝ, C(Icc ε U, ℝ)) :=
    (⟨fun w : ℝ × Icc ε U => -2 * N V (J w.2) (projIcc 0 (V : ℝ) V.property w.1) *
      Real.exp (-((X V).1 (J w.2) (projIcc 0 (V : ℝ) V.property w.1) 2 + 2 * k * w.1)),
        by fun_prop⟩ : C(ℝ × Icc ε U, ℝ)).curry
  have he (s : ℝ) (hs : 0 ≤ s) (hsV : s ≤ V) : massCoefficientRow hε k X N s = F s := by
    ext u
    rw [(massCoefficientRow_apply hε X N hX hN V hs hsV u).1]
    simp only [F, J, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
      projIcc_of_mem V.property (show s ∈ Icc 0 (V : ℝ) from ⟨hs, hsV⟩),
      Real.exp_neg, Real.exp_add, div_eq_mul_inv]
    ring
  apply F.continuous.continuousWithinAt.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [(eventually_lt_nhds (show t < (V : ℝ) from lt_add_one t)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hs0
  exact he s hs0 hs.le

end CauchyHorizon
