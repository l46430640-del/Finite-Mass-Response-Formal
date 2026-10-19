import CauchyHorizon.Reduced.MassFlux
import CauchyHorizon.Reduced.MassCoefficientContinuity

/-! Actual mass rows, their flux integral, and finite-time sequence convergence. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def massRow {U ε : ℝ} (hε : 0 ≤ ε) (e Λ : ℝ)
    (X : (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)))
    (hr : ∀ (V : Ici (0 : ℝ)) u v, (X V).1 u v 0 ≠ 0) : ℝ → C(Icc ε U, ℝ) :=
  scalarBoundaryRow hε (fun V => massField e Λ (X V).1 (X V).2.1 (N V) (hr V))

theorem mass_rows {U ε k e Λ : ℝ} (hε : 0 ≤ ε)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V)
    (N : (n : ℕ) → (V : Ici (0 : ℝ)) → C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)))
    (hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0)
    (hX : ∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X n T) = X n S)
    (hN : ∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      N n S u v = N n T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (hflux : ∀ n (V : Ici (0 : ℝ)) (u : Icc 0 U) (v : Icc 0 (V : ℝ)),
      let m := massField e Λ (X n V).1 (X n V).2.1 (N n V) (hr n V)
      m u v = m u ⟨0, le_rfl, V.property⟩ + ∫ t in (0 : ℝ)..v,
        -2 * (intervalExtension V.property ((X n V).1 u) t 0) ^ 2 *
          intervalExtension V.property (N n V u) t *
          Real.exp (-intervalExtension V.property ((X n V).1 u) t 2) *
          (intervalExtension V.property ((X n V).2.1 u) t 1) ^ 2)
    (hfinite : ∀ V, Tendsto (fun n => X n V) atTop (𝓝 (X 0 V)))
    (hNfinite : ∀ V, Tendsto (fun n => N n V) atTop (𝓝 (N 0 V))) :
    let J : C(Icc ε U, Icc 0 U) := ⟨fun u => ⟨u, hε.trans u.property.1, u.property.2⟩, by fun_prop⟩
    let M := fun n => massRow hε e Λ (X n) (N n) (hr n)
    (∀ n a b, 0 ≤ a → a ≤ b →
      M n b = M n a + ∫ t in a..b,
        massCoefficientRow hε k (X n) (N n) t * ((radiationRow k (X n) t).comp J) ^ 2) ∧
      ∀ t, 0 ≤ t → Tendsto (fun n => M n t) atTop (𝓝 (M 0 t)) := by
  dsimp only
  let J : C(Icc ε U, Icc 0 U) := ⟨fun u => ⟨u, hε.trans u.property.1, u.property.2⟩, by fun_prop⟩
  let F := fun n t => massCoefficientRow hε k (X n) (N n) t * ((radiationRow k (X n) t).comp J) ^ 2
  let m := fun n V => massField e Λ (X n V).1 (X n V).2.1 (N n V) (hr n V)
  have hmc (n : ℕ) (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v :
      m n S u v = m n T u ⟨v, v.property.1, v.property.2.trans hST⟩ := by
    have hz := congrArg (fun w : WaveState U S => w.1 u v) (hX n S T hST)
    have hw := congrArg (fun w : WaveState U S => w.2.1 u v) (hX n S T hST)
    change (X n T).1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X n S).1 u v at hz
    change (X n T).2.1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X n S).2.1 u v at hw
    simp only [zero_add] at hz hw
    simp only [m, massField_apply, ← hz, ← hw, hN n S T hST]
  have he (n : ℕ) (V : Ici (0 : ℝ)) {t : ℝ} (ht : 0 ≤ t) (htV : t ≤ V) (u : Icc ε U) :
      massRow hε e Λ (X n) (N n) (hr n) t u = m n V (J u) ⟨t, ht, htV⟩ :=
    scalarBoundaryRow_apply hε (m n) (hmc n) V ht htV u
  have hFc (n : ℕ) : ContinuousOn (F n) (Ici 0) :=
    (continuousOn_massCoefficientRow hε (X n) (N n) (hX n) (hN n)).mul
      (((ContinuousMap.compCLM ℝ ℝ J).continuous.comp (continuous_radiationRow (X n) (hX n))).continuousOn.pow 2)
  have hFi (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable (F n) volume a b :=
    ((hFc n).mono (fun _ ht => ha.trans ht.1)).intervalIntegrable_of_Icc hab
  constructor
  · intro n a b ha hab
    let V : Ici (0 : ℝ) := ⟨b, ha.trans hab⟩
    have hzero (t : ℝ) (ht : 0 ≤ t) (htb : t ≤ b) (u : Icc ε U) :
        massRow hε e Λ (X n) (N n) (hr n) t u = m n V (J u) ⟨0, le_rfl, V.property⟩ +
          (∫ s in (0 : ℝ)..t, F n s) u := by
      rw [he n V ht htb u]
      have hh := hflux n V (J u) ⟨t, ht, htb⟩
      change m n V (J u) ⟨t, ht, htb⟩ = m n V (J u) ⟨0, le_rfl, V.property⟩ + _ at hh
      have hev := (ContinuousMap.evalCLM ℝ u).intervalIntegral_comp_comm (hFi n le_rfl ht)
      simp only [ContinuousMap.evalCLM_apply] at hev
      rw [← hev]
      apply hh.trans
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht] at hs
      have hsV : s ∈ Icc 0 (V : ℝ) := ⟨hs.1, hs.2.trans htb⟩
      change -2 * ((X n V).1 (J u) (projIcc 0 (V : ℝ) V.property s) 0) ^ 2 *
        N n V (J u) (projIcc 0 (V : ℝ) V.property s) *
        Real.exp (-((X n V).1 (J u) (projIcc 0 (V : ℝ) V.property s) 2)) *
        ((X n V).2.1 (J u) (projIcc 0 (V : ℝ) V.property s) 1) ^ 2 = F n s u
      rw [projIcc_of_mem V.property hsV]
      exact (massCoefficientRow_apply (k := k) hε (X n) (N n) (hX n) (hN n) V hsV.1 hsV.2 u).2.symm
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hFi n le_rfl ha) (hFi n ha hab)
    ext u
    simp only [ContinuousMap.add_apply, hzero b (ha.trans hab) le_rfl u, hzero a ha hab u]
    have hh := congrArg (fun f : C(Icc ε U, ℝ) => f u) hsplit
    simp only [ContinuousMap.add_apply] at hh
    linarith only [hh]
  · intro t ht
    let V : Ici (0 : ℝ) := ⟨t, ht⟩
    let P := {w : WaveState U V // ∀ u v, w.1 u v 0 ≠ 0}
    let G : C(P × C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ)), C(Icc ε U, ℝ)) :=
      (⟨fun q : (P × C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ))) × Icc ε U =>
        renormalizedMass (q.1.1.val.1 (J q.2) ⟨t, ht, le_rfl⟩ 0)
          (q.1.2 (J q.2) ⟨t, ht, le_rfl⟩)
          (q.1.1.val.2.1 (J q.2) ⟨t, ht, le_rfl⟩ 0)
          (q.1.1.val.1 (J q.2) ⟨t, ht, le_rfl⟩ 2) e Λ, by
        have hv : Continuous (fun q : (P × C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ))) × Icc ε U => q.1.1.val) :=
          continuous_subtype_val.comp continuous_fst.fst
        have hu := J.continuous.comp (continuous_snd (X := P × C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ))))
        have hz := (hv.fst.eval hu).eval (continuous_const (y := (⟨t, ht, le_rfl⟩ : Icc 0 (V : ℝ))))
        have hw := (hv.snd.fst.eval hu).eval (continuous_const (y := (⟨t, ht, le_rfl⟩ : Icc 0 (V : ℝ))))
        have hn := (continuous_fst.snd.eval hu).eval (continuous_const (y := (⟨t, ht, le_rfl⟩ : Icc 0 (V : ℝ))))
        have hR := (continuous_apply (0 : Fin 3)).comp hz
        have hL := (continuous_apply (0 : Fin 3)).comp hw
        have hE := (continuous_apply (2 : Fin 3)).comp hz
        exact ((hR.div_const 2).add ((continuous_const (y := e ^ 2)).div (hR.const_mul 2)
          (fun q => mul_ne_zero (by norm_num) (q.1.1.property _ _))) |>.sub
            ((hR.pow 3).const_mul Λ |>.div_const 6)).add
          ((((hR.const_mul 2).mul hn).mul hL).mul (Real.continuous_exp.comp hE.neg))⟩ :
            C((P × C(Icc 0 U, C(Icc 0 (V : ℝ), ℝ))) × Icc ε U, ℝ)).curry
    have hl : Tendsto (fun n => (⟨X n V, hr n V⟩ : P)) atTop (𝓝 (⟨X 0 V, hr 0 V⟩ : P)) :=
      tendsto_subtype_rng.2 (hfinite V)
    have heq (n : ℕ) : G (⟨X n V, hr n V⟩, N n V) = massRow hε e Λ (X n) (N n) (hr n) t := by
      ext u
      exact (he n V ht le_rfl u).symm
    simpa only [Function.comp_def, heq] using
      G.continuous.tendsto (⟨X 0 V, hr 0 V⟩, N 0 V) |>.comp (hl.prodMk_nhds (hNfinite V))

end CauchyHorizon
