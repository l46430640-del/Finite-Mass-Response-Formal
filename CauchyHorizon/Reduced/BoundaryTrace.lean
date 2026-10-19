import CauchyHorizon.Reduced.RectangleRestriction
import CauchyHorizon.Analysis.TailLimit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Compatible finite developments determine continuous compact incoming traces. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

noncomputable def renormalizedWaveRow {U ε : ℝ} (hε : 0 ≤ ε) (k : ℝ)
    (X : (T : Ici (0 : ℝ)) → WaveState U T) (t : ℝ) : C(Icc ε U, WaveVector) :=
  let T : Ici (0 : ℝ) := ⟨max 0 t, le_max_left (0 : ℝ) t⟩
  let v : Icc 0 (T : ℝ) := ⟨T, T.property, le_rfl⟩
  ⟨fun u => (X T).1 ⟨u, hε.trans u.property.1, u.property.2⟩ v +
    (fun i => if i = 2 then 2 * k * t else 0), by fun_prop⟩

theorem renormalizedWaveRow_apply {U ε k : ℝ} (hε : 0 ≤ ε)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (T : Ici (0 : ℝ)) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (u : Icc ε U) (i : Fin 3) :
    renormalizedWaveRow hε k X t u i =
      (X T).1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨t, ht, htT⟩ i +
        (if i = 2 then 2 * k * t else 0) := by
  have he := congrArg (fun x : WaveState U (max 0 t) =>
    x.1 ⟨u, hε.trans u.property.1, u.property.2⟩ ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ i)
    (hcompat ⟨max 0 t, le_max_left (0 : ℝ) t⟩ T (max_le T.property htT))
  change (X T).1 ⟨0 + (u : ℝ), by simpa using hε.trans u.property.1, by simpa using u.property.2⟩
      ⟨0 + max 0 t, by simp, by simpa using max_le T.property htT⟩ i =
    (X ⟨max 0 t, le_max_left (0 : ℝ) t⟩).1 ⟨u, hε.trans u.property.1, u.property.2⟩
      ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ i at he
  simp only [zero_add, max_eq_right ht] at he
  change (X ⟨max 0 t, le_max_left (0 : ℝ) t⟩).1 ⟨u, hε.trans u.property.1, u.property.2⟩
      ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ i + (if i = 2 then 2 * k * t else 0) = _
  simp only [max_eq_right ht]
  exact congrArg
    (fun x => x + (if i = 2 then 2 * k * t else 0)) he.symm

theorem exists_renormalized_wave_limit {U ε k C η T₀ : ℝ} (hε : 0 ≤ ε)
    (hT₀ : 0 ≤ T₀) (hC : 0 ≤ C) (hη : 0 < η)
    (X : (T : Ici (0 : ℝ)) → WaveState U T)
    (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (htail : ∀ (T : Ici (0 : ℝ)) (u : Icc ε U) (a b : Icc 0 (T : ℝ)), T₀ ≤ a → a ≤ b →
      ∀ i : Fin 3,
        |(X T).1 ⟨u, hε.trans u.property.1, u.property.2⟩ b i -
          (X T).1 ⟨u, hε.trans u.property.1, u.property.2⟩ a i +
          (if i = 2 then 2 * k * ((b : ℝ) - a) else 0)| ≤ C * Real.exp (-η * a)) :
    ∃ z : C(Icc ε U, WaveVector),
      Tendsto (renormalizedWaveRow hε k X) atTop (𝓝 z) ∧
      (∀ t ≥ T₀, ‖renormalizedWaveRow hε k X t - z‖ ≤ C * Real.exp (-η * t)) ∧
      ∀ u : Icc ε U, 0 < Real.exp (z u 2) ∧
        Tendsto (fun t => Real.exp (2 * k * t) *
          Real.exp ((X ⟨max 0 t, le_max_left (0 : ℝ) t⟩).1 ⟨u, hε.trans u.property.1, u.property.2⟩
            ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ 2)) atTop (𝓝 (Real.exp (z u 2))) := by
  have hb : Tendsto (fun t : ℝ => C * Real.exp (-η * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq, mul_zero] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hη))).const_mul C
  obtain ⟨z, hz, hzbound⟩ := exists_limit_of_tail_bound hb (T := T₀) (f := renormalizedWaveRow hε k X) (by
    intro a ha b hab
    rw [dist_comm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (mul_nonneg hC (Real.exp_pos _).le)).2
    intro u
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)).2
    intro i
    have ha0 := hT₀.trans ha
    have hb0 := ha0.trans hab
    simp only [ContinuousMap.sub_apply, Pi.sub_apply,
      renormalizedWaveRow_apply hε X hcompat ⟨b, hb0⟩ hb0 le_rfl,
      renormalizedWaveRow_apply hε X hcompat ⟨b, hb0⟩ ha0 hab, Real.norm_eq_abs]
    convert htail ⟨b, hb0⟩ u ⟨a, ha0, hab⟩ ⟨b, hb0, le_rfl⟩ ha hab i using 1
    split_ifs <;> congr 1 <;> ring)
  refine ⟨z, hz, (fun t ht => by simpa only [dist_eq_norm] using hzbound t ht), fun u => ⟨Real.exp_pos _, ?_⟩⟩
  have he := ((continuous_apply 2).comp (continuous_eval_const u)).tendsto z |>.comp hz
  have hex := Real.continuous_exp.continuousAt.tendsto.comp he
  change Tendsto (fun t => Real.exp (
    (X ⟨max 0 t, le_max_left (0 : ℝ) t⟩).1 ⟨u, hε.trans u.property.1, u.property.2⟩
      ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ 2 + 2 * k * t)) atTop (𝓝 (Real.exp (z u 2))) at hex
  simpa only [Real.exp_add, mul_comm] using hex

end CauchyHorizon
