import CauchyHorizon.Reduced.MassRows

/-! One absolute mass bound on all physical prefixes and their actual horizon limits. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

def HasUniformMassBound {U : ℝ} (e Λ : ℝ) (zIn : ℕ → C(Icc 0 U, WaveVector))
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0,
    ∀ n (V : Ici (0 : ℝ)) u v,
      let ν := radialNuField V.property e Λ (zIn n) (X n V).1 (hr n V)
      |massField e Λ (X n V).1 (X n V).2.1 ν (hr n V) u v| ≤ C

theorem HasUniformMassBound.rows_and_limits {U e Λ : ℝ}
    {zIn : ℕ → C(Icc 0 U, WaveVector)}
    {X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V}
    (h : HasUniformMassBound e Λ zIn X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 ≤ ε),
      ∀ hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0,
        let ν := fun n (V : Ici (0 : ℝ)) => radialNuField V.property e Λ (zIn n) (X n V).1 (hr n V)
        (∀ n t, ‖massRow hε e Λ (X n) (ν n) (hr n) t‖ ≤ C) ∧
        ∀ Mh : ℕ → C(Icc ε U, ℝ),
          (∀ n, Tendsto (massRow hε e Λ (X n) (ν n) (hr n)) atTop (𝓝 (Mh n))) →
          ∀ n, ‖Mh n‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun ε hε hr => ?_⟩
  let ν := fun n (V : Ici (0 : ℝ)) => radialNuField V.property e Λ (zIn n) (X n V).1 (hr n V)
  have hrow (n : ℕ) (t : ℝ) : ‖massRow hε e Λ (X n) (ν n) (hr n) t‖ ≤ C := by
    apply (ContinuousMap.norm_le _ hC).2
    intro u
    rw [Real.norm_eq_abs]
    exact hb hr n ⟨max 0 t, le_max_left (0 : ℝ) t⟩ ⟨u, hε.trans u.property.1, u.property.2⟩
      ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩
  exact ⟨hrow, fun Mh hMh n => le_of_tendsto (hMh n).norm (Eventually.of_forall (hrow n))⟩

end CauchyHorizon
