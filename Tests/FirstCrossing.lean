import CauchyHorizon.Characteristic.PacketQuantiles

open Set Filter
open scoped Topology

namespace CauchyHorizon.Tests

-- Attainment at the initial endpoint is retained exactly.
example (T q : ℝ) : firstCrossing (fun _ => q) T q = T := by
  have hh := firstCrossing_of_bracket (f := fun _ => q) (q := q)
    continuous_const.continuousOn (T := T) (a := T) (b := T)
    le_rfl le_rfl (fun _ hv hvt => False.elim (not_lt_of_ge hv hvt)) le_rfl le_rfl
  exact le_antisymm hh.2.2 hh.2.1

-- This curve first decreases, then increases; its first level-one crossing is still well defined.
example : firstCrossing (fun v : ℝ => |v - 1| - 1) 0 1 = 3 := by
  have hh := firstCrossing_of_bracket (by fun_prop : ContinuousOn (fun v : ℝ => |v - 1| - 1) (Ici 0))
    (a := 2) (b := 3) (q := 1) (by norm_num) (by norm_num)
    (fun v hv hv2 => by
      have ha : |v - 1| < 2 := abs_lt.2 ⟨by linarith, by linarith⟩
      linarith only [ha]) (by norm_num) (by norm_num)
  have he := hh.1.1.2
  rw [abs_of_nonneg (by linarith only [hh.2.1])] at he
  linarith only [he]

-- Every earlier admissible time fails to attain the level, by the actual least-element statement.
example {f : ℝ → ℝ} {T q : ℝ}
    (hf : IsLeast {v | T ≤ v ∧ f v = q} (firstCrossing f T q)) :
    f (firstCrossing f T q) = q ∧
      ∀ v, T ≤ v → v < firstCrossing f T q → f v ≠ q := by
  refine ⟨hf.1.2, fun v hv hvf he => ?_⟩
  exact not_lt_of_ge (hf.2 ⟨hv, he⟩) hvf

-- Uniform approximation brackets the first crossing even when the perturbed curve oscillates.
example {f : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hc : ContinuousOn f (Ici 0)) (he : ∀ v, 0 ≤ v → |f v - v| ≤ η) :
    IsLeast {v | 0 ≤ v ∧ f v = 2} (firstCrossing f 0 2) ∧
      |firstCrossing f 0 2 - 2| ≤ 2 * η := by
  have hh := firstCrossing_profile_bracket hc (F := id) monotone_id (A := 1) (by norm_num)
    (d := η) (by simpa only [one_mul, id_eq] using he)
    (a := 2 - 2 * η) (b := 2 + 2 * η) (q := 2)
    (by linarith) (by linarith) (by dsimp; linarith) (by dsimp; linarith)
  exact ⟨hh.1, abs_le.2 ⟨by linarith only [hh.2.1], by linarith only [hh.2.2]⟩⟩

-- The exported mass statement uses half the actual terminal excess, with one eventual index for all rays.
example {K : Type*} [TopologicalSpace K] {M : ℕ → ℝ → C(K, ℝ)}
    {Mh : ℕ → C(K, ℝ)} {T : ℝ} (hf : HasMassFirstCrossings M Mh T) :
    ∀ᶠ n in atTop, ∀ u,
      let q := (1 / 2 : ℝ) * (Mh n - Mh 0) u
      let v := firstCrossing (fun t => (M n t - M 0 t) u) T q
      0 < (Mh n - Mh 0) u ∧ T ≤ v ∧ (M n v - M 0 v) u = q ∧
        ∀ t, T ≤ t → (M n t - M 0 t) u = q → v ≤ t := by
  filter_upwards [hf.2 (1 / 2) (by norm_num)] with n hn
  intro u
  have hh := (hn u).2 (1 / 2) le_rfl (by norm_num)
  exact ⟨(hn u).1, hh.1.1, hh.1.2, fun t ht he => hh.2 ⟨ht, he⟩⟩

end CauchyHorizon.Tests
