import CauchyHorizon.Analysis.PrimitiveCompatibility
import Mathlib.MeasureTheory.Function.L2Space

/-! An integrable derivative and a continuous endpoint determine affine continuation data. -/

open MeasureTheory Set Filter

namespace CauchyHorizon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def IsAffineCharacteristicData (a b : ℝ)
    (f g : ℝ → E) (q : E) (z : C(Icc a b, E)) (d : Lp E 2 (volume.restrict (Icc a b))) : Prop :=
  (∃ hab : a ≤ b, z = ContinuousMap.const _ (f a) + horizontalPrimitive hab d) ∧
  (∀ x : Icc a b, (x : ℝ) ≤ 0 → z x = f x) ∧
  (∀ x : Icc a b, 0 ≤ (x : ℝ) → z x = f 0 + (x : ℝ) • q) ∧
  (d =ᵐ[volume.restrict (Icc a 0)] g) ∧
  (d =ᵐ[volume.restrict (Ioc 0 b)] fun _ => q) ∧
  (∫ x in Icc a b, ‖d x‖ ^ 2) = (∫ x in Icc a 0, ‖g x‖ ^ 2) + b * ‖q‖ ^ 2

set_option maxHeartbeats 800000 in
theorem exists_affine_characteristic_data {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    {f g : ℝ → E} (hc : ContinuousOn f (Icc a 0))
    (hd : ∀ x ∈ Ioo a 0, HasDerivAt f (g x) x)
    (hg : MemLp g 2 (volume.restrict (Icc a 0))) (q : E) :
    ∃ z : C(Icc a b, E), ∃ d : Lp E 2 (volume.restrict (Icc a b)),
      IsAffineCharacteristicData a b f g q z d := by
  classical
  let G := (Iic (0 : ℝ)).piecewise g (fun _ => q)
  have hG : MemLp G 2 (volume.restrict (Icc a b)) := by
    apply MemLp.piecewise measurableSet_Iic
    · rw [Measure.restrict_restrict measurableSet_Iic]
      have he : Iic (0 : ℝ) ∩ Icc a b = Icc a 0 := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hb⟩⟩
      rw [he]
      exact hg
    · exact memLp_const q
  let d := hG.toLp G
  let z := ContinuousMap.const (Icc a b) (f a) + horizontalPrimitive (ha.trans hb) d
  have hlsub : Icc a 0 ⊆ Icc a b := Icc_subset_Icc le_rfl hb
  have hrsub : Ioc 0 b ⊆ Icc a b := fun x hx => ⟨ha.trans hx.1.le, hx.2⟩
  have hl : d =ᵐ[volume.restrict (Icc a 0)] g := by
    filter_upwards [ae_mono (Measure.restrict_mono hlsub le_rfl) hG.coeFn_toLp,
      ae_restrict_mem measurableSet_Icc] with x hx hm
    exact hx.trans (if_pos hm.2)
  have hr : d =ᵐ[volume.restrict (Ioc 0 b)] fun _ => q := by
    filter_upwards [ae_mono (Measure.restrict_mono hrsub le_rfl) hG.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with x hx hm
    exact hx.trans (if_neg (not_le.mpr hm.1))
  have hgi : IntegrableOn g (Icc a 0) := hg.integrable (by norm_num)
  have hdi : IntegrableOn (fun x => d x) (Icc a b) := (Lp.memLp d).integrable (by norm_num)
  have hleft (x : Icc a 0) : (∫ t in a..(x : ℝ), d t) = f x - f a := by
    have hs : Ioc a (x : ℝ) ⊆ Icc a 0 := fun t ht => ⟨ht.1.le, ht.2.trans x.property.2⟩
    have he : (∫ t in a..(x : ℝ), d t) = ∫ t in a..(x : ℝ), g t := by
      simp only [intervalIntegral.integral_of_le x.property.1]
      exact integral_congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) hl)
    rw [he]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le x.property.1
      (hc.mono (Icc_subset_Icc le_rfl x.property.2))
      (fun t ht => hd t ⟨ht.1, ht.2.trans_le x.property.2⟩)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le x.property.1).2
        (hgi.mono_set (Icc_subset_Icc le_rfl x.property.2)))
  have hright (x : Icc 0 b) : (∫ t in (0 : ℝ)..(x : ℝ), d t) = (x : ℝ) • q := by
    have hs : Ioc (0 : ℝ) (x : ℝ) ⊆ Ioc 0 b := Ioc_subset_Ioc le_rfl x.property.2
    have he : (∫ t in (0 : ℝ)..(x : ℝ), d t) = ∫ _t in (0 : ℝ)..(x : ℝ), q := by
      simp only [intervalIntegral.integral_of_le x.property.1]
      exact integral_congr_ae (ae_mono (Measure.restrict_mono hs le_rfl) hr)
    rw [he, intervalIntegral.integral_const, sub_zero]
  refine ⟨z, d, ⟨ha.trans hb, rfl⟩, ?_, ?_, hl, hr, ?_⟩
  · intro x hx
    change f a + (∫ t in a..(x : ℝ), d t) = f x
    rw [hleft ⟨x, x.property.1, hx⟩]
    abel
  · intro x hx
    have hda0 : IntervalIntegrable (fun t => d t) volume a 0 :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ha).2 (hdi.mono_set hlsub)
    have hd0x : IntervalIntegrable (fun t => d t) volume 0 x :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx).2
        (hdi.mono_set (Icc_subset_Icc ha x.property.2))
    change f a + (∫ t in a..(x : ℝ), d t) = f 0 + (x : ℝ) • q
    rw [← intervalIntegral.integral_add_adjacent_intervals hda0 hd0x,
      hleft ⟨0, ha, le_rfl⟩, hright ⟨x, hx, x.property.2⟩]
    abel
  · have hi : IntegrableOn (fun x => ‖d x‖ ^ 2) (Icc a b) :=
      (memLp_two_iff_integrable_sq_norm (Lp.memLp d).1).1 (Lp.memLp d)
    have hdis : Disjoint (Icc a (0 : ℝ)) (Ioc 0 b) := by
      apply disjoint_left.2
      intro x hx hy
      exact (not_lt_of_ge hx.2) hy.1
    have hsum := setIntegral_union hdis measurableSet_Ioc (hi.mono_set hlsub) (hi.mono_set hrsub)
    rw [Icc_union_Ioc_eq_Icc ha hb] at hsum
    rw [hsum]
    rw [integral_congr_ae (hl.mono (fun _ hx => congrArg (fun y => ‖y‖ ^ 2) hx)),
      integral_congr_ae (hr.mono (fun _ hx => congrArg (fun y => ‖y‖ ^ 2) hx)), setIntegral_const]
    simp only [Real.volume_real_Ioc, sub_zero, max_eq_left hb, smul_eq_mul]

end CauchyHorizon
