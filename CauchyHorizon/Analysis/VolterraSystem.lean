import CauchyHorizon.Analysis.VolterraOperator

/-! A coupled Volterra system on a closed interval, including integrable singular endpoints. -/

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace CauchyHorizon

variable {a b : ℝ} (hab : a ≤ b)

def IsVolterraPair (c d : ℝ → ℝ) (X₀ V₀ : ℝ)
    (p : C(Icc a b, ℝ) × C(Icc a b, ℝ)) : Prop :=
  ∀ x : Icc a b,
    p.1 x = X₀ + ∫ t in a..(x : ℝ), c t * extendCurve hab p.2 t ∧
    p.2 x = V₀ + ∫ t in a..(x : ℝ), d t * extendCurve hab p.1 t

section Weighted

variable {c d w : ℝ → ℝ}
variable (hc : IntervalIntegrable c volume a b) (hd : IntervalIntegrable d volume a b)
variable (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ t ∈ uIcc a b, 0 < w t)

noncomputable def divideCurve (f : C(Icc a b, ℝ)) : C(Icc a b, ℝ) where
  toFun x := f x / w x
  continuous_toFun := f.continuous.div (by
    have h := hw
    rw [uIcc_of_le hab] at h
    exact h.domRestrict) (fun x => (hwpos x (by
      simpa only [uIcc_of_le hab] using x.property)).ne')

noncomputable def weightedVolterraMap (X₀ V₀ : ℝ)
    (p : C(Icc a b, ℝ) × C(Icc a b, ℝ)) :
    C(Icc a b, ℝ) × C(Icc a b, ℝ) :=
  (divideCurve hab hw hwpos (.const _ X₀) + weightedPrimitive hab hc hw hwpos p.2,
   divideCurve hab hw hwpos (.const _ V₀) + weightedPrimitive hab hd hw hwpos p.1)

theorem weightedVolterraMap_contracting (X₀ V₀ : ℝ)
    (hck : ∀ x ∈ Icc a b, (∫ t in a..x, |c t| * w t) ≤ (1 / 2 : ℝ) * w x)
    (hdk : ∀ x ∈ Icc a b, (∫ t in a..x, |d t| * w t) ≤ (1 / 2 : ℝ) * w x) :
    ContractingWith (1 / 2) (weightedVolterraMap hab hc hd hw hwpos X₀ V₀) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun p q => ?_⟩
  have hcl := weightedPrimitive_lipschitz hab hc hw hwpos (1 / 2) (by simpa using hck)
  have hdl := weightedPrimitive_lipschitz hab hd hw hwpos (1 / 2) (by simpa using hdk)
  simp only [weightedVolterraMap, Prod.dist_eq, dist_add_left]
  apply max_le
  · exact (hcl.dist_le_mul p.2 q.2).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
  · exact (hdl.dist_le_mul p.1 q.1).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))

theorem weightedVolterraMap_fixed_iff (X₀ V₀ : ℝ)
    (p : C(Icc a b, ℝ) × C(Icc a b, ℝ)) :
    Function.IsFixedPt (weightedVolterraMap hab hc hd hw hwpos X₀ V₀)
      (divideCurve hab hw hwpos p.1, divideCurve hab hw hwpos p.2) ↔
      IsVolterraPair hab c d X₀ V₀ p := by
  have hcancel (e : ℝ → ℝ) (f : C(Icc a b, ℝ)) (x : Icc a b) :
      (∫ t in a..(x : ℝ), e t *
        (w t * extendCurve hab (divideCurve hab hw hwpos f) t)) =
      ∫ t in a..(x : ℝ), e t * extendCurve hab f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc a b := by
      rw [uIcc_of_le x.property.1] at ht
      exact ⟨ht.1, ht.2.trans x.property.2⟩
    have hn := (hwpos t (by simpa only [uIcc_of_le hab] using ht')).ne'
    simp only [extendCurve, divideCurve, ContinuousMap.coe_mk, projIcc_of_mem hab ht']
    field_simp
  change weightedVolterraMap hab hc hd hw hwpos X₀ V₀ _ = _ ↔ _
  rw [Prod.ext_iff]
  simp only [ContinuousMap.ext_iff]
  constructor
  · rintro ⟨hX, hV⟩ x
    have hn := (hwpos x (by simpa only [uIcc_of_le hab] using x.property)).ne'
    have hx := hX x
    have hv := hV x
    change X₀ / w x + (∫ t in a..(x : ℝ), c t *
      (w t * extendCurve hab (divideCurve hab hw hwpos p.2) t)) / w x = p.1 x / w x at hx
    change V₀ / w x + (∫ t in a..(x : ℝ), d t *
      (w t * extendCurve hab (divideCurve hab hw hwpos p.1) t)) / w x = p.2 x / w x at hv
    rw [hcancel, ← add_div, div_left_inj' hn] at hx
    rw [hcancel, ← add_div, div_left_inj' hn] at hv
    exact ⟨hx.symm, hv.symm⟩
  · intro hp
    constructor <;> intro x
    · change X₀ / w x + (∫ t in a..(x : ℝ), c t *
        (w t * extendCurve hab (divideCurve hab hw hwpos p.2) t)) / w x = p.1 x / w x
      rw [hcancel, ← add_div, (hp x).1]
    · change V₀ / w x + (∫ t in a..(x : ℝ), d t *
        (w t * extendCurve hab (divideCurve hab hw hwpos p.1) t)) / w x = p.2 x / w x
      rw [hcancel, ← add_div, (hp x).2]

theorem weightedVolterraMap_fixedPoint_nonneg {X₀ V₀ : ℝ}
    (hX : 0 ≤ X₀) (hV : 0 ≤ V₀)
    (hcpos : ∀ t ∈ Icc a b, 0 ≤ c t) (hdpos : ∀ t ∈ Icc a b, 0 ≤ d t)
    (hcon : ContractingWith (1 / 2) (weightedVolterraMap hab hc hd hw hwpos X₀ V₀)) :
    0 ≤ hcon.fixedPoint (weightedVolterraMap hab hc hd hw hwpos X₀ V₀) := by
  let T := weightedVolterraMap hab hc hd hw hwpos X₀ V₀
  have hmaps (p : C(Icc a b, ℝ) × C(Icc a b, ℝ)) (hp : 0 ≤ p) : 0 ≤ T p := by
    constructor
    · intro x
      exact add_nonneg (div_nonneg hX (hwpos x (by
        simpa only [uIcc_of_le hab] using x.property)).le)
        (weightedPrimitive_nonneg hab hc hw hwpos hcpos p.2 hp.2 x)
    · intro x
      exact add_nonneg (div_nonneg hV (hwpos x (by
        simpa only [uIcc_of_le hab] using x.property)).le)
        (weightedPrimitive_nonneg hab hd hw hwpos hdpos p.1 hp.1 x)
  have hi (n : ℕ) : 0 ≤ T^[n] 0 := by
    induction n with
    | zero => exact le_refl _
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmaps _ ih
  have hlim := hcon.tendsto_iterate_fixedPoint 0
  constructor
  · intro x
    exact ge_of_tendsto' (((continuous_eval_const x).comp continuous_fst).tendsto _ |>.comp hlim)
      (fun n => (hi n).1 x)
  · intro x
    exact ge_of_tendsto' (((continuous_eval_const x).comp continuous_snd).tendsto _ |>.comp hlim)
      (fun n => (hi n).2 x)

include hc hd hw hwpos in
theorem exists_unique_volterraPair_of_weight (X₀ V₀ : ℝ)
    (hck : ∀ x ∈ Icc a b, (∫ t in a..x, |c t| * w t) ≤ (1 / 2 : ℝ) * w x)
    (hdk : ∀ x ∈ Icc a b, (∫ t in a..x, |d t| * w t) ≤ (1 / 2 : ℝ) * w x) :
    ∃! p, IsVolterraPair hab c d X₀ V₀ p := by
  let T := weightedVolterraMap hab hc hd hw hwpos X₀ V₀
  have hcon : ContractingWith (1 / 2) T :=
    weightedVolterraMap_contracting hab hc hd hw hwpos X₀ V₀ hck hdk
  let q := hcon.fixedPoint T
  let W : C(Icc a b, ℝ) := ⟨fun x => w x, by
    have h := hw
    rw [uIcc_of_le hab] at h
    exact h.domRestrict⟩
  have hdiv (f : C(Icc a b, ℝ)) : divideCurve hab hw hwpos (W * f) = f := by
    ext x
    change w x * f x / w x = f x
    exact mul_div_cancel_left₀ _ (hwpos x (by
      simpa only [uIcc_of_le hab] using x.property)).ne'
  refine ⟨(W * q.1, W * q.2), ?_, ?_⟩
  · apply (weightedVolterraMap_fixed_iff hab hc hd hw hwpos X₀ V₀ _).1
    simpa only [hdiv] using hcon.fixedPoint_isFixedPt
  · intro p hp
    have hfixed := (weightedVolterraMap_fixed_iff hab hc hd hw hwpos X₀ V₀ p).2 hp
    have heq := hcon.fixedPoint_unique hfixed
    have heq₁ := congrArg Prod.fst heq
    have heq₂ := congrArg Prod.snd heq
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro x
    · have hx := congrArg (fun f : C(Icc a b, ℝ) => f x) heq₁
      change p.1 x / w x = q.1 x at hx
      change p.1 x = w x * q.1 x
      rw [(div_eq_iff (hwpos x (by
        simpa only [uIcc_of_le hab] using x.property)).ne').1 hx, mul_comm]
    · have hx := congrArg (fun f : C(Icc a b, ℝ) => f x) heq₂
      change p.2 x / w x = q.2 x at hx
      change p.2 x = w x * q.2 x
      rw [(div_eq_iff (hwpos x (by
        simpa only [uIcc_of_le hab] using x.property)).ne').1 hx, mul_comm]

include hc hd hw hwpos in
theorem volterraPair_nonneg_of_weight {X₀ V₀ : ℝ}
    (hck : ∀ x ∈ Icc a b, (∫ t in a..x, |c t| * w t) ≤ (1 / 2 : ℝ) * w x)
    (hdk : ∀ x ∈ Icc a b, (∫ t in a..x, |d t| * w t) ≤ (1 / 2 : ℝ) * w x)
    (hX : 0 ≤ X₀) (hV : 0 ≤ V₀)
    (hcpos : ∀ t ∈ Icc a b, 0 ≤ c t) (hdpos : ∀ t ∈ Icc a b, 0 ≤ d t)
    {p : C(Icc a b, ℝ) × C(Icc a b, ℝ)} (hp : IsVolterraPair hab c d X₀ V₀ p) :
    0 ≤ p := by
  have hcon := weightedVolterraMap_contracting hab hc hd hw hwpos X₀ V₀ hck hdk
  have hpos := weightedVolterraMap_fixedPoint_nonneg hab hc hd hw hwpos hX hV hcpos hdpos hcon
  have heq := hcon.fixedPoint_unique
    ((weightedVolterraMap_fixed_iff hab hc hd hw hwpos X₀ V₀ p).2 hp)
  rw [← heq] at hpos
  constructor <;> intro x
  · simpa using (le_div_iff₀ (hwpos x (by
      simpa only [uIcc_of_le hab] using x.property))).1 (hpos.1 x)
  · simpa using (le_div_iff₀ (hwpos x (by
      simpa only [uIcc_of_le hab] using x.property))).1 (hpos.2 x)

end Weighted

include hab in
theorem exists_volterra_weight {c d : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) (hd : IntervalIntegrable d volume a b)
    (hcc : ContinuousOn c (Ioo a b)) (hdc : ContinuousOn d (Ioo a b)) :
    ∃ w : ℝ → ℝ, ContinuousOn w (uIcc a b) ∧ (∀ t ∈ uIcc a b, 0 < w t) ∧
      (∀ x ∈ Icc a b, (∫ t in a..x, |c t| * w t) ≤ (1 / 2 : ℝ) * w x) ∧
      (∀ x ∈ Icc a b, (∫ t in a..x, |d t| * w t) ≤ (1 / 2 : ℝ) * w x) := by
  let m := fun t => |c t| + |d t|
  have hm : IntervalIntegrable m volume a b := hc.abs.add hd.abs
  have hmc : ContinuousOn m (Ioo a b) := hcc.abs.add hdc.abs
  refine ⟨volterraWeight a m, volterraWeight_continuous hm,
    fun t _ => volterraWeight_pos a m t, ?_, ?_⟩
  · exact volterraWeight_kernel_bound hab hc hm hmc (fun t _ => le_add_of_nonneg_right (abs_nonneg _))
  · exact volterraWeight_kernel_bound hab hd hm hmc (fun t _ => le_add_of_nonneg_left (abs_nonneg _))

theorem exists_unique_volterraPair {c d : ℝ → ℝ}
    (hc : IntervalIntegrable c volume a b) (hd : IntervalIntegrable d volume a b)
    (hcc : ContinuousOn c (Ioo a b)) (hdc : ContinuousOn d (Ioo a b)) (X₀ V₀ : ℝ) :
    ∃! p, IsVolterraPair hab c d X₀ V₀ p := by
  obtain ⟨w, hw, hwpos, hck, hdk⟩ := exists_volterra_weight hab hc hd hcc hdc
  exact exists_unique_volterraPair_of_weight hab hc hd hw hwpos X₀ V₀ hck hdk

theorem volterraPair_nonneg {c d : ℝ → ℝ} {X₀ V₀ : ℝ}
    (hc : IntervalIntegrable c volume a b) (hd : IntervalIntegrable d volume a b)
    (hcc : ContinuousOn c (Ioo a b)) (hdc : ContinuousOn d (Ioo a b))
    (hX : 0 ≤ X₀) (hV : 0 ≤ V₀)
    (hcpos : ∀ t ∈ Icc a b, 0 ≤ c t) (hdpos : ∀ t ∈ Icc a b, 0 ≤ d t)
    {p : C(Icc a b, ℝ) × C(Icc a b, ℝ)} (hp : IsVolterraPair hab c d X₀ V₀ p) :
    0 ≤ p := by
  obtain ⟨w, hw, hwpos, hck, hdk⟩ := exists_volterra_weight hab hc hd hcc hdc
  exact volterraPair_nonneg_of_weight hab hc hd hw hwpos hck hdk hX hV hcpos hdpos hp

theorem volterraPair_lower_bounds {c d : ℝ → ℝ} {X₀ V₀ : ℝ}
    (hcpos : ∀ t ∈ Icc a b, 0 ≤ c t) (hdpos : ∀ t ∈ Icc a b, 0 ≤ d t)
    {p : C(Icc a b, ℝ) × C(Icc a b, ℝ)} (hp : IsVolterraPair hab c d X₀ V₀ p)
    (hp0 : 0 ≤ p) (x : Icc a b) : X₀ ≤ p.1 x ∧ V₀ ≤ p.2 x := by
  constructor
  · rw [(hp x).1]
    apply le_add_of_nonneg_right
    apply intervalIntegral.integral_nonneg x.property.1
    intro t ht
    exact mul_nonneg (hcpos t ⟨ht.1, ht.2.trans x.property.2⟩)
      (hp0.2 (projIcc a b hab t))
  · rw [(hp x).2]
    apply le_add_of_nonneg_right
    apply intervalIntegral.integral_nonneg x.property.1
    intro t ht
    exact mul_nonneg (hdpos t ⟨ht.1, ht.2.trans x.property.2⟩)
      (hp0.1 (projIcc a b hab t))

theorem volterraPair_strict_positive {c d : ℝ → ℝ} {V₀ : ℝ}
    (hc : IntervalIntegrable c volume a b) (hV : 0 < V₀)
    (hcpos : ∀ t ∈ Icc a b, 0 ≤ c t) (hdpos : ∀ t ∈ Icc a b, 0 ≤ d t)
    (hcstrict : ∀ t ∈ Ioo a b, 0 < c t)
    {p : C(Icc a b, ℝ) × C(Icc a b, ℝ)} (hp : IsVolterraPair hab c d 0 V₀ p)
    (hp0 : 0 ≤ p) (x : Icc a b) (hx : a < x) : 0 < p.1 x ∧ 0 < p.2 x := by
  have hl := volterraPair_lower_bounds hab hcpos hdpos hp hp0
  refine ⟨?_, hV.trans_le (hl x).2⟩
  rw [(hp x).1, zero_add]
  have hi := hc.mul_continuousOn (continuous_extendCurve hab p.2).continuousOn
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hi.mono_set (by
    rw [uIcc_of_le hx.le, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl x.property.2)) _ hx
  intro t ht
  exact mul_pos (hcstrict t ⟨ht.1, ht.2.trans_le x.property.2⟩)
    (hV.trans_le (hl (projIcc a b hab t)).2)

theorem volterraPair_hasDerivAt {c d : ℝ → ℝ} {X₀ V₀ : ℝ}
    (hc : IntervalIntegrable c volume a b) (hd : IntervalIntegrable d volume a b)
    (hcc : ContinuousOn c (Ioo a b)) (hdc : ContinuousOn d (Ioo a b))
    {p : C(Icc a b, ℝ) × C(Icc a b, ℝ)} (hp : IsVolterraPair hab c d X₀ V₀ p)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (extendCurve hab p.1) (c x * extendCurve hab p.2 x) x ∧
    HasDerivAt (extendCurve hab p.2) (d x * extendCurve hab p.1 x) x := by
  have heq₁ : extendCurve hab p.1 =ᶠ[𝓝 x]
      (fun y => X₀ + ∫ t in a..y, c t * extendCurve hab p.2 t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    simpa only [extendCurve, projIcc_of_mem hab ⟨ht.1.le, ht.2.le⟩] using
      (hp ⟨t, ⟨ht.1.le, ht.2.le⟩⟩).1
  have heq₂ : extendCurve hab p.2 =ᶠ[𝓝 x]
      (fun y => V₀ + ∫ t in a..y, d t * extendCurve hab p.1 t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    simpa only [extendCurve, projIcc_of_mem hab ⟨ht.1.le, ht.2.le⟩] using
      (hp ⟨t, ⟨ht.1.le, ht.2.le⟩⟩).2
  constructor
  · exact ((primitive_hasDerivAt_interior
      (hc.mul_continuousOn (continuous_extendCurve hab p.2).continuousOn)
      (hcc.mul (continuous_extendCurve hab p.2).continuousOn) hx).const_add X₀).congr_of_eventuallyEq heq₁
  · exact ((primitive_hasDerivAt_interior
      (hd.mul_continuousOn (continuous_extendCurve hab p.1).continuousOn)
      (hdc.mul (continuous_extendCurve hab p.1).continuousOn) hx).const_add V₀).congr_of_eventuallyEq heq₂

theorem volterraPair_terminal_remainder {c d : ℝ → ℝ} {X₀ V₀ : ℝ}
    (hc : IntervalIntegrable c volume a b)
    {p : C(Icc a b, ℝ) × C(Icc a b, ℝ)} (hp : IsVolterraPair hab c d X₀ V₀ p)
    (x : Icc a b) :
    ‖p.1 ⟨b, right_mem_Icc.2 hab⟩ - p.1 x‖ ≤
      (∫ t in (x : ℝ)..b, |c t|) * ‖p.2‖ := by
  have hi := hc.mul_continuousOn (continuous_extendCurve hab p.2).continuousOn
  have hleft : uIcc a (x : ℝ) ⊆ uIcc a b := by
    rw [uIcc_of_le x.property.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl x.property.2
  have hright : uIcc (x : ℝ) b ⊆ uIcc a b := by
    rw [uIcc_of_le x.property.2, uIcc_of_le hab]
    exact Icc_subset_Icc x.property.1 le_rfl
  rw [(hp ⟨b, right_mem_Icc.2 hab⟩).1, (hp x).1, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left hi (hi.mono_set hleft)]
  calc
    _ ≤ ∫ t in (x : ℝ)..b, |c t| * ‖p.2‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le x.property.2 _
        ((hc.abs.mul_const ‖p.2‖).mono_set hright)
      apply ae_of_all
      intro t _
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (p.2.norm_coe_le_norm (projIcc a b hab t))
        (abs_nonneg (c t))
    _ = _ := intervalIntegral.integral_mul_const _ _

end CauchyHorizon
