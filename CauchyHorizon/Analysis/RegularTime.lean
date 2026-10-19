import CauchyHorizon.Analysis.TerminalIntegral
import CauchyHorizon.Analysis.ArrivalInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! An integrable positive lapse defines the regular time coordinate and its inverse. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

noncomputable def regularTime (a : ℝ → ℝ) (v : ℝ) : ℝ := -∫ w in Ioi v, a w

def IsRegularTimeCoordinate (a : ℝ → ℝ) (T : ℝ) (χ : ℝ → ℝ) : Prop :=
  Continuous a ∧ (∀ v, 0 < a v) ∧ (∀ v, IntegrableOn a (Ioi v)) ∧
    StrictMono (regularTime a) ∧ (∀ v, HasDerivAt (regularTime a) (a v) v) ∧
    (∀ v, regularTime a v < 0) ∧ Tendsto (regularTime a) atTop (𝓝[<] (0 : ℝ)) ∧
    regularTime a '' Ioi T = Ioo (regularTime a T) 0 ∧
    ContinuousOn χ (Ioo (regularTime a T) 0) ∧ Tendsto χ (𝓝[<] (0 : ℝ)) atTop ∧
    (∀ w ∈ Ioo (regularTime a T) 0,
      T < χ w ∧ regularTime a (χ w) = w ∧ HasDerivAt χ (1 / a (χ w)) w) ∧
    ∀ v ∈ Ioi T, χ (regularTime a v) = v

theorem exists_regular_time_coordinate {a : ℝ → ℝ} (hc : Continuous a)
    (hp : ∀ v, 0 < a v) (hi : ∀ v, IntegrableOn a (Ioi v)) (T : ℝ) :
    ∃ χ : ℝ → ℝ, IsRegularTimeCoordinate a T χ := by
  let g := fun v => ∫ w in Ioi v, a w
  have hd (v : ℝ) : HasDerivAt g (-a v) v := futureIntegral_hasDerivAt hc hi v
  have hg : StrictAnti g := strictAnti_of_hasDerivAt_neg hd (fun v => neg_neg_of_pos (hp v))
  have hgzero : Tendsto g atTop (𝓝 0) := by
    simpa only [id_eq] using (tendsto_integral_Ioi_zero (f := a) (μ := volume) tendsto_id)
  have hgnonneg (v : ℝ) : 0 ≤ g v :=
    le_of_tendsto hgzero ((eventually_ge_atTop v).mono (fun w hw => hg.antitone hw))
  have hgpos (v : ℝ) : 0 < g v := (hgnonneg (v + 1)).trans_lt (hg (lt_add_one v))
  have hgc : Continuous g := continuous_iff_continuousAt.2 (fun v => (hd v).continuousAt)
  obtain ⟨ι, hιc, hιtop, hιright, hιleft⟩ := exists_arrival_inverse_closed
    (hgc.continuousOn (s := Ici T)) (hg.strictAntiOn _) hgzero (fun v _ => hgpos v)
    (fun v _ => ⟨(hd v).differentiableAt, by rw [(hd v).deriv]; exact neg_neg_of_pos (hp v)⟩)
  let χ := fun w => ι (-w)
  have hmem {w : ℝ} (hw : w ∈ Ioo (regularTime a T) 0) : -w ∈ Ioo 0 (g T) := by
    change -g T < w ∧ w < 0 at hw
    constructor <;> linarith only [hw.1, hw.2]
  have hχc : ContinuousOn χ (Ioo (regularTime a T) 0) :=
    hιc.comp continuous_neg.continuousOn (fun _ hw => hmem hw)
  have hneg : Tendsto (fun w : ℝ => -w) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · simpa only [neg_zero] using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact neg_pos.2 (show w < 0 from hw)
  have hχtop : Tendsto χ (𝓝[<] (0 : ℝ)) atTop := hιtop.comp hneg
  have hVd (v : ℝ) : HasDerivAt (regularTime a) (a v) v := by
    change HasDerivAt (fun w => -g w) (a v) v
    simpa only [neg_neg] using (hd v).fun_neg
  have hVm : StrictMono (regularTime a) := strictMono_of_hasDerivAt_pos hVd hp
  have hVneg (v : ℝ) : regularTime a v < 0 := neg_neg_of_pos (hgpos v)
  have hVtop : Tendsto (regularTime a) atTop (𝓝[<] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, Eventually.of_forall hVneg⟩
    change Tendsto (fun w => -g w) atTop (𝓝 0)
    simpa only [neg_zero] using hgzero.neg
  have hχright (w : ℝ) (hw : w ∈ Ioo (regularTime a T) 0) :
      T < χ w ∧ regularTime a (χ w) = w ∧ HasDerivAt χ (1 / a (χ w)) w := by
    obtain ⟨hdom, hright, hderiv⟩ := hιright (-w) (hmem hw)
    refine ⟨hdom, ?_, ?_⟩
    · change -g (ι (-w)) = w
      rw [hright, neg_neg]
    · have hh := hderiv.comp w (hasDerivAt_id w).neg
      rw [(hd (ι (-w))).deriv] at hh
      simpa only [χ, Function.comp_def, neg_inv, neg_mul, mul_neg, mul_one, neg_neg, one_div] using hh
  refine ⟨χ, hc, hp, hi, hVm, hVd, hVneg, hVtop, ?_, hχc, hχtop, hχright, ?_⟩
  · ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hVm hv, hVneg v⟩
    · intro hw
      exact ⟨χ w, (hχright w hw).1, (hχright w hw).2.1⟩
  · intro v hv
    change ι (- -g v) = v
    rw [neg_neg]
    exact hιleft v hv

end CauchyHorizon
