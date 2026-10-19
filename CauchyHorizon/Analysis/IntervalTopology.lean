import CauchyHorizon.Analysis.IntervalJoin

/-! Continuity of restriction and concatenation in the transverse L2 norm. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

variable {A a U W : ℝ} {E : Type*} [NormedAddCommGroup E]

theorem continuous_intervalTranslateLp (ha : 0 ≤ a) (haU : a + U ≤ A) :
    Continuous (intervalTranslateLp (E := E) ha haU) := by
  let T : Lp E 2 (volume.restrict (Icc 0 A)) →+ Lp E 2 (volume.restrict (Icc 0 U)) :=
    AddMonoidHom.mk' (intervalTranslateLp ha haU) (by
      intro f g
      apply Lp.ext
      filter_upwards [intervalTranslateLp_ae ha haU (f + g),
        intervalTranslateLp_ae ha haU f, intervalTranslateLp_ae ha haU g,
        intervalTranslate_ae ha haU (Lp.coeFn_add f g),
        Lp.coeFn_add (intervalTranslateLp ha haU f) (intervalTranslateLp ha haU g)]
        with t hfg hf hg ha hb
      simp only [hfg, hb, ha, Pi.add_apply, hf, hg])
  exact AddMonoidHomClass.continuous_of_bound T 1 (fun f => by
    change ‖intervalTranslateLp ha haU f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using intervalTranslateLp_norm_le ha haU f)

theorem intervalJoinLp_norm_le (hW : 0 ≤ W)
    (f : Lp E 2 (volume.restrict (Icc 0 U))) (g : Lp E 2 (volume.restrict (Icc 0 W))) :
    ‖intervalJoinLp hW f g‖ ≤ ‖f‖ + ‖g‖ := by
  classical
  let μ := volume.restrict (Icc 0 (U + W))
  have hs : Iic U ∩ Icc 0 (U + W) = Icc 0 U := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · intro ht
      exact ⟨ht.2.1, ht.1⟩
    · intro ht
      exact ⟨ht.2, ht.1, by linarith [ht.2]⟩
  have hm : μ.restrict (Iic U)ᶜ ≤ volume.restrict (Icc U (U + W)) := by
    rw [Measure.restrict_restrict measurableSet_Iic.compl]
    exact Measure.restrict_mono (show (Iic U)ᶜ ∩ Icc 0 (U + W) ⊆ Icc U (U + W) from
      fun t ht => ⟨(not_le.mp (show ¬ t ≤ U from ht.1)).le, ht.2.2⟩) le_rfl
  have hf : MemLp (fun t => f t) 2 (μ.restrict (Iic U)) := by
    simpa only [μ, Measure.restrict_restrict measurableSet_Iic, hs] using Lp.memLp f
  have hg := ((Lp.memLp g).comp_measurePreserving (intervalUntranslate_measure U W)).mono_measure hm
  have hfi := (memLp_indicator_iff_restrict measurableSet_Iic).2 hf
  have hgi := (memLp_indicator_iff_restrict measurableSet_Iic.compl).2 hg
  have he : (Iic U).piecewise (fun t => f t) (fun t => g (t - U)) =
      (Iic U).indicator (fun t => f t) + (Iic U)ᶜ.indicator (fun t => g (t - U)) := by
    funext t
    simp only [piecewise, indicator, mem_compl_iff, Pi.add_apply]
    split_ifs <;> simp_all
  have hb : eLpNorm ((Iic U).piecewise (fun t => f t) (fun t => g (t - U))) 2 μ ≤
      eLpNorm f 2 (volume.restrict (Icc 0 U)) + eLpNorm g 2 (volume.restrict (Icc 0 W)) := by
    rw [he]
    refine (eLpNorm_add_le hfi.1 hgi.1 (by norm_num)).trans ?_
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic,
      eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic.compl]
    apply add_le_add
    · simp only [μ, Measure.restrict_restrict measurableSet_Iic, hs, le_refl]
    · refine (eLpNorm_mono_measure _ hm).trans ?_
      exact (eLpNorm_comp_measurePreserving (Lp.memLp g).1 (intervalUntranslate_measure U W)).le
  rw [intervalJoinLp, Lp.norm_toLp, Lp.norm_def, Lp.norm_def]
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(Lp.memLp f).2.ne, (Lp.memLp g).2.ne⟩) hb).trans_eq
    (ENNReal.toReal_add (Lp.memLp f).2.ne (Lp.memLp g).2.ne)

theorem continuous_intervalJoinLp (hU : 0 ≤ U) (hW : 0 ≤ W) :
    Continuous (fun p : Lp E 2 (volume.restrict (Icc 0 U)) × Lp E 2 (volume.restrict (Icc 0 W)) =>
      intervalJoinLp hW p.1 p.2) := by
  let T : (Lp E 2 (volume.restrict (Icc 0 U)) × Lp E 2 (volume.restrict (Icc 0 W))) →+
      Lp E 2 (volume.restrict (Icc 0 (U + W))) :=
    AddMonoidHom.mk' (fun p => intervalJoinLp hW p.1 p.2)
      (fun p q => intervalJoinLp_add hU hW p.1 q.1 p.2 q.2)
  exact AddMonoidHomClass.continuous_of_bound T 2 (fun p =>
    (intervalJoinLp_norm_le hW p.1 p.2).trans (by linarith [norm_fst_le p, norm_snd_le p]))

end CauchyHorizon
