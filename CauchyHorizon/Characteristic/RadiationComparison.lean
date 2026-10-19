import CauchyHorizon.Characteristic.LateRadiationHalfline
import CauchyHorizon.Characteristic.GammaTransmissionTail
import CauchyHorizon.Analysis.HistoryTail

/-! The actual compact-ray radiation limit from gamma transmission and finite histories. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

noncomputable def radiationComparisonRow {U ε : ℝ} (hε : 0 ≤ ε) (k c : ℝ)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (P : ℕ → ℝ → ℝ)
    (n : ℕ) (t : ℝ) : C(Icc ε U, ℝ) :=
  let J : C(Icc ε U, Icc (0 : ℝ) U) :=
    ⟨fun u => ⟨u, hε.trans u.property.1, u.property.2⟩, by fun_prop⟩
  (radiationRow k (X n) t).comp J - (radiationRow k (X 0) t).comp J -
    ContinuousMap.const _ (c * P n t)

set_option maxHeartbeats 1400000 in
theorem radiation_comparison (B : Background) {U ε β T₀ q Ed Dg c : ℝ}
    (hU : 0 ≤ U) (hε : 0 < ε) (hβ : 0 ≤ β) (hq : 0 < q)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (g P : ℕ → ℝ → ℝ)
    (hcompat : ∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X n T) = X n S)
    (hR : ∀ n, MemLp (radiationRow B.innerRate (X n)) 2 (volume.restrict (Ici 0)))
    (hP : ∀ n, Continuous (P n) ∧ MemLp (P n) 2 (volume.restrict (Ici 0)))
    (hscale : ∀ n t, T₀ ≤ t → g n t * Real.exp (B.outerRate * t) ≤ Dg)
    (hD : ∀ n, LateRadiationHalfline hU B.innerRate β T₀ q Ed (X n) (g n))
    (hΓ : RadiationGammaTransmissionTail B hU X g P β c)
    (hhistory : ∀ V : Ici (0 : ℝ), Tendsto (fun n => X n V) atTop (𝓝 (X 0 V)))
    (hvanish : ∀ S : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) S, P n t = 0) :
    (∀ n, MemLp (radiationComparisonRow hε.le B.innerRate c X P n) 2 (volume.restrict (Ici 0))) ∧
      Tendsto (fun n => ∫ t in Ici (0 : ℝ), ‖radiationComparisonRow hε.le B.innerRate c X P n t‖ ^ 2)
        atTop (𝓝 0) := by
  let J : C(Icc ε U, Icc (0 : ℝ) U) :=
    ⟨fun u => ⟨u, hε.le.trans u.property.1, u.property.2⟩, by fun_prop⟩
  let R := fun n => radiationRow B.innerRate (X n)
  let F := radiationComparisonRow hε.le B.innerRate c X P
  have hRc (n : ℕ) : Continuous (R n) := continuous_radiationRow (X n) (hcompat n)
  have hFc (n : ℕ) : Continuous (F n) :=
    (((ContinuousMap.compCLM ℝ ℝ J).continuous.comp (hRc n)).sub
      ((ContinuousMap.compCLM ℝ ℝ J).continuous.comp (hRc 0))).sub
        ((ContinuousLinearMap.const ℝ (Icc ε U) : ℝ →L[ℝ] C(Icc ε U, ℝ)).continuous.comp
          ((hP n).1.const_mul c))
  have hFi (n : ℕ) : MemLp (F n) 2 (volume.restrict (Ici 0)) :=
    (((ContinuousMap.compCLM ℝ ℝ J).comp_memLp' (hR n)).sub
      ((ContinuousMap.compCLM ℝ ℝ J).comp_memLp' (hR 0))).sub
        ((ContinuousLinearMap.const ℝ (Icc ε U) : ℝ →L[ℝ] C(Icc ε U, ℝ)).comp_memLp'
          ((hP n).2.const_mul c))
  have hFii (n : ℕ) : IntegrableOn (fun t => ‖F n t‖ ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq_norm (hFi n).1).1 (hFi n)
  have hHist (S : ℝ) (hS : 0 ≤ S) :
      Tendsto (fun n => ∫ t in (0 : ℝ)..S, ‖F n t‖ ^ 2) atTop (𝓝 0) := by
    let V : Ici (0 : ℝ) := ⟨S, hS⟩
    let Q : C(WaveState U S, C(Icc (0 : ℝ) S, C(Icc ε U, ℝ))) :=
      (⟨fun w : (WaveState U S × Icc (0 : ℝ) S) × Icc ε U =>
        Real.exp (B.innerRate * w.1.2) *
          (w.1.1.1 (J w.2) w.1.2 0 * w.1.1.2.1 (J w.2) w.1.2 1), by
          have hr : Continuous (fun w : (WaveState U S × Icc (0 : ℝ) S) × Icc ε U =>
              w.1.1.1 (J w.2) w.1.2) :=
            (continuous_fst.fst.fst.eval (J.continuous.comp continuous_snd)).eval continuous_fst.snd
          have hv : Continuous (fun w : (WaveState U S × Icc (0 : ℝ) S) × Icc ε U =>
              w.1.1.2.1 (J w.2) w.1.2) :=
            (continuous_fst.fst.snd.fst.eval (J.continuous.comp continuous_snd)).eval continuous_fst.snd
          have he : Continuous (fun w : (WaveState U S × Icc (0 : ℝ) S) × Icc ε U =>
              Real.exp (B.innerRate * w.1.2)) := by fun_prop
          exact he.mul (((continuous_apply (0 : Fin 3)).comp hr).mul
            ((continuous_apply (1 : Fin 3)).comp hv))⟩ :
        C((WaveState U S × Icc (0 : ℝ) S) × Icc ε U, ℝ)).curry.curry
    have hlim : Tendsto (fun n => S * ‖Q (X n V) - Q (X 0 V)‖ ^ 2) atTop (𝓝 0) := by
      have hc : Tendsto (fun n => Q (X n V)) atTop (𝓝 (Q (X 0 V))) :=
        (Q.continuous.tendsto (X 0 V)).comp (hhistory V)
      have hn : Tendsto (fun n => ‖Q (X n V) - Q (X 0 V)‖) atTop (𝓝 0) := by
        exact (tendsto_iff_norm_sub_tendsto_zero
          (f := fun n => Q (X n V)) (b := Q (X 0 V))).1 hc
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using (hn.pow 2).const_mul S
    apply squeeze_zero' (Eventually.of_forall (fun _ =>
      intervalIntegral.integral_nonneg hS (fun _ _ => sq_nonneg _))) _ hlim
    filter_upwards [hvanish S] with n hn
    calc
      _ ≤ ∫ _t in (0 : ℝ)..S, ‖Q (X n V) - Q (X 0 V)‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on hS ((hFc n).norm.pow 2 |>.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        intro t ht
        have heq : F n t = (Q (X n V) - Q (X 0 V)) ⟨t, ht⟩ := by
          ext u
          simp only [F, radiationComparisonRow, ContinuousMap.sub_apply, ContinuousMap.comp_apply,
            ContinuousMap.const_apply, hn t ht, mul_zero, sub_zero,
            radiationRow_eq (X n) (hcompat n) V ht.2, radiationRow_eq (X 0) (hcompat 0) V ht.2,
            Q, spatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
            V, projIcc_of_mem hS ht, zero_mul, sub_zero]
          rfl
        change ‖F n t‖ ^ 2 ≤ _
        rw [heq]
        exact pow_le_pow_left₀ (norm_nonneg _) ((Q (X n V) - Q (X 0 V)).norm_coe_le_norm _) 2
      _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  choose D hDeq hDweight hDE hDtail using hD
  have hα : 0 < 1 + β := by linarith only [hβ]
  have hentry : ∃ T : ℝ, 0 ≤ T ∧ ∀ n t, T ≤ t →
      T₀ ≤ t / (1 + β) ∧ g n (t / (1 + β)) ≤ ε := by
    have hl : Tendsto (fun t : ℝ => Dg * Real.exp (-(B.outerRate / (1 + β)) * t)) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_apply, id_eq] using
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
          (neg_neg_of_pos (div_pos B.outerRate_pos hα)))).const_mul Dg
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hl.eventually_lt_const hε)
    let S := max 0 (max T ((1 + β) * T₀))
    refine ⟨S, le_max_left _ _, ?_⟩
    intro n t ht
    have hbase : (1 + β) * T₀ ≤ S :=
      (le_max_right T ((1 + β) * T₀)).trans (le_max_right 0 (max T ((1 + β) * T₀)))
    have htime : T₀ ≤ t / (1 + β) := (le_div_iff₀ hα).2 (by
      simpa only [mul_comm] using hbase.trans ht)
    refine ⟨htime, ?_⟩
    have hh := mul_le_mul_of_nonneg_right (hscale n _ htime)
      (Real.exp_pos (-(B.outerRate / (1 + β)) * t)).le
    have he : Real.exp (B.outerRate * (t / (1 + β))) *
        Real.exp (-(B.outerRate / (1 + β)) * t) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      congr 1
      ring
    rw [mul_assoc, he, mul_one] at hh
    exact hh.trans (hT t (((le_max_left _ _).trans (le_max_right _ _)).trans ht)).le
  have htail : ∀ η : ℝ, 0 < η → ∃ T : ℝ, ∀ S : ℝ, T ≤ S →
      ∀ᶠ n in atTop, (∫ t in Ici S, ‖F n t‖ ^ 2) < η := by
    intro η hη
    have heps : 0 < η / 16 := by positivity
    obtain ⟨Tγ, hTγ, hγ⟩ := hΓ (η / 16) heps
    obtain ⟨Te, hTe, hentry⟩ := hentry
    have hdec : Tendsto (fun t : ℝ => Real.exp (-(2 * q) * t) * Ed) atTop (𝓝 0) := by
      simpa only [zero_mul, Function.comp_apply, id_eq] using (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos (by positivity : 0 < 2 * q)))).mul_const Ed
    obtain ⟨Td, hTd⟩ := eventually_atTop.1 (hdec.eventually_lt_const heps)
    have href : Tendsto (fun S : ℝ => ∫ t in Ici S, ‖R 0 t‖ ^ 2) atTop (𝓝 0) :=
      tendsto_integral_Ici_zero tendsto_id
    obtain ⟨Tr, hTr⟩ := eventually_atTop.1 (href.eventually_lt_const heps)
    refine ⟨max Tγ (max Te (max Td Tr)), ?_⟩
    intro S hS
    have hγS : Tγ ≤ S := (le_max_left _ _).trans hS
    have heS : Te ≤ S := ((le_max_left _ _).trans (le_max_right _ _)).trans hS
    have hdS : Td ≤ S := ((le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))).trans hS
    have hrS : Tr ≤ S := ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))).trans hS
    have hS0 : 0 ≤ S := hTe.trans heS
    have hsub : Ici S ⊆ Ici (0 : ℝ) := Ici_subset_Ici.2 hS0
    filter_upwards [hγ] with n hn
    let G := fun t => R n t (projIcc 0 U hU (g n (t / (1 + β)))) - c * P n t
    have hGi : IntegrableOn (fun t => G t ^ 2) (Ici Tγ) :=
      (memLp_two_iff_integrable_sq hn.1.1).1 hn.1
    have hGS : (∫ t in Ici S, G t ^ 2) < η / 16 :=
      (setIntegral_mono_set hGi (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall (fun _ ht => hγS.trans ht))).trans_lt hn.2
    have hDi : IntegrableOn (fun t => ‖D n t‖ ^ 2) (Ici S) :=
      (memLp_two_iff_integrable_sq_norm (hDtail n S hS0).1.1).1 (hDtail n S hS0).1
    have hRi : IntegrableOn (fun t => ‖R 0 t‖ ^ 2) (Ici S) :=
      IntegrableOn.mono_set ((memLp_two_iff_integrable_sq_norm (hR 0).1).1 (hR 0)) hsub
    have hGt := hGi.mono_set (Ici_subset_Ici.2 hγS)
    have hnorm (t : ℝ) (ht : S ≤ t) : ‖F n t‖ ≤ ‖D n t‖ + ‖G t‖ + ‖R 0 t‖ := by
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro u
      have he := hentry n t (heS.trans ht)
      have hzu : projIcc 0 U hU (g n (t / (1 + β))) ≤ J u := by
        change (projIcc 0 U hU (g n (t / (1 + β))) : ℝ) ≤ (u : ℝ)
        rw [coe_projIcc]
        exact max_le (hε.le.trans u.property.1) ((min_le_right _ _).trans (he.2.trans u.property.1))
      have hpt := hDeq n t (J u)
      simp only [max_eq_right he.1, max_eq_right hzu] at hpt
      have hid : F n t u = D n t (J u) + G t - R 0 t (J u) := by
        rw [hpt]
        change R n t (J u) - R 0 t (J u) - c * P n t = _
        dsimp only [G]
        ring
      rw [hid]
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((D n t).norm_coe_le_norm _) le_rfl))
        ((R 0 t).norm_coe_le_norm _))
    have hDG : IntegrableOn (fun t => ‖D n t‖ ^ 2 + G t ^ 2) (Ici S) := hDi.add hGt
    have hsum := hDG.add hRi
    have hb := integral_mono_ae ((hFii n).mono_set hsub) (hsum.const_mul 4) (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hnorm t ht)
      have hGsq : ‖G t‖ ^ 2 = G t ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      change ‖F n t‖ ^ 2 ≤ 4 * ((‖D n t‖ ^ 2 + G t ^ 2) + ‖R 0 t‖ ^ 2)
      nlinarith only [hh, hGsq, add_sq_le (a := ‖D n t‖) (b := ‖G t‖),
        add_sq_le (a := ‖D n t‖ + ‖G t‖) (b := ‖R 0 t‖), sq_nonneg ‖R 0 t‖])
    change (∫ t in Ici S, ‖F n t‖ ^ 2) ≤
      ∫ t in Ici S, 4 * ((‖D n t‖ ^ 2 + G t ^ 2) + ‖R 0 t‖ ^ 2) at hb
    rw [integral_const_mul, integral_add hDG hRi, integral_add hDi hGt] at hb
    have hDS := (hDtail n S hS0).2.trans_lt (hTd S hdS)
    linarith only [hb, hDS, hGS, hTr S hrS, hη]
  refine ⟨hFi, ?_⟩
  have hh := pair_energy_tendsto_of_history_tail (F := fun n t => ‖F n t‖) (G := fun _ _ => 0)
    (F₀ := fun _ => 0) (G₀ := fun _ => 0) (fun n => (hFi n).norm) (fun _ => MemLp.zero)
    MemLp.zero MemLp.zero (by simpa only [sub_zero, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
      using hHist) (by simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using htail)
  simpa only [sub_zero, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero] using hh

end CauchyHorizon
