import CauchyHorizon.Characteristic.AuxiliaryRadiationTail
import CauchyHorizon.Radial.InnerRadiationCoefficient

/-! Removing the inner cutoff on the original radiation curve. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CauchyHorizon

def RadiationGammaTransmissionTail (B : Background) {U : ℝ} (hU : 0 ≤ U)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (g P : ℕ → ℝ → ℝ)
    (β c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧ ∀ᶠ n in atTop,
    let F := fun t => radiationRow B.innerRate (X n) t
      (projIcc 0 U hU (g n (t / (1 + β)))) - c * P n t
    MemLp F 2 (volume.restrict (Ici T)) ∧ (∫ t in Ici T, F t ^ 2) < ε

set_option maxHeartbeats 800000 in
theorem radiation_gamma_transmission_tail (B : Background) (hm : B.criticalExponent < 1)
    {U Yr β L Ch T₀ Eprofile Etotal : ℝ} (hU : 0 ≤ U) (hYr : B.inner < Yr) (hβ : 0 ≤ β)
    (X : (n : ℕ) → (V : Ici (0 : ℝ)) → WaveState U V) (g P : ℕ → ℝ → ℝ)
    (hR : ∀ n, Continuous (radiationRow B.innerRate (X n)) ∧
      MemLp (radiationRow B.innerRate (X n)) 2 (volume.restrict (Ici 0)))
    (hg : ∀ n, ContinuousOn (g n) (Ici T₀))
    (hP : ∀ n, MemLp (P n) 2 (volume.restrict (Ici 0)))
    (hPE : ∀ n, (∫ t in Ici (0 : ℝ), P n t ^ 2) ≤ Eprofile)
    (hdata : ∀ Y : Ioo B.inner Yr,
      let cθ := extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - Y) * Ch
      let cζ := extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - Y) * Ch
      ∃ l S : ℝ, ∃ gY θ : ℕ → ℝ → ℝ, 0 ≤ l ∧
        (∀ n, MemLp (θ n) 2 (volume.restrict (Ici l))) ∧
        (∀ n t, l ≤ t → θ n t = radiationRow B.innerRate (X n) t (projIcc 0 U hU (gY n t))) ∧
        (∀ n t, max l T₀ ≤ t / (1 + β) → S ≤ t →
          projIcc 0 U hU (gY n t) ≤ projIcc 0 U hU (g n (t / (1 + β)))) ∧
        (∀ n, MemLp (fun t => θ n t - θ 0 t - cθ * P n t) 2 (volume.restrict (Ici l))) ∧
        Tendsto (fun n => ∫ t in Ici l, (θ n t - θ 0 t - cθ * P n t) ^ 2) atTop (𝓝 0) ∧
        AuxiliaryRadiationTail B hU X gY g β Y L l T₀ S (cζ ^ 2 * Eprofile) Etotal) :
    RadiationGammaTransmissionTail B hU X g P β (B.transmission hm * Ch) := by
  intro ε hε
  have hη : 0 < ε / 16 := by positivity
  obtain ⟨Y, hY, hYcap, hsmall⟩ := ((show ∀ᶠ Y : ℝ in 𝓝[>] B.inner, B.inner < Y from
    self_mem_nhdsWithin).and
    ((eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hYr)).and
      ((B.inner_transmission_error_tendsto hm L Ch Eprofile Etotal).eventually_lt_const hη))).exists
  obtain ⟨l, S, gY, θ, hl, hθ, htrace, horder, he, helim, htail⟩ := hdata ⟨Y, hY, hYcap⟩
  let cθ := extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - Y) * Ch
  let c := B.transmission hm * Ch
  let e := fun n t => θ n t - θ 0 t - cθ * P n t
  obtain ⟨T₁, hlT₁, hT₁⟩ := htail (ε / 16) hη
  have hzero : Tendsto (fun T : ℝ => ∫ t in Ici T, θ 0 t ^ 2) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 (hzero.eventually_lt_const hη)
  let l' := max T₁ T₂
  have hll' : l ≤ l' := hlT₁.trans (le_max_left _ _)
  have hl' : 0 ≤ l' := hl.trans hll'
  have hα : 0 < 1 + β := by linarith only [hβ]
  let T := max S ((1 + β) * max l' T₀)
  have hstart : max l' T₀ ≤ T / (1 + β) :=
    (le_div_iff₀ hα).2 (by simpa only [T, mul_comm] using (le_max_right S ((1 + β) * max l' T₀)))
  have hT : 0 ≤ T := (le_div_iff₀ hα).1 (hl'.trans ((le_max_left _ _).trans hstart)) |>
    (by simpa only [zero_mul] using ·)
  have hl'T : l' ≤ T := ((le_max_left _ _).trans hstart).trans
    (div_le_self hT (by linarith only [hβ]))
  have hlT : l ≤ T := hll'.trans hl'T
  have hsub : Ici T ⊆ Ici l := Ici_subset_Ici.2 hlT
  have hsub₀ : Ici T ⊆ Ici (0 : ℝ) := Ici_subset_Ici.2 hT
  let Γ := fun n t => radiationRow B.innerRate (X n) t (projIcc 0 U hU (g n (t / (1 + β))))
  have hΓ (n : ℕ) : MemLp (Γ n) 2 (volume.restrict (Ici T)) := by
    have hgc : ContinuousOn (fun t => projIcc 0 U hU (g n (t / (1 + β)))) (Ici T) :=
      continuous_projIcc.comp_continuousOn ((hg n).comp (by fun_prop) (fun t ht =>
        ((le_max_right _ _).trans hstart).trans (div_le_div_of_nonneg_right ht hα.le)))
    have hc : ContinuousOn (Γ n) (Ici T) := continuous_eval.comp_continuousOn
      ((hR n).1.continuousOn.prodMk hgc)
    apply ((hR n).2.mono_measure (Measure.restrict_mono hsub₀ le_rfl)).of_le_mul (c := 1)
      (hc.aestronglyMeasurable measurableSet_Ici)
    exact Eventually.of_forall (fun t => by simpa only [one_mul] using
      (radiationRow B.innerRate (X n) t).norm_coe_le_norm (projIcc 0 U hU (g n (t / (1 + β)))))
  have hPi (n : ℕ) : IntegrableOn (fun t => P n t ^ 2) (Ici 0) :=
    (memLp_two_iff_integrable_sq (hP n).1).1 (hP n)
  have hθi : IntegrableOn (fun t => θ 0 t ^ 2) (Ici l) :=
    (memLp_two_iff_integrable_sq (hθ 0).1).1 (hθ 0)
  have href : (∫ t in Ici T, θ 0 t ^ 2) < ε / 16 := hT₂ T ((le_max_right _ _).trans hl'T)
  have hmodel (n : ℕ) : (∫ t in Ici T, ((cθ - c) * P n t) ^ 2) ≤ (cθ - c) ^ 2 * Eprofile := by
    simp only [mul_pow, integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((setIntegral_mono_set (hPi n)
      (Eventually.of_forall (fun t => sq_nonneg _)) (Eventually.of_forall (fun _ ht => hsub₀ ht))).trans
      (hPE n)) (sq_nonneg _)
  refine ⟨T, hT, ?_⟩
  filter_upwards [hT₁ l' (le_max_left _ _), helim.eventually_lt_const hη] with n hn hen
  obtain ⟨D, hD, hiD, hED⟩ := hn T hstart (le_max_left _ _)
  have hiF := (hΓ n).sub (((hP n).mono_measure (Measure.restrict_mono hsub₀ le_rfl)).const_mul c)
  refine ⟨hiF, ?_⟩
  have hei : IntegrableOn (fun t => e n t ^ 2) (Ici l) :=
    (memLp_two_iff_integrable_sq (he n).1).1 (he n)
  have heT : (∫ t in Ici T, e n t ^ 2) < ε / 16 :=
    (setIntegral_mono_set hei (Eventually.of_forall (fun t => sq_nonneg _))
      (Eventually.of_forall (fun _ ht => hsub ht))).trans_lt hen
  have hiD₂ : IntegrableOn (fun t => ‖D t‖ ^ 2) (Ici T) :=
    (memLp_two_iff_integrable_sq_norm hiD.1).1 hiD
  have hie := hei.mono_set hsub
  have hiθ := hθi.mono_set hsub
  have hiP : IntegrableOn (fun t => ((cθ - c) * P n t) ^ 2) (Ici T) := by
    simpa only [mul_pow] using (show IntegrableOn (fun t => (cθ - c) ^ 2 * P n t ^ 2) (Ici T) volume from
      ((hPi n).mono_set hsub₀).const_mul ((cθ - c) ^ 2))
  have hiDe : IntegrableOn (fun t => ‖D t‖ ^ 2 + e n t ^ 2) (Ici T) := hiD₂.add hie
  have hiθP : IntegrableOn (fun t => θ 0 t ^ 2 + ((cθ - c) * P n t) ^ 2) (Ici T) := hiθ.add hiP
  have hbound := integral_mono_ae ((memLp_two_iff_integrable_sq hiF.1).1 hiF)
    ((hiDe.add hiθP).const_mul 4) (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      let w := projIcc 0 U hU (g n (t / (1 + β)))
      have hz := horder n t ((max_le_max hll' le_rfl).trans
        (hstart.trans (div_le_div_of_nonneg_right ht hα.le))) ((le_max_left _ _).trans ht)
      have hh := hD t ht w
      simp only [w, min_self, max_eq_right hz] at hh
      rw [← htrace n t (hlT.trans ht)] at hh
      have hid : Γ n t - c * P n t = (D t w + e n t) + (θ 0 t + (cθ - c) * P n t) := by
        rw [show D t w = Γ n t - θ n t from hh]
        dsimp only [e]
        ring
      have hd : (D t w) ^ 2 ≤ ‖D t‖ ^ 2 := by
        simpa only [Real.norm_eq_abs, sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) ((D t).norm_coe_le_norm w) 2
      change (Γ n t - c * P n t) ^ 2 ≤ 4 * ((‖D t‖ ^ 2 + e n t ^ 2) +
        (θ 0 t ^ 2 + ((cθ - c) * P n t) ^ 2))
      rw [hid]
      nlinarith only [hd, add_sq_le (a := D t w) (b := e n t),
        add_sq_le (a := θ 0 t) (b := (cθ - c) * P n t),
        add_sq_le (a := D t w + e n t) (b := θ 0 t + (cθ - c) * P n t)])
  change (∫ t in Ici T, (Γ n t - c * P n t) ^ 2) ≤
    ∫ t in Ici T, 4 * ((‖D t‖ ^ 2 + e n t ^ 2) + (θ 0 t ^ 2 + ((cθ - c) * P n t) ^ 2)) at hbound
  rw [integral_const_mul, integral_add hiDe hiθP, integral_add hiD₂ hie, integral_add hiθ hiP] at hbound
  dsimp only [Background.innerTransmissionError] at hsmall
  change (∫ t in Ici T, (Γ n t - c * P n t) ^ 2) < ε
  linarith only [hbound, hED, hsmall, heT, href, hmodel n]

end CauchyHorizon
