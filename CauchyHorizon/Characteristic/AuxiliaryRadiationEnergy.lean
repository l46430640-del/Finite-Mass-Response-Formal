import CauchyHorizon.Characteristic.AuxiliaryRadiusCharts
import CauchyHorizon.Characteristic.TransverseDifference

/-! Actual radius traces supply the source and moving endpoint of the transverse difference. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon

def AuxiliaryRadiationEstimate (B : Background) {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (x : WaveState U V) (gY g : ℝ → ℝ) (β Y L : ℝ) (l b₀ : Icc 0 V) (A : ℝ → ℝ) : Prop :=
  ∃ z w : C(Icc 0 V, Icc 0 U),
    (∀ b : Icc 0 V, b₀ ≤ b → z b = projIcc 0 U hU (gY b) ∧
      w b = projIcc 0 U hU (g ((b : ℝ) / (1 + β))) ∧ z b ≤ w b) ∧
    let C := Real.exp (2 + 1 / 16) * (L * (Y - B.inner)) ^ 2
    let M := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 V) U) (fun _ => hU) 0 B.innerRate 0 x
    (∫ t in (b₀ : ℝ)..V, ‖transverseRadiationRows B.innerRate x z w (projIcc 0 V hV t)‖ ^ 2) ≤
      2 * (C / ((B.inner / 2) * B.innerRate)) ^ 2 * (∫ t in (l : ℝ)..V, A t ^ 2) +
        2 * (C * (2 * Real.exp 2) / (4 * B.innerRate ^ 2 * (B.inner / 2) ^ 2)) ^ 2 *
          ∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2

set_option maxHeartbeats 1600000 in
theorem IsWaveIntegral.auxiliary_radiation_energy (B : Background) {U V T₀ β Y L S : ℝ}
    {h r : ℝ → ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR hp hf) x)
    (hβ : 0 ≤ β) (hY : B.inner < Y) (hL : 0 ≤ L)
    (l b₀ : Icc 0 V) (hstart : max (l : ℝ) T₀ ≤ (b₀ : ℝ) / (1 + β)) (hS : S ≤ b₀)
    (gY g A : ℝ → ℝ) (hgY : ContinuousOn gY (Ici (l : ℝ))) (hg : ContinuousOn g (Ici T₀))
    (hAc : ContinuousOn A (Ici (l : ℝ))) (hA0 : ∀ t ∈ Ici (l : ℝ), 0 ≤ A t)
    (hlevel : ∀ b : Icc 0 V, l ≤ b → x.1 (projIcc 0 U hU (gY b)) b 0 = Y) :
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    AuxiliaryRadiationCharts B hU x ν g T₀ β Y L S →
    (∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, l ≤ v →
      x.1 (projIcc 0 U hU u) v 0 = Y →
        Real.exp (B.innerRate * v) * |x.1 (projIcc 0 U hU u) v 0 * x.2.2 u v 1| ≤
          (-ν (projIcc 0 U hU u) v) * A v) →
      AuxiliaryRadiationEstimate B hU hV x gY g β Y L l b₀ A := by
  intro ν hcharts hsource
  have hα : 0 < 1 + β := by linarith only [hβ]
  have hα1 : 1 ≤ 1 + β := by linarith only [hβ]
  have hl₀ : l ≤ b₀ := ((le_max_left _ _).trans hstart).trans (div_le_self b₀.property.1 hα1)
  let z : C(Icc 0 V, Icc 0 U) := ⟨fun b => projIcc 0 U hU (gY (max (l : ℝ) b)),
    continuous_projIcc.comp (hgY.comp_continuous (by fun_prop)
      (fun b => show (l : ℝ) ≤ max (l : ℝ) b from le_max_left _ _))⟩
  let w : C(Icc 0 V, Icc 0 U) := ⟨fun b => projIcc 0 U hU (g (max T₀ ((b : ℝ) / (1 + β)))),
    continuous_projIcc.comp (hg.comp_continuous (by fun_prop)
      (fun b => show T₀ ≤ max T₀ ((b : ℝ) / (1 + β)) from le_max_left _ _))⟩
  let A₀ : C(Icc 0 V, ℝ) := ⟨fun b => A (max (l : ℝ) b),
    hAc.comp_continuous (by fun_prop) (fun b => show (l : ℝ) ≤ max (l : ℝ) b from le_max_left _ _)⟩
  have hz (b : Icc 0 V) (hb : b₀ ≤ b) : z b = projIcc 0 U hU (gY b) := by
    simp only [z, ContinuousMap.coe_mk, max_eq_right (show (l : ℝ) ≤ b from hl₀.trans hb)]
  have hw (b : Icc 0 V) (hb : b₀ ≤ b) : w b = projIcc 0 U hU (g ((b : ℝ) / (1 + β))) := by
    have ht : T₀ ≤ (b : ℝ) / (1 + β) := ((le_max_right _ _).trans hstart).trans
      (div_le_div_of_nonneg_right hb hα.le)
    simp only [w, ContinuousMap.coe_mk, max_eq_right ht]
  have hA₀ (v : Icc 0 V) (hv : l ≤ v) : A₀ v = A v := by
    simp only [A₀, ContinuousMap.coe_mk, max_eq_right (show (l : ℝ) ≤ v from hv)]
  have hleft (b : Icc 0 V) (hb : b₀ ≤ b) (z' : Icc 0 U) (hz' : x.1 z' b 0 = Y) : z' = z b := by
    have ha := hx.radial_strictAnti hx.choose rfl
      (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1 b
      (fun u => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u b).2.2.1)
    apply ha.injective
    change x.1 z' b 0 = x.1 (z b) b 0
    rw [hz', hz b hb, hlevel b (hl₀.trans hb)]
  have hzw (b : Icc 0 V) (hb : b₀ ≤ b) : z b ≤ w b := by
    obtain ⟨_hgw, z', _hz', hzw', hrow⟩ := hcharts b (hS.trans hb)
    obtain ⟨Q, hQz, _hQd, hQp⟩ := hrow z' le_rfl hzw'
    have hr := (hQp z' (by simp)).1
    rw [hQz, projIcc_of_mem hU z'.property] at hr
    rw [← hleft b hb z' hr, hw b hb]
    exact hzw'
  let Ly := L * (Y - B.inner)
  let Ld := Real.exp (2 + 1 / 16) * Ly
  have hLy : 0 ≤ Ly := mul_nonneg hL (sub_pos.2 hY).le
  have hLd : 0 ≤ Ld := mul_nonneg (Real.exp_pos _).le hLy
  have he := hx.transverse_radiation_difference_energy
    (k := B.innerRate) (ρ := B.inner / 2) (N := 2 * Real.exp 2) (L := Ld) (Lᵧ := Ly)
    hU hV hUR hp hf B.innerRate_pos (half_pos B.inner_pos) (by positivity) hLd hLy
    l b₀ hl₀ z w hzw A₀ (fun v => hA0 _ (show (l : ℝ) ≤ max (l : ℝ) v from le_max_left _ _))
  have hchart := he (by
    intro b hb u hzu huw
    obtain ⟨_hgw, z', _hz', hzw', hrow⟩ := hcharts b (hS.trans hb)
    obtain ⟨Q₀, hQ₀z, _hQ₀d, hQ₀p⟩ := hrow z' le_rfl hzw'
    have hr := (hQ₀p z' (by simp)).1
    rw [hQ₀z, projIcc_of_mem hU z'.property] at hr
    have heq := hleft b hb z' hr
    subst z'
    obtain ⟨Q, hQz, hQd, hQp⟩ := hrow u hzu.le (by rw [← hw b hb]; exact huw)
    let τ := fun t => Q (projIcc (z b : ℝ) u hzu.le t)
    have htime (t : ℝ) (ht : t ∈ Icc (z b : ℝ) u) : l ≤ τ t := by
      obtain ⟨a, _ha, hba, _hga, haτ, _hτb, _hτγ⟩ := (hQp t ht).2.2.2.2.2.2.1
      exact (((le_max_left _ _).trans hstart).trans
        (div_le_div_of_nonneg_right hb hα.le)).trans (hba.trans haτ.le)
    refine ⟨Q, hQz, htime u (right_mem_Icc.2 (show (z b : ℝ) ≤ u from hzu.le)),
      (fun t ht => (hQp t ht).2.2.2.2.2.2.1.choose_spec.2.2.2.2.1),
      (fun t ht => (hQp t ht).2.1), (fun t ht => ?_), hQd,
      (fun t ht v hv => ((hQp t ht).2.2.2.2.2.2.2 _ v le_rfl hv.1 hv.2).1),
      (fun t ht v hv => ?_), (fun t ht => ?_), ?_⟩
    · have hh := hQp t ht
      exact ⟨neg_le.1 hh.2.2.2.2.2.1, neg_pos.1 hh.2.2.2.2.1⟩
    · simpa only [neg_mul] using ((hQp t ht).2.2.2.2.2.2.2 _ v le_rfl hv.1 hv.2).2.1
    · have hh := hQp t ht
      have hτb : τ t ≤ b := hh.2.2.2.2.2.2.1.choose_spec.2.2.2.2.1
      have hd := (hh.2.2.2.2.2.2.2 _ b le_rfl hτb le_rfl).2.2
      have hd' := hd.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh.2.2.2.2.2.1 (Real.exp_pos (2 + 1 / 16)).le)
        (Real.exp_pos (-2 * B.innerRate * ((b : ℝ) - τ t))).le)
      simpa only [Ld, Ly, neg_mul] using hd'
    · filter_upwards [hsource] with t hs
      intro ht
      change Real.exp (B.innerRate * τ t) *
        |x.1 (projIcc 0 U hU t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
          (-ν (projIcc 0 U hU t) (τ t)) * A₀ (τ t)
      rw [hA₀ _ (htime t ht)]
      exact hs (τ t) (htime t ht) (hQp t ht).1)
  refine ⟨z, w, fun b hb => ⟨hz b hb, hw b hb, hzw b hb⟩, ?_⟩
  have hAi : (∫ t in (l : ℝ)..V, (A₀ (projIcc 0 V hV t)) ^ 2) = ∫ t in (l : ℝ)..V, A t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (l : ℝ) V := by simpa only [uIcc_of_le l.property.2] using ht
    have htV : t ∈ Icc 0 V := ⟨l.property.1.trans ht'.1, ht'.2⟩
    simp only [A₀, ContinuousMap.coe_mk, projIcc_of_mem hV htV, max_eq_right ht'.1]
  have hh := hchart.2
  rw [hAi] at hh
  simpa only [Ly, Ld, pow_two, mul_assoc] using hh

end CauchyHorizon
