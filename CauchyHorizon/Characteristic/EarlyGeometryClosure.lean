import CauchyHorizon.Characteristic.InnerMargin
import CauchyHorizon.Characteristic.InnerPotential
import CauchyHorizon.Characteristic.TrappedBarrier
import CauchyHorizon.Characteristic.EarlyInnerFeedback
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Joint geometric improvement from the actual mass flux and a trapped-radius barrier. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

theorem Background.exists_early_radius_mass_improvement (B : Background) {ε κ₀ c β : ℝ}
    (hε : 0 < ε) (hk : 0 < κ₀) (hc0 : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ B.inner / 4 ∧ δ ≤ (B.event - B.inner) / 2 ∧
      (∀ r ∈ Icc (B.inner - δ) (B.inner + δ), B.innerRate / 4 ≤ radialPotential r B.charge B.cosmological) ∧
      ∀ H C γ : ℝ, 0 ≤ H → 0 < γ →
        ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ Y : ℝ, B.inner < Y → Y ≤ B.inner + δ / 2 →
          ∀ {U V : ℝ} {h r : ℝ → ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
            (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
            (_hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
            (_hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
              (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
            {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
            {x : WaveState U V}
            (hx : IsWaveIntegral hU hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hf) x)
            (u : Icc 0 U) (a b : Icc 0 V), a ≤ b → T₀ ≤ a →
            x.1 u a 0 = Y → x.2.1 u a 0 < 0 → (b : ℝ) ≤ (1 + β) * a →
            (∀ v ∈ Icc a b, |x.2.1 u v 1| ≤ H * Real.exp (-c * v)) →
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
            let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
            |m u a - B.mass| ≤ C * Real.exp (-γ * a) →
            (∀ v ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
              |x.1 u b 0 - B.inner| ≤ δ / 2 ∧ |m u b - B.mass| ≤ δ / 2 ∧
                3 * B.inner / 4 ≤ x.1 u b 0 ∧
                  |horizonK (x.1 u b 0) (m u b) B.charge B.cosmological + B.innerRate| ≤ ε / 2 := by
  obtain ⟨δK, hδK, hδKr, hδKe, hmargin⟩ := B.exists_inner_K_margin hε
  obtain ⟨δP, hδP, hpotential⟩ := B.exists_positive_radial_potential
  let δ := min δK δP
  have hδ : 0 < δ := lt_min hδK hδP
  have hδr : δ ≤ B.inner / 4 := (min_le_left _ _).trans hδKr
  have hδe : δ ≤ (B.event - B.inner) / 2 := (min_le_left _ _).trans hδKe
  have hpot : ∀ r ∈ Icc (B.inner - δ) (B.inner + δ),
      B.innerRate / 4 ≤ radialPotential r B.charge B.cosmological := by
    intro r hr
    exact hpotential r ⟨by linarith only [hr.1, min_le_right δK δP],
      by linarith only [hr.2, min_le_right δK δP]⟩
  let ρ := B.inner - δ / 2
  have hρ : 0 < ρ := by dsimp only [ρ]; linarith only [hδr, B.inner_pos]
  have hρi : ρ < B.inner := by dsimp only [ρ]; linarith only [hδ]
  have hF : 0 < B.F ρ := by
    rw [B.factorization hρ.ne']
    have h₁ : ρ - B.inner < 0 := sub_neg.2 hρi
    have h₂ : ρ - B.event < 0 := sub_neg.2 (hρi.trans B.inner_lt_event)
    have h₃ : ρ - B.cosmologicalRadius < 0 := sub_neg.2 (hρi.trans (B.inner_lt_event.trans B.event_lt_cosmological))
    have h₄ : 0 < ρ - B.negativeRoot := sub_pos.2 (B.negativeRoot_neg.trans hρ)
    exact div_pos (mul_pos (mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (neg_neg_of_pos B.cosmological_pos) h₁) h₂) h₃) h₄) (by positivity)
  let μ := min (δ / 2) (ρ * B.F ρ / 4)
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  refine ⟨δ, hδ, hδr, hδe, hpot, ?_⟩
  intro H C γ hH hγ
  let P := B.event ^ 2 * H ^ 2 / (2 * κ₀)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hmlim : Tendsto (fun t : ℝ => C * Real.exp (-γ * t) + (P * β) * (t * Real.exp (-(2 * c) * t)))
      atTop (𝓝 0) := by
    have h₁ : Tendsto (fun t : ℝ => C * Real.exp (-γ * t)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, id_eq, mul_zero] using
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hγ))).const_mul C
    have h₂ : Tendsto (fun t : ℝ => (P * β) * (t * Real.exp (-(2 * c) * t))) atTop (𝓝 0) := by
      simpa only [Real.rpow_one, mul_zero] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 * c) (by positivity)).const_mul (P * β)
    simpa only [add_zero] using h₁.add h₂
  obtain ⟨T₀, hlate⟩ := eventually_atTop.1 (hmlim.eventually_lt_const hμ)
  refine ⟨max 0 T₀, le_max_left _ _, ?_⟩
  intro Y hY hYδ U V h r hU hV hUR hc hi hrc hr0 hφ hrd p hp f hf x hx u a b hab hTa
    hra ha hwindow hscalar
  dsimp only
  intro hm hkappa
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
  have hRa : x.1 u a 0 ≤ B.event := by rw [hra]; linarith only [hYδ, hδe, B.inner_lt_event.le]
  have hmass := hx.trapped_mass_increment_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf
    hk hH hc0.le u a b hab ha hRa hscalar hkappa
  have hlength : (b : ℝ) - a ≤ β * a := by nlinarith only [hwindow]
  have hinc : m u b - m u a ≤ (P * β) * ((a : ℝ) * Real.exp (-(2 * c) * a)) := by
    apply hmass.2.trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength hP)
      (Real.exp_pos (-(2 * c) * a)).le
    exact hh.trans_eq (by ring)
  have hmb : |m u b - B.mass| ≤ μ := by
    calc
      _ = |(m u a - B.mass) + (m u b - m u a)| := by congr 1; ring
      _ ≤ |m u a - B.mass| + |m u b - m u a| := abs_add_le _ _
      _ = |m u a - B.mass| + (m u b - m u a) := by rw [abs_of_nonneg hmass.1]
      _ ≤ C * Real.exp (-γ * a) + (P * β) * ((a : ℝ) * Real.exp (-(2 * c) * a)) := add_le_add hm hinc
      _ ≤ _ := (hlate a ((le_max_right _ _).trans hTa)).le
  have hmlow := hmb.trans (min_le_left _ _)
  have hrlo := hx.trapped_radius_barrier B hρ hF hU hV hUR hc hi hrc hr0 hφ hrd hp hf
    u a b hab ha (by rw [hra]; exact hρi.le.trans hY.le)
    (by have hh := (abs_le.1 hmb).2.trans (min_le_right _ _); linarith only [hh])
  have hrhi := (hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha).2
  have hrad : |x.1 u b 0 - B.inner| ≤ δ / 2 := by
    rw [hra] at hrhi
    apply abs_le.2
    dsimp only [ρ] at hrlo
    constructor <;> linarith only [hrlo, hrhi, hYδ]
  exact ⟨hrad, hmlow, hmargin (x.1 u b 0) (m u b)
    (hrad.trans ((half_le_self hδ.le).trans (min_le_left _ _)))
    (hmlow.trans ((half_le_self hδ.le).trans (min_le_left _ _)))⟩

end CauchyHorizon
