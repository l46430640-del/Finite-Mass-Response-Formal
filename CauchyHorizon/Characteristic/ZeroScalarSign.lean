import CauchyHorizon.Reduced.ScalarSign
import CauchyHorizon.Characteristic.ZeroScalar
import CauchyHorizon.Characteristic.OuterTrapping

/-! The positive outgoing tail keeps the actual reference scalar positive in the outer prefix. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 600000 in
theorem exists_zero_outer_scalar_positive (B : Background) {s l c H Hlo dH : ℝ} {h r : ℝ → ℝ}
    (hs : 0 < s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s)
    (hl : l < 2 * s + c) (hH : 0 ≤ H) (hHlo : 0 < Hlo)
    (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hlo : ∀ t ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * t) ≤ h t)
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ W : ℝ, 0 < δ ∧ 0 < W ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p)
        (hf : MemLp (fun _ : ℝ => (0 : ℝ)) p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        U ≤ W → U * Real.exp (B.outerRate * V) ≤ δ →
          (∀ u v, scalarPositiveLambdaCorrection hU hV x.1 x.2.1
            (radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose) u v < h v) ∧
          (∀ u v, 0 < x.1 u v 0 * x.2.1 u v 1) ∧
          ∀ u (v : Icc 0 V), 0 < (v : ℝ) → 0 < scalarTransportCorrection hV
            (radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose) x.2.1 u v := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let ρ := (B.event - dH) / 2
  have hρ : 0 < ρ := half_pos (sub_pos.2 hdHR)
  obtain ⟨δ₀, n, N, L, q, K, T₀, hδ₀, _hδr, hn, hN, hL, hq, hK, hT₀, hsolve⟩ :=
    B.exists_outer_flux_prefix hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut
      (c := 0) le_rfl B.outerRate_pos hs.le (A := 0) le_rfl
  let δ := min δ₀ (ρ / N)
  have hδ : 0 < δ := lt_min hδ₀ (div_pos hρ hN)
  have hδN : N * δ ≤ ρ := by
    have hh := (le_div_iff₀ hN).1 (min_le_right δ₀ (ρ / N))
    simpa only [mul_comm] using hh
  let E := H / ρ * Real.exp (L * N * δ / (ρ ^ 2 * (a - c)))
  let S := N * E / (a - c)
  let Cearly := L * S / ρ
  let Clate := δ * K * S / ρ ^ 2
  have hac : 0 < a - c := sub_pos.2 hca
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hS : 0 ≤ S := div_nonneg (mul_nonneg hN.le hE) hac.le
  have hCe : 0 ≤ Cearly := div_nonneg (mul_nonneg hL hS) hρ.le
  have hCl : 0 ≤ Clate := by dsimp only [Clate]; positivity
  have htail : Tendsto (fun t : ℝ => Clate * Real.exp (-(2 * s + c - l) * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq, mul_zero] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (neg_neg_of_pos (sub_pos.2 hl)))).const_mul Clate
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (htail.eventually_lt_const hHlo)
  let T := max T₀ T₁
  have hT : 0 ≤ T := hT₀.trans (le_max_left _ _)
  let Chead := Cearly * Real.exp ((a - c + |l|) * T)
  have hCh : 0 ≤ Chead := mul_nonneg hCe (Real.exp_pos _).le
  let W := Hlo / (2 * (Chead + 1))
  have hW : 0 < W := div_pos hHlo (by positivity)
  refine ⟨δ, W, hδ, hW, ?_⟩
  intro U V hU hV hUR p hp hf x hx hUW hwidth
  have hbudget : (eLpNorm (fun _ : ℝ => (0 : ℝ)) p (volume.restrict (Icc 0 U))).toReal ≤ 0 := by simp
  have hpR : 0 ≤ a * (1 - 1 / p.toReal) := by
    by_cases hpt : p = ∞
    · subst p; simp only [ENNReal.toReal_top, div_zero, sub_zero, mul_one]; exact ha.le
    · have hp4 : (4 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp
      exact mul_nonneg ha.le (sub_nonneg.2 ((div_le_one (by linarith : 0 < p.toReal)).2 (by linarith)))
  obtain ⟨y, ⟨hy, hg⟩, _⟩ := hsolve U V hU hV hUR p hp _ hf hbudget hpR
    (hwidth.trans (min_le_left _ _))
  have he := hy.incoming_unique hU hV hUR hp hf hx
  subst y
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hw (u : Icc 0 U) (v : Icc 0 V) : (u : ℝ) * Real.exp (a * v) ≤ δ :=
    (mul_le_mul u.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 ha.le))
      (Real.exp_pos _).le hU).trans hwidth
  have hfloor (u : Icc 0 U) (v : Icc 0 V) : ρ ≤ x.1 u v 0 := by
    obtain ⟨_, _, _, _, _, _, hgap, _⟩ := hg u v
    have hh := hgap.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hw u v) hN.le)
    have hb := hrb v
    dsimp only [ρ] at *
    linarith only [hh, hδN, hb]
  have hr (u : Icc 0 U) (v : Icc 0 V) : 0 < x.1 u v 0 := hρ.trans_le (hfloor u v)
  have hnneg (u : Icc 0 U) (v : Icc 0 V) : ν u v < 0 := by
    have hh := (hg u v).1
    have hhpos := mul_pos hn (Real.exp_pos (a * v))
    change n * Real.exp (a * v) ≤ -ν u v at hh
    linarith only [hh, hhpos]
  have hnhi (u : Icc 0 U) (v : Icc 0 V) : |ν u v| ≤ N * Real.exp (a * v) := by
    rw [abs_of_neg (hnneg u v)]
    exact (hg u v).2.1
  have hlam (u : Icc 0 U) (v : Icc 0 V) : |x.2.1 u v 0| ≤ L := (hg u v).2.2.1
  have hout (v : Icc 0 V) : Real.exp (c * v) * |h v| ≤ H := by
    have hh := mul_le_mul_of_nonneg_left (hb v) (Real.exp_pos (c * v)).le
    rw [Real.norm_eq_abs] at hh
    have he : Real.exp (c * v) * Real.exp (-s * v) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith only [mul_nonneg (sub_nonneg.2 hcs) v.property.1]
    nlinarith only [hh, mul_le_mul_of_nonneg_left he hH]
  have hscalar := hx.horizon_zero_weighted_scalar hU hV hUR hc hi hrc hr0 hφ hrd hp hf
    hc0 hca hρ hN.le hL hH hfloor hnhi hlam hout hwidth
  have hsource (u : Icc 0 U) (v : Icc 0 V) :
      |scalarTransportCorrection hV ν x.2.1 u v| ≤ S * Real.exp ((a - c) * v) := hscalar.2 u v
  have hcorr (u : Icc 0 U) (v : Icc 0 V) (M : ℝ) (hM : 0 ≤ M)
      (hm : ∀ w, max (x.2.1 w v 0) 0 ≤ M) :
      scalarPositiveLambdaCorrection hU hV x.1 x.2.1 ν u v ≤
        (u : ℝ) * (M * (S * Real.exp ((a - c) * v)) / ρ) := by
    let G := fun t : ℝ => max (x.2.1 (projIcc 0 U hU t) v 0) 0 *
      |scalarTransportCorrection hV ν x.2.1 (projIcc 0 U hU t) v| / x.1 (projIcc 0 U hU t) v 0
    have hrc' : Continuous (fun t => x.1 (projIcc 0 U hU t) v 0) :=
      ((continuous_apply 0).comp ((continuous_eval_const v).comp x.1.continuous)).comp continuous_projIcc
    have hlc : Continuous (fun t => x.2.1 (projIcc 0 U hU t) v 0) :=
      ((continuous_apply 0).comp ((continuous_eval_const v).comp x.2.1.continuous)).comp continuous_projIcc
    have hsc : Continuous (fun t => scalarTransportCorrection hV ν x.2.1 (projIcc 0 U hU t) v) :=
      ((continuous_eval_const v).comp (scalarTransportCorrection hV ν x.2.1).continuous).comp continuous_projIcc
    have hnc : Continuous (fun t => max (x.2.1 (projIcc 0 U hU t) v 0) 0 *
      |scalarTransportCorrection hV ν x.2.1 (projIcc 0 U hU t) v|) := (hlc.max continuous_const).mul hsc.abs
    have hGc : Continuous G := hnc.div hrc' (fun _ => (hr _ _).ne')
    have hh := intervalIntegral.integral_mono_on (μ := volume) u.property.1
      (f := G) (g := fun _ => M * (S * Real.exp ((a - c) * v)) / ρ)
      (hGc.intervalIntegrable _ _) intervalIntegrable_const (by
        intro t _ht
        let w := projIcc 0 U hU t
        exact (div_le_div_of_nonneg_left
          (mul_nonneg (le_max_right _ _) (abs_nonneg _)) hρ (hfloor w v)).trans
            (div_le_div_of_nonneg_right
              (mul_le_mul (hm w) (hsource w v) (abs_nonneg _) hM) hρ.le))
    simpa only [scalarPositiveLambdaCorrection, G, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul] using hh
  have hbad (u : Icc 0 U) (v : Icc 0 V) :
      scalarPositiveLambdaCorrection hU hV x.1 x.2.1 ν u v < h v := by
    have hlow : Hlo ≤ h v * Real.exp (l * v) := by
      have hh := mul_le_mul_of_nonneg_right (hlo v v.property.1) (Real.exp_pos (l * v)).le
      simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] using hh
    suffices hh : scalarPositiveLambdaCorrection hU hV x.1 x.2.1 ν u v * Real.exp (l * v) < Hlo by
      exact lt_of_mul_lt_mul_right (hh.trans_le hlow) (Real.exp_pos _).le
    by_cases hv : T ≤ (v : ℝ)
    · have hmax (w : Icc 0 U) : max (x.2.1 w v 0) 0 ≤ K / ρ * Real.exp (-(2 * s) * v) := by
        have hf := (hg w v).2.2.2.2.2.2.2 ((le_max_left _ _).trans hv)
        have hq0 := mul_nonneg (mul_nonneg hq.le w.property.1) (Real.exp_pos (a * v)).le
        have hf' : x.1 w v 0 * x.2.1 w v 0 ≤ K * Real.exp (-(2 * s) * v) := by linarith only [hf, hq0]
        apply max_le _ (by positivity)
        by_cases hz : x.2.1 w v 0 ≤ 0
        · exact hz.trans (by positivity)
        have hp := mul_le_mul_of_nonneg_right (hfloor w v) (lt_of_not_ge hz).le
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hρ).2
        simpa only [div_mul_eq_mul_div, mul_comm] using hp.trans hf'
      have hh := mul_le_mul_of_nonneg_right (hcorr u v _ (by positivity) hmax) (Real.exp_pos (l * v)).le
      have he : Real.exp (-(2 * s) * v) * Real.exp ((a - c) * v) * Real.exp (l * v) =
          Real.exp (a * v) * Real.exp (-(2 * s + c - l) * v) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have halg : (u : ℝ) * ((K / ρ * Real.exp (-(2 * s) * v)) *
          (S * Real.exp ((a - c) * v)) / ρ) * Real.exp (l * v) =
          (K * S / ρ ^ 2) * ((u : ℝ) * Real.exp (a * v)) * Real.exp (-(2 * s + c - l) * v) := by
        calc
          _ = (K * S / ρ ^ 2) * (u : ℝ) *
              (Real.exp (-(2 * s) * v) * Real.exp ((a - c) * v) * Real.exp (l * v)) := by
                field_simp
          _ = _ := by rw [he]; ring
      rw [halg] at hh
      have hw' := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hw u v) (by positivity : 0 ≤ K * S / ρ ^ 2))
        (Real.exp_pos (-(2 * s + c - l) * v)).le
      have hbound : scalarPositiveLambdaCorrection hU hV x.1 x.2.1 ν u v * Real.exp (l * v) ≤
          Clate * Real.exp (-(2 * s + c - l) * v) := by
        simpa only [Clate, mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using hh.trans hw'
      exact hbound.trans_lt (hT₁ v ((le_max_right _ _).trans hv))
    · have hvT : (v : ℝ) ≤ T := (lt_of_not_ge hv).le
      have hh := mul_le_mul_of_nonneg_right
        (hcorr u v L hL (fun w => max_le ((le_abs_self _).trans (hlam w v)) hL)) (Real.exp_pos (l * v)).le
      have he : Real.exp ((a - c) * v) * Real.exp (l * v) ≤ Real.exp ((a - c + |l|) * T) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have hh := mul_le_mul_of_nonneg_right (le_abs_self l) v.property.1
        have ht := mul_le_mul_of_nonneg_left hvT (by positivity : 0 ≤ a - c + |l|)
        nlinarith only [hh, ht]
      have hu := (le_div_iff₀ (by positivity : 0 < 2 * (Chead + 1))).1 hUW
      have hhead : U * Chead < Hlo := by nlinarith only [hu, hU, hHlo]
      calc
        _ ≤ (u : ℝ) * Cearly * (Real.exp ((a - c) * v) * Real.exp (l * v)) := by
          apply hh.trans_eq
          dsimp only [Cearly]
          ring
        _ ≤ (u : ℝ) * Chead := by
          simpa only [Chead, mul_assoc] using mul_le_mul_of_nonneg_left he (mul_nonneg u.property.1 hCe)
        _ ≤ U * Chead := mul_le_mul_of_nonneg_right u.property.2 hCh
        _ < Hlo := hhead
  have hdata := incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)
  have hzero : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp hf u 1 = 0 := by
    filter_upwards [incomingWaveVelocity_ae hUR hp hf] with u hu
    rw [hu]
    rfl
  refine ⟨hbad, ?_⟩
  apply hx.zero_scalar_positive hr rfl hdata.1 hzero hnneg
  intro u v
  have hh := (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v
  rw [hh]
  change scalarPositiveLambdaCorrection hU hV x.1 x.2.1 ν u v < r v * (h v / r v)
  rw [mul_div_cancel₀ _ (hr0 v)]
  exact hbad u v

end CauchyHorizon.Background
