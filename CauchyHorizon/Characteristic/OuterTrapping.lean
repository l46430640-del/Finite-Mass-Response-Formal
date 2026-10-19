import CauchyHorizon.Characteristic.HorizonBounds
import CauchyHorizon.Characteristic.OuterExistence
import CauchyHorizon.Characteristic.OuterConstraint
import CauchyHorizon.Reduced.RadialTrapping

/-! Signed outer flux and uniform entry into the trapped region. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

theorem exists_outer_flux_prefix (B : Background) {s H dH c A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s) (hA : 0 ≤ A) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ n N L q K T : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ 0 < n ∧ 0 < N ∧
      0 ≤ L ∧ 0 < q ∧ 0 ≤ K ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) → U * Real.exp (B.outerRate * V) ≤ δ →
        ∃! x : WaveState U V, ∃ hx :
          IsWaveIntegral hU hV B.charge B.cosmological (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x,
          ∀ (u : Icc 0 U) (v : Icc 0 V),
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
            n * Real.exp (B.outerRate * v) ≤ -ν u v ∧ -ν u v ≤ N * Real.exp (B.outerRate * v) ∧
              |x.2.1 u v 0| ≤ L ∧ 0 < x.1 u v 0 ∧ x.1 u v 0 ≤ B.event + dH ∧
              n * u * Real.exp (B.outerRate * v) ≤ r v - x.1 u v 0 ∧
              r v - x.1 u v 0 ≤ N * u * Real.exp (B.outerRate * v) ∧
              (T ≤ (v : ℝ) → x.1 u v 0 * x.2.1 u v 0 ≤
                K * Real.exp (-(2 * s) * v) - q * u * Real.exp (B.outerRate * v)) := by
  let hi := horizon_mass_integrable hs hH hc hb
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  have ha : 0 < a := B.outerRate_pos
  let ρ := (B.event - dH) / 2
  let R := B.event + dH
  have hρ : 0 < ρ := half_pos (sub_pos.2 hdHR)
  have hR : 0 < R := add_pos_of_pos_of_nonneg B.event_pos hdH
  obtain ⟨W, hW, hrlam⟩ := B.horizon_radius_lambda_bounds hs hH hdH hdHR hb hrdec
  have haxis (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : r t ∈ Icc (2 * ρ) R := by
    have hh := (hrlam t ht).1
    constructor
    · dsimp only [ρ]; linarith only [hh.1]
    · exact hh.2
  have hlout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      |horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological| ≤ W :=
    (hrlam t ht).2.trans (mul_le_of_le_one_right hW (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hs]) ht)))
  have hout (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : Real.exp (c * t) * |h t| ≤ H := by
    have hh := mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos (c * t)).le
    rw [Real.norm_eq_abs] at hh
    have he : Real.exp (c * t) * Real.exp (-s * t) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith only [mul_nonneg (sub_nonneg.2 hcs) ht]
    nlinarith only [hh, mul_le_mul_of_nonneg_left he hH]
  obtain ⟨nH, NH, hnH, _hnH1, hNH, hνaxis⟩ := hOut.nu_bounds hs hc hi hrc hr0
  have hNHp : 0 < NH := zero_lt_one.trans_le hNH
  obtain ⟨δ₀, L, hδ₀, _hδ₀1, hδ₀r, hL, hsolve⟩ := exists_horizon_outer_wave hc hi hrc hr0 hφ hrd
    ha hc0 hca hρ hnH hNHp hH hW hA haxis hνaxis hout hlout
  obtain ⟨η, hη, _hηR, hpot⟩ := B.exists_negative_radial_potential
  let n := nH / 2
  let N := 2 * NH
  let P := a / 8
  have hn : 0 < n := by dsimp only [n]; positivity
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hP : 0 < P := by dsimp only [P]; positivity
  let E₀ := 2 * (H + L * (r 0 / ρ) * A) / ρ
  let C := (2 * R / n) * (r 0 / ρ) ^ 2 * A ^ 2
  let D := (2 * R / n) * (N / (ρ * (a - c)) * E₀) ^ 2
  obtain ⟨δ, hδ, hδ1, hδb, hδη, hδsmall, hδerr⟩ := exists_small_outer_width
    (by positivity : 0 < 4 * δ₀) (by positivity : 0 < 2 * η)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)) N (L * N / (ρ ^ 2 * (a - c))) C D
  have hδδ : δ ≤ δ₀ := by linarith only [hδb]
  have hNδ : N * δ ≤ η / 2 := by linarith only [hδη]
  have hsmall : L * N * δ / (ρ ^ 2 * (a - c)) ≤ 1 / 2 := by
    simpa only [div_mul_eq_mul_div] using hδsmall
  have hexp : Tendsto (fun t : ℝ => dH * Real.exp (-(2 * s) * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith only [hs] : -(2 * s) < 0))).const_mul dH
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hexp.eventually_lt_const (half_pos hη))
  let T := max 0 T₀
  have hT (v : ℝ) (hv : T ≤ v) : dH * Real.exp (-(2 * s) * v) ≤ η / 2 :=
    (hT₀ v ((le_max_right _ _).trans hv)).le
  refine ⟨δ, n, N, L, 2 * ρ * P * n, R * W, T, hδ, hδδ.trans hδ₀r, hn,
    by dsimp only [N]; positivity, hL, by positivity, by positivity, le_max_left _ _, ?_⟩
  intro U V hU hV hUR p hp f hf hfn hcb hwidth
  obtain ⟨x, ⟨hx, hg⟩, _⟩ := hsolve U V hU hV hUR p hp f hf hfn hcb (hwidth.trans hδδ)
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  have hνneg (q : Icc 0 U) (v : Icc 0 V) : ν q v < 0 :=
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf q v).2.2.1
  have hlo (q : Icc 0 U) (v : Icc 0 V) : ρ ≤ x.1 q v 0 := by linarith only [(hg q v).1, hρ]
  have hrhi (q : Icc 0 U) (v : Icc 0 V) : x.1 q v 0 ≤ R := (hg q v).2.1
  have hlam (q : Icc 0 U) (v : Icc 0 V) : |x.2.1 q v 0| ≤ L := (hg q v).2.2.1
  have hnlo (q : Icc 0 U) (v : Icc 0 V) : n * Real.exp (a * v) ≤ -ν q v :=
    (mul_le_mul_of_nonneg_right (by dsimp only [n]; linarith only [hnH]) (Real.exp_pos _).le).trans (hg q v).2.2.2.1
  have hnhi (q : Icc 0 U) (v : Icc 0 V) : |ν q v| ≤ N * Real.exp (a * v) := by
    rw [abs_of_neg (hνneg q v)]
    exact (hg q v).2.2.2.2.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [N]; linarith only [hNHp]) (Real.exp_pos _).le)
  have hw (q : Icc 0 U) (v : Icc 0 V) : q * Real.exp (a * v) ≤ δ :=
    (mul_le_mul q.property.2 (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left v.property.2 ha.le))
      (Real.exp_pos _).le hU).trans hwidth
  have hΩ (q : Icc 0 U) (v : Icc 0 V) : (2 * n) * Real.exp (a * v) ≤ Real.exp (x.1 q v 2) := by
    have hfb := hx.horizon_outer_feedback hU hV hUR hc hi hrc hr0 hφ hrd hp hf hA hfn
      hc0 hca hcb hρ hR.le hn hN hL hH hδ.le hlo hrhi hnlo hnhi hlam
      (fun v => hout v v.property.1) hwidth hsmall q v
    have he := outer_constraint_envelope hp ha.le hc0 hca hρ hR.le hrp.le hn hN hL hH hA
      hδ.le hδ1 q.property.1 v.property.1 (hw q v)
    have heps := he.trans hδerr
    have he' := Real.exp_le_exp.2 (neg_le_neg heps)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he'
    norm_num only at he'
    have hk : (1 / 2 : ℝ) ≤ -Real.exp (x.1 q v 2) / (4 * ν q v) := he'.trans hfb.2.1
    have hh := (le_div_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) (hνneg q v))).1 hk
    linarith only [hh, hnlo q v]
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · intro u v
    have htr := (hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd hp hf).2 v
    have hinu := (incomingWave_constraint_data hU hUR hp hf (horizonPhi h r 0)).1
    have hgap (q : Icc 0 U) : 0 ≤ r v - x.1 q v 0 ∧
        r v - x.1 q v 0 ≤ N * q * Real.exp (a * v) := by
      have hh := hx.radial_gap_weighted_bound hx.choose rfl hinu (fun q v => (hνneg q v).le) hnhi q v
      rw [htr] at hh
      exact hh
    have hrad := hx.radial_gap_weighted_lower hx.choose rfl hinu hnlo u v
    rw [htr] at hrad
    refine ⟨hnlo u v, (neg_le_abs (ν u v)).trans (hnhi u v), hlam u v,
      hρ.trans_le (hlo u v), hrhi u v, hrad, (hgap u).2, ?_⟩
    intro hv
    have htailr := (hrdec v v.property.1).trans (hT v hv)
    have hpv (q : Icc 0 U) : radialPotential (x.1 q v 0) B.charge B.cosmological ≤ -P := by
      have ht := abs_le.1 htailr
      have hgapδ : r v - x.1 q v 0 ≤ N * δ := (hgap q).2.trans
        (by nlinarith only [mul_le_mul_of_nonneg_left (hw q v) hN])
      have hrange : x.1 q v 0 ∈ Icc (B.event - η) (B.event + η) :=
        ⟨by linarith only [ht.1, hgapδ, hNδ], by linarith only [ht.2, (hgap q).1, hη]⟩
      simpa only [P, neg_div] using hpot _ hrange
    have hflam := hx.radial_flux_negative_bound hx.choose rfl hρ.le hP.le
      (by positivity : 0 ≤ 2 * n) hlo v hpv (fun q => hΩ q v) u
    rw [htr] at hflam
    change x.1 u v 0 * x.2.1 u v 0 ≤ r v * horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological -
      ρ * P * (2 * n) * u * Real.exp (a * v) at hflam
    have hprod : r v * horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological ≤
        R * W * Real.exp (-(2 * s) * v) := by
      apply (mul_le_mul_of_nonneg_left (le_abs_self _) ((sub_pos.2 hdHR).trans_le (hrb v)).le).trans
      exact ((mul_le_mul_of_nonneg_right (haxis v v.property.1).2 (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hrlam v v.property.1).2 hR.le)).trans_eq (by ring)
    nlinarith only [hflam, hprod]
  · intro y hy
    exact hy.1.incoming_unique hU hV hUR hp hf hx

theorem exists_outer_trapped_prefix (B : Background) {s H dH c A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s) (hA : 0 ≤ A) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ T σ τ : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ 0 ≤ T ∧ 0 < σ ∧ 0 < τ ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) → U * Real.exp (B.outerRate * V) ≤ δ →
        ∃! x : WaveState U V,
          IsWaveIntegral hU hV B.charge B.cosmological (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hf) x ∧
          ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) → u * Real.exp (B.outerRate * v) = δ →
            x.1 u v 0 ≤ B.event - σ ∧ x.2.1 u v 0 ≤ -τ := by
  obtain ⟨δ, n, N, L, q, K, T₀, hδ, hδr, hn, _hN, _hL, hq, _hK, hT₀, hsolve⟩ :=
    B.exists_outer_flux_prefix hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  let σ := n * δ / 2
  let R := B.event + dH
  let τ := q * δ / (2 * R)
  have hR : 0 < R := add_pos_of_pos_of_nonneg B.event_pos hdH
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have he : Tendsto (fun t : ℝ => max dH K * Real.exp (-(2 * s) * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, id_eq] using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith only [hs] : -(2 * s) < 0))).const_mul (max dH K)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1
    (he.eventually_lt_const (lt_min hσ (by positivity : 0 < q * δ / 2)))
  refine ⟨δ, max T₀ T₁, σ, τ, hδ, hδr, hT₀.trans (le_max_left _ _), hσ, hτ, ?_⟩
  intro U V hU hV hUR p hp f hf hfn hcb hw
  obtain ⟨x, ⟨hx, hg⟩, _⟩ := hsolve U V hU hV hUR p hp f hf hfn hcb hw
  refine ⟨x, ⟨hx, ?_⟩, fun y hy => hy.1.incoming_unique hU hV hUR hp hf hx⟩
  intro u v hv heq
  obtain ⟨_, _, _, hrp, hrhi, hgap, _, hflux⟩ := hg u v
  have ht := (hT₁ v ((le_max_right _ _).trans hv)).le
  have htailr := (hrdec v v.property.1).trans
    ((mul_le_mul_of_nonneg_right (le_max_left dH K) (Real.exp_pos _).le).trans (ht.trans (min_le_left _ _)))
  have htailK := (mul_le_mul_of_nonneg_right (le_max_right dH K) (Real.exp_pos (-(2 * s) * v)).le).trans
    (ht.trans (min_le_right _ _))
  have hfl := hflux ((le_max_left _ _).trans hv)
  rw [mul_assoc n, heq] at hgap
  rw [mul_assoc q, heq] at hfl
  have hprod : x.1 u v 0 * x.2.1 u v 0 ≤ -(q * δ / 2) := by linarith only [hfl, htailK]
  have hlamneg : x.2.1 u v 0 < 0 := by
    have hh : 0 < q * δ / 2 := by positivity
    nlinarith only [hprod, hh, hrp]
  have hlam : x.2.1 u v 0 ≤ -τ := by
    dsimp only [τ]
    rw [← neg_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * R)).2
    have hh := mul_le_mul_of_nonpos_right hrhi hlamneg.le
    dsimp only [R] at *
    nlinarith only [hh, hprod]
  have hrend := (abs_le.1 htailr).2
  exact ⟨by dsimp only [σ] at hrend ⊢; linarith only [hrend, hgap], hlam⟩

end CauchyHorizon.Background
