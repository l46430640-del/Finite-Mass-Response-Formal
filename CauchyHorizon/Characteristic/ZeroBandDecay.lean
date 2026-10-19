import CauchyHorizon.Characteristic.ZeroScalar
import CauchyHorizon.Characteristic.BandTransportDecay
import CauchyHorizon.Characteristic.ScalarOverlap
import CauchyHorizon.Radial.CriticalWeight

/-! The zero-incoming reference has decaying normalized scalar traces and bottom flux. -/

open Set MeasureTheory
open scoped ENNReal

namespace CauchyHorizon.Background

set_option maxHeartbeats 3000000 in
theorem exists_zero_band_decay (B : Background) {s H dH : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    (hm : B.criticalExponent < 1) (hks : B.innerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R γ : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧ 0 < γ ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ C d T : ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧ 0 ≤ C ∧ 0 < d ∧ 0 < T ∧
          ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
            ∀ (hfU : MemLp (fun _ : ℝ => (0 : ℝ)) p (volume.restrict (Icc 0 U))) (x : WaveState U V)
              (hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x),
              ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ∈ Ioo 0 U → (v : ℝ) ∈ Ioo 0 V →
                T ≤ (v : ℝ) → x.1 u v 0 ∈ Icc Y Z →
                let ν := radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                let θ := Real.exp (B.innerRate * v) * (x.1 u v 0 * x.2.1 u v 1)
                let q := Real.exp (B.innerRate * v) * (u : ℝ) *
                  scalarTransportCorrection hV ν x.2.1 u v / B.criticalWeight (x.1 u v 0)
                x.2.1 u v 0 ≤ -d ∧ |θ| + |q| ≤ C * Real.exp (-γ * v) ∧
                  0 ≤ (-1 / x.2.1 u v 0) * q ^ 2 ∧
                    (-1 / x.2.1 u v 0) * q ^ 2 ≤ C ^ 2 / d * Real.exp (-(2 * γ) * v) := by
  intro hi hr0
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  let a := B.outerRate
  let k := B.innerRate
  have ha : 0 < a := B.outerRate_pos
  have hk : 0 < k := B.innerRate_pos
  have hka : k < a := (div_lt_one ha).1 hm
  let c := (k + min a s) / 2
  have hkc : k < c := by dsimp only [c]; linarith only [lt_min hka hks]
  have hca : c < a := by dsimp only [c]; linarith only [hka, min_le_left a s]
  have hcs : c ≤ s := by dsimp only [c]; linarith only [hks, min_le_right a s]
  have hc0 : 0 < c := hk.trans hkc
  have hac : 0 < a - c := sub_pos.2 hca
  let γ := c - k
  have hγ : 0 < γ := sub_pos.2 hkc
  let cg := min s a / 2
  have hcg : 0 < cg := half_pos (lt_min hs ha)
  have hcga : cg < a := (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans_lt (half_lt_self ha)
  have hcgs : cg ≤ s := (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans (half_le_self hs.le)
  have hcgHalf : cg ≤ a / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨δg, Rg, hδg, _hδgr, hRg, _hRgr, hdomain⟩ := B.exists_band_radiation_domain
    (A := 0) hs hH hdH hdHR le_rfl hcg hcga hcgs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δd, Rd, hδd, _hδdr, hRd, hdecay⟩ := B.exists_band_transport_decay
    (A := 0) hs hH hdH hdHR le_rfl hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨max δg δd, min Rg Rd, γ, hδg.trans_le (le_max_left _ _),
    ⟨lt_min hRg.1 hRd.1, (min_le_left _ _).trans_lt hRg.2⟩, hγ, ?_⟩
  intro Y Z hY hYZ hYR hZ
  have hY0 : 0 < Y := B.inner_pos.trans hY
  have hZ0 : 0 < Z := hY0.trans hYZ
  obtain ⟨Ug, Tg, _j, D, _η, _Cg, N, L, hUg, hUgδ, hTg, _hj, hD, _hη, _hCg, hN, hL, hsolve⟩ :=
    hdomain Y hY (hYR.trans (min_le_left _ _))
  obtain ⟨Ud, _Cd, d, _γd, Td, hUd, _hUdδ, _hCd, hd, _hγd, hTd, hmargin⟩ :=
    hdecay Y Z hY hYZ (hYR.trans (min_le_right _ _)) hZ
  have hyr (z : ℝ) (hz : z ∈ Icc Y Z) : z ∈ Ioo B.inner B.event :=
    ⟨hY.trans_le hz.1, hz.2.trans_lt hZ⟩
  have hqc : ContinuousOn (fun z => (B.criticalWeight z)⁻¹) (Icc Y Z) :=
    (B.criticalWeight_continuousOn.mono hyr).inv₀ (fun z hz => (B.criticalWeight_pos (hyr z hz)).ne')
  obtain ⟨Q, hQbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hqc
  let Qm := max Q 0
  have hQm : 0 ≤ Qm := le_max_right _ _
  let E := H / Y * Real.exp (L * N * D / (Y ^ 2 * (a - c)))
  let C := (Z + N * D / (a - c) * Qm) * E
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨min Ug Ud, C, d, max Tg Td, lt_min hUg hUd,
    ((min_le_left _ _).trans hUgδ).trans (le_max_left _ _), hC, hd,
    hTg.trans_le (le_max_left _ _), ?_⟩
  intro p hp U V hU hV hUR hUU hfU x hx u v hu hv hTv hrband ν θ q
  have hcp : cg ≤ a * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le
    linarith only [hcgHalf, hh, ha]
  have hfg : MemLp (fun _ : ℝ => (0 : ℝ)) p (volume.restrict (Icc 0 δg)) := MemLp.zero'
  obtain ⟨g, _hgc, hga, _hgl, _hgdc, _hgstart, hpoint, hphysical⟩ :=
    hsolve p hp (fun _ => 0) hfg (by simp) hcp
  have hvG : Tg ≤ (v : ℝ) := (le_max_left _ _).trans hTv
  have hphys := hphysical U V hU hV hUR (hUU.trans (min_le_left _ _)) hfU x hx
  have hug : (u : ℝ) ≤ g v := by
    by_cases hgU : g v ≤ U
    · have hg : g v ∈ Icc 0 U := ⟨(hpoint v hvG).1.1.le, hgU⟩
      have hhit := hphys.2.1 v ⟨hvG, v.property.2⟩ hgU
      simp only [intervalExtension_apply, projIcc_of_mem hU hg, projIcc_of_mem hV v.property] at hhit
      by_contra hn
      have hanti := hx.radial_strictAnti hx.choose rfl
        (incomingWave_constraint_data hU hUR hp hfU (horizonPhi h r 0)).1 v
        (fun w => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU w v).2.2.1)
      have hh := hanti (show (⟨g v, hg⟩ : Icc 0 U) < u from lt_of_not_ge hn)
      change x.1 u v 0 < x.1 ⟨g v, hg⟩ v 0 at hh
      rw [hhit] at hh
      exact (not_lt_of_ge hrband.1) hh
    · exact u.property.2.trans (lt_of_not_ge hgU).le
  let hf' := hfU.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl u.property.2) le_rfl)
  let y := waveTranslate (a := 0) (U := (u : ℝ)) (b := 0) (V := (v : ℝ))
    le_rfl (by simpa only [zero_add] using u.property.2) le_rfl (by simpa only [zero_add] using v.property.2) x
  have hy := hx.horizon_prefix hU hV hUR u.property.1 v.property.1 u.property.2 v.property.2 hc hi hrc hr0 hp hfU
  let uu : Icc 0 (u : ℝ) := ⟨u, u.property.1, le_rfl⟩
  let vv : Icc 0 (v : ℝ) := ⟨v, v.property.1, le_rfl⟩
  have hpre := hphysical u v u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    (u.property.2.trans (hUU.trans (min_le_left _ _))) hf' y hy
  have hgeom (w : Icc 0 (u : ℝ)) (t : Icc 0 (v : ℝ)) :=
    hpre.1 w t (w.property.2.trans (hug.trans
      (hga.antitoneOn (le_max_left Tg (t : ℝ)) hvG (max_le hvG t.property.2))))
  have hwidth := (mul_le_mul_of_nonneg_right hug (Real.exp_pos _).le).trans (hpoint v hvG).2.1
  have hout (t : Icc 0 (v : ℝ)) : Real.exp (c * t) * |h t| ≤ H := by
    have hh := mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos (c * t)).le
    rw [Real.norm_eq_abs] at hh
    have he : Real.exp (c * t) * Real.exp (-s * t) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith only [mul_nonneg (sub_nonneg.2 hcs) t.property.1]
    nlinarith only [hh, mul_le_mul_of_nonneg_left he hH]
  have hscalar := hy.horizon_zero_weighted_scalar u.property.1 v.property.1 (u.property.2.trans_lt hUR)
    hc hi hrc hr0 hφ hrd hp hf' hc0.le hca hY0 hN.le hL hH
    (fun w t => (hgeom w t).1) (fun w t => (hgeom w t).2.1) (fun w t => (hgeom w t).2.2) hout hwidth
  have he := hy.horizon_overlap u.property.1 v.property.1 (u.property.2.trans_lt hUR) hU hV hUR
    hc hi hrc hr0 hp hf' hfU hx uu.property u.property vv.property v.property
  have hζ := hy.horizon_overlap_zeta u.property.1 v.property.1 (u.property.2.trans_lt hUR) hU hV hUR
    hc hi hrc hr0 hp hf' hfU hx uu.property u.property vv.property v.property
  simp only [mul_zero, zero_add] at hζ
  have hφv : |x.2.1 u v 1| ≤ E * Real.exp (-c * v) := by
    have hh := hscalar.1 uu vv
    rwa [he.2] at hh
  have hζv : |scalarTransportCorrection hV ν x.2.1 u v| ≤ N * E / (a - c) * Real.exp ((a - c) * v) := by
    have hh := hscalar.2 uu vv
    rwa [hζ] at hh
  have hθ : |θ| ≤ Z * E * Real.exp (-γ * v) := by
    dsimp only [θ]
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (hY0.trans_le hrband.1)]
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul hrband.2 hφv (abs_nonneg _) hZ0.le) (Real.exp_pos (k * v)).le
    apply hh.trans_eq
    rw [show -γ * (v : ℝ) = k * v + -c * v by dsimp only [γ]; ring, Real.exp_add]
    ring
  have hqinv : |(B.criticalWeight (x.1 u v 0))⁻¹| ≤ Qm := by
    have hh : |(B.criticalWeight (x.1 u v 0))⁻¹| ≤ Q := by
      simpa only [Real.norm_eq_abs] using hQbound _ hrband
    exact hh.trans (le_max_left _ _)
  have hq : |q| ≤ (N * E / (a - c) * D * Qm) * Real.exp (-γ * v) := by
    dsimp only [q]
    rw [div_eq_mul_inv, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg u.property.1]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hζv
      (mul_nonneg (Real.exp_pos (k * v)).le u.property.1)) hqinv (abs_nonneg _)
      (mul_nonneg (mul_nonneg (Real.exp_pos (k * v)).le u.property.1)
        (mul_nonneg (div_nonneg (mul_nonneg hN.le hE) hac.le) (Real.exp_pos _).le))
    have ht : Real.exp (k * v) * (u : ℝ) * (N * E / (a - c) * Real.exp ((a - c) * v)) * Qm =
        (N * E / (a - c) * Qm) * ((u : ℝ) * Real.exp (a * v)) * Real.exp (-γ * v) := by
      have hexp : Real.exp (k * v) * Real.exp ((a - c) * v) = Real.exp (a * v) * Real.exp (-γ * v) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp only [γ]
        ring
      calc
        _ = (N * E / (a - c) * Qm) * u * (Real.exp (k * v) * Real.exp ((a - c) * v)) := by ring
        _ = _ := by rw [hexp]; ring
    rw [ht] at hh
    apply hh.trans
    have hw := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ N * E / (a - c) * Qm)) (Real.exp_pos (-γ * v)).le
    exact hw.trans_eq (by ring)
  have hsum : |θ| + |q| ≤ C * Real.exp (-γ * v) := by
    apply (add_le_add hθ hq).trans_eq
    dsimp only [C]
    ring
  have hfd : MemLp (fun _ : ℝ => (0 : ℝ)) p (volume.restrict (Icc 0 δd)) := MemLp.zero'
  have hlam := (hmargin p hp (fun _ => 0) hfd (by simp) U V hU hV hUR
    (hUU.trans (min_le_right _ _)) hfU x hx u v hu hv ((le_max_right _ _).trans hTv) hrband).1
  have hlneg : x.2.1 u v 0 < 0 := hlam.trans_lt (neg_neg_of_pos hd)
  have hcpos : 0 ≤ -1 / x.2.1 u v 0 := div_nonneg_of_nonpos (by norm_num) hlneg.le
  have hcinv : -1 / x.2.1 u v 0 ≤ 1 / d := by
    rw [show (-1 : ℝ) / x.2.1 u v 0 = 1 / (-x.2.1 u v 0) by simp [div_eq_mul_inv]]
    exact one_div_le_one_div_of_le hd (by linarith only [hlam])
  have hqsq : q ^ 2 ≤ C ^ 2 * Real.exp (-(2 * γ) * v) := by
    have hh := (sq_le_sq₀ (abs_nonneg q) (mul_nonneg hC (Real.exp_pos _).le)).2
      ((le_add_of_nonneg_left (abs_nonneg θ)).trans hsum)
    rw [sq_abs, mul_pow, pow_two (Real.exp _), ← Real.exp_add,
      show -γ * (v : ℝ) + -γ * v = -(2 * γ) * v by ring] at hh
    exact hh
  refine ⟨hlam, hsum, mul_nonneg hcpos (sq_nonneg q), ?_⟩
  exact (mul_le_mul hcinv hqsq (sq_nonneg q) (one_div_nonneg.2 hd.le)).trans_eq (by ring)

end CauchyHorizon.Background
