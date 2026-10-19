import CauchyHorizon.Characteristic.BandGeometry

/-! A small matching speed from the simple inner root and the actual mass error. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

theorem Background.exists_small_matching_speed (B : Background) {R L : ℝ}
    (hR : B.inner < R) (hRe : R ≤ B.event) (hL : 0 < L) :
    ∃ Y ∈ Ioo B.inner R, ∀ C η : ℝ, 0 < η → ∃ T₀ : ℝ, 0 ≤ T₀ ∧
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
        (u : Icc 0 U) (v : Icc 0 V), T₀ ≤ v → x.1 u v 0 = Y →
        let ν := radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
        |massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v - B.mass| ≤ C * Real.exp (-η * v) →
          0 < -x.2.1 u v 0 ∧ -x.2.1 u v 0 ≤ L := by
  have hFzero : B.F B.inner = 0 := B.root_inner
  have hnear : ∀ᶠ y in 𝓝 B.inner, |B.F y| < L / 2 := by
    have hh := B.hasDerivAt_F_inner.continuousAt.abs.eventually_lt_const (show |B.F B.inner| < L / 2 by
      rw [hFzero, abs_zero]; positivity)
    exact hh
  have hright : ∀ᶠ y in 𝓝[>] B.inner, y ∈ Ioo B.inner R ∧ |B.F y| < L / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      ((eventually_lt_nhds hR).and hnear).filter_mono nhdsWithin_le_nhds] with y hy hb
    exact ⟨⟨hy, hb.1⟩, hb.2⟩
  obtain ⟨Y, hY, hFY⟩ := hright.exists
  have hY0 : 0 < Y := B.inner_pos.trans hY.1
  have hFneg : B.F Y < 0 := B.F_neg ⟨hY.1, hY.2.trans_le hRe⟩
  let δ := Y * (-B.F Y) / 4
  have hδ : 0 < δ := div_pos (mul_pos hY0 (neg_pos.2 hFneg)) (by norm_num)
  refine ⟨Y, hY, ?_⟩
  intro C η hη
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-η * t)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply, id_eq] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hη))).const_mul C
  obtain ⟨T₀, hlate⟩ := eventually_atTop.1 (hlim.eventually_lt_const hδ)
  refine ⟨max 0 T₀, le_max_left _ _, ?_⟩
  intro U V h r hU hV hUR hc hi hrc hr0 hφ hrd p hp f hf x hx u v hTv hrY
  dsimp only
  intro hm
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v
  let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf
  have hk0 : 0 < κ := (hg u v).2.2.2.1
  have hk1 : κ ≤ 1 := (hg u v).2.2.2.2
  have hmm : |m - B.mass| ≤ δ := hm.trans (hlate v ((le_max_right _ _).trans hTv)).le
  have herr : |2 * (m - B.mass) / Y| ≤ -B.F Y / 2 := by
    calc
      _ = 2 * |m - B.mass| / Y := by rw [abs_div, abs_mul, abs_of_pos hY0]; norm_num
      _ ≤ 2 * δ / Y := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmm (by norm_num)) hY0.le
      _ = _ := by dsimp only [δ]; field_simp; ring
  have hFm : horizonFunction Y m B.charge B.cosmological = B.F Y - 2 * (m - B.mass) / Y :=
    horizonFunction_mass_difference Y m B.mass B.charge B.cosmological
  have hFmneg : horizonFunction Y m B.charge B.cosmological < 0 := by
    rw [hFm]
    linarith only [(abs_le.1 herr).1, hFneg]
  have hFbound : -horizonFunction Y m B.charge B.cosmological ≤ L := by
    rw [hFm]
    rw [abs_of_neg hFneg] at hFY
    linarith only [(abs_le.1 herr).2, hFY, hL]
  have hid := massField_lambda_eq_kappa (e := B.charge) (Λ := B.cosmological)
    x.1 x.2.1 ν hx.choose (fun w t => (hg w t).2.2.1.ne) u v
  change x.2.1 u v 0 = κ * horizonFunction (x.1 u v 0) m B.charge B.cosmological at hid
  rw [hrY] at hid
  have hvel : x.2.1 u v 0 < 0 := by rw [hid]; exact mul_neg_of_pos_of_neg hk0 hFmneg
  refine ⟨neg_pos.2 hvel, ?_⟩
  calc
    -x.2.1 u v 0 = κ * (-horizonFunction Y m B.charge B.cosmological) := by rw [hid]; ring
    _ ≤ -horizonFunction Y m B.charge B.cosmological := mul_le_of_le_one_left (neg_pos.2 hFmneg).le hk1
    _ ≤ L := hFbound

end CauchyHorizon
