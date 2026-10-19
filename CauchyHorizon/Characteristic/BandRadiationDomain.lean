import CauchyHorizon.Characteristic.BandArrival
import CauchyHorizon.Characteristic.PhysicalOverlapNu

/-! A common actual radius boundary supplies the geometry for critical band radiation. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Background

set_option maxHeartbeats 1600000 in
theorem exists_band_radiation_domain (G : Background) {s H dH A c : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event) (hA : 0 ≤ A)
    (hc0 : 0 < c) (hca : c < G.outerRate) (hcs : c ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t) (hrinit : G.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hout
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ R ∈ Ioo G.inner G.event ∧ R < r 0 ∧
      ∀ Y : ℝ, G.inner < Y → Y ≤ R → ∃ U₀ T j D η C N L : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ 0 < j ∧ 0 < D ∧ 0 < η ∧ 0 < C ∧ 0 < N ∧ 0 ≤ L ∧
        ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
          (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
          c ≤ G.outerRate * (1 - 1 / p.toReal) →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧ Tendsto g atTop (𝓝 0) ∧
            ContinuousOn (deriv g) (Ici T) ∧ U₀ < g T ∧
            (∀ t ∈ Ici T, g t ∈ Ioo 0 (r 0) ∧ g t * Real.exp (G.outerRate * t) ≤ D ∧
              DifferentiableAt ℝ g t ∧ η ≤ -deriv g t / g t ∧
              j ≤ g t * Real.exp (G.outerRate * t) ∧ -deriv g t / g t ≤ C) ∧
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV G.charge G.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                  (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR hp hfU) x),
                let ν := radialNuField hV G.charge G.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                (∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ g (max T (v : ℝ)) →
                  Y ≤ x.1 u v 0 ∧ |ν u v| ≤ N * Real.exp (G.outerRate * v) ∧ |x.2.1 u v 0| ≤ L) ∧
                (∀ t ∈ Icc T V, g t ≤ U →
                  intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 = Y) ∧
                ∀ (u : Icc 0 U) (v : Icc 0 V), 0 < (u : ℝ) →
                  x.1 u v 0 = Y → x.2.1 u v 0 < 0 → g v = u := by
  dsimp only
  let hi := horizon_mass_integrable hs hH hc hout
  let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hout hrb
  obtain ⟨δ₁, R₁, hδ₁, hδ₁r, hR₁, hbounds⟩ :=
    G.exists_band_bounds hs hH hdH hdHR hA hc0 hca hcs hc hout hrc hrb hrd hrdec hOut
  obtain ⟨δ₂, R₂, hδ₂, hδ₂r, hR₂, hR₂r, harrival⟩ :=
    G.exists_band_arrival hs hH hdH hdHR hA hc0 hca hcs hc hout hrc hrb hrinit hrd hrdec hOut
  refine ⟨max δ₁ δ₂, min R₁ R₂, hδ₁.trans_le (le_max_left _ _), max_le hδ₁r hδ₂r,
    ⟨lt_min hR₁.1 hR₂.1, (min_le_left _ _).trans_lt hR₁.2⟩,
    (min_le_right _ _).trans_lt hR₂r, ?_⟩
  intro Y hY hYR
  obtain ⟨U₀, _Db, _nb, N, L, _E, hU₀, hU₀δ, _hDb, _hnb, hN, hL, _hE, hband⟩ :=
    hbounds Y hY (hYR.trans (min_le_left _ _))
  obtain ⟨ε, j, D, η, C, T, _n, _Na, _La, _Ea, _τ, _σ, _Cerr,
    hε, hεδ, hj, hD, hη, hC, hT, _hn, _hNa, _hLa, _hEa, _hτ, _hσ, _hσε, _hCerr, hsolve⟩ :=
    harrival Y hY (hYR.trans (min_le_right _ _))
  let Uc := min U₀ (min (ε / 4) (j * Real.exp (-G.outerRate * T) / 2))
  have hUc : 0 < Uc := by dsimp only [Uc]; positivity
  have hUcε : Uc < ε / 2 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt
    (by linarith only [hε])
  refine ⟨Uc, T, j, D, η, C + 1, N, L, hUc, ((min_le_left _ _).trans hU₀δ).trans (le_max_left _ _),
    hT, hj, hD, hη, by positivity, hN, hL, ?_⟩
  intro p hp f hf hfn hcp
  let hf₁ := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_left δ₁ δ₂)) le_rfl)
  let hf₂ := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (le_max_right δ₁ δ₂)) le_rfl)
  have hfn₁ := (scalar_prefix_norm_le (le_max_left δ₁ δ₂) hf).trans hfn
  have hfn₂ := (scalar_prefix_norm_le (le_max_right δ₁ δ₂) hf).trans hfn
  obtain ⟨arrival, g, _hac, _haa, _hal, haT, _haσ, hgc, hga, hgl, hpoint, hinv, hwitness⟩ :=
    hsolve p hp f hf₂ hfn₂ hcp
  have hsub : Ici T ⊆ Ioi (arrival (ε / 2)) := fun _ ht => haT.trans_le ht
  have hstart : Uc < g T := by
    have hh := mul_le_mul_of_nonneg_right (hpoint T (hsub (by simp only [mem_Ici, le_refl]))).2.2.2.1
      (Real.exp_pos (-G.outerRate * T)).le
    have hlow : j * Real.exp (-G.outerRate * T) ≤ g T := by
      simpa only [mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one] using hh
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
      ((half_lt_self (by positivity : 0 < j * Real.exp (-G.outerRate * T))).trans_le hlow)
  have hgr (t : ℝ) (ht : t ∈ Ici T) : g t ∈ Ioo 0 (r 0) := by
    have hh := (hpoint t (hsub ht)).1
    have hrp := G.inner_pos.trans hrinit
    exact ⟨hh.1, hh.2.trans_le (by linarith only [hεδ, hδ₂r, hrp])⟩
  have hderiv {W Z : ℝ} (hW : 0 ≤ W) (hZ : 0 ≤ Z) (hWR : W < r 0)
      (hfW : MemLp f p (volume.restrict (Icc 0 W))) (x : WaveState W Z)
      (hx : IsWaveIntegral hW hZ G.charge G.cosmological
        (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
        (horizonWaveVelocity G.mass G.charge G.cosmological Z hc hi hrc hr0)
        (incomingWaveVelocity hWR hp hfW) x)
      (t : ℝ) (ht : T ≤ t) (hgtW : g t ≤ W) (htZ : t ≤ Z) :
      let ν := radialNuField hZ G.charge G.cosmological
        (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) x.1 hx.choose
      HasDerivAt g (-x.2.1 (projIcc 0 W hW (g t)) (projIcc 0 Z hZ t) 0 /
        ν (projIcc 0 W hW (g t)) (projIcc 0 Z hZ t)) t ∧
        ν (projIcc 0 W hW (g t)) (projIcc 0 Z hZ t) < 0 := by
    dsimp only
    have hpt := hpoint t (hsub ht)
    have hgt : g t ∈ Ioo 0 ε := ⟨hpt.1.1, hpt.1.2.trans (half_lt_self hε)⟩
    obtain ⟨ha, _hj, _hD, _hb, _hC, W', Z', hW', hZ', hWR', hfW', y, hy, hgy, hat,
      _hWε, _hfloor, _hhit, _hlneg, hnlo, _hnhi, _hτ, _hlam, _hk, _hscalar,
      _hpre, _hda, _hjac, hgd, _herr⟩ := hwitness (g t) hgt
    have hgtW' : g t ∈ Icc 0 W := ⟨hgt.1.le, hgtW⟩
    have htv : arrival (g t) ∈ Icc 0 Z := ⟨ha.le, hpt.2.1.trans_le htZ⟩
    have he := hy.horizon_overlap hW' hZ' hWR' hW hZ hWR hc hi hrc hr0 hp hfW' hfW hx
      ⟨hgt.1.le, hgy.le⟩ hgtW' ⟨ha.le, hat.le⟩ htv
    have hn := hy.horizon_overlap_nu hW' hZ' hWR' hW hZ hWR hc hi hrc hr0 hp hfW' hfW hx
      ⟨hgt.1.le, hgy.le⟩ hgtW' ⟨ha.le, hat.le⟩ htv
    have hd := (hgd hpt.1.2).1.hasDerivAt
    rw [he.2, hn] at hd
    rw [hn] at hnlo
    have hneg : radialNuField hZ G.charge G.cosmological
        (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) x.1 hx.choose
        ⟨g t, hgtW'⟩ ⟨arrival (g t), htv⟩ < 0 := by
      by_contra hnneg
      have hh := mul_nonneg hgt.1.le (not_lt.1 hnneg)
      nlinarith only [hnlo, hh, mul_pos _hn hj]
    have htmem : t ∈ Icc 0 Z := ⟨hT.le.trans ht, htZ⟩
    rw [projIcc_of_mem hW hgtW', projIcc_of_mem hZ htmem]
    simpa only [hpt.2.1] using And.intro hd hneg
  have hdc : ContinuousOn (deriv g) (Ici T) := by
    intro t ht
    have hpt := hpoint t (hsub ht)
    obtain ⟨_ha, _hj, _hD, _hb, _hC, W, Z, hW, hZ, hWR, hfW, x, hx, hgtW, haZ, _⟩ :=
      hwitness (g t) ⟨hpt.1.1, hpt.1.2.trans (half_lt_self hε)⟩
    have htZ : t < Z := hpt.2.1.symm.trans_lt haZ
    let ν := radialNuField hZ G.charge G.cosmological
      (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) x.1 hx.choose
    let F := fun q => -x.2.1 (projIcc 0 W hW (g q)) (projIcc 0 Z hZ q) 0 /
      ν (projIcc 0 W hW (g q)) (projIcc 0 Z hZ q)
    have hgtc : ContinuousWithinAt g (Ici T) t := (hgc.mono hsub) t ht
    have hFc : ContinuousWithinAt F (Ici T) t := by
      dsimp only [F]
      apply ContinuousWithinAt.div
      · have hh : Continuous (fun q : ℝ × ℝ =>
            -x.2.1 (projIcc 0 W hW q.1) (projIcc 0 Z hZ q.2) 0) := by fun_prop
        exact hh.continuousAt.comp_continuousWithinAt (f := fun q : ℝ => (g q, q))
          (hgtc.prodMk continuousWithinAt_id)
      · have hh : Continuous (fun q : ℝ × ℝ =>
            ν (projIcc 0 W hW q.1) (projIcc 0 Z hZ q.2)) := by fun_prop
        exact hh.continuousAt.comp_continuousWithinAt (f := fun q : ℝ => (g q, q))
          (hgtc.prodMk continuousWithinAt_id)
      · exact (hderiv hW hZ hWR hfW x hx t ht hgtW.le htZ.le).2.ne
    have hgnear : ∀ᶠ q in 𝓝[Ici T] t, g q < W :=
      hgtc.eventually (Iio_mem_nhds hgtW)
    have htnear : ∀ᶠ q in 𝓝[Ici T] t, q < Z :=
      (eventually_lt_nhds htZ).filter_mono nhdsWithin_le_nhds
    apply hFc.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin, hgnear, htnear] with q hq hqW hqZ
      exact (hderiv hW hZ hWR hfW x hx q hq hqW.le hqZ.le).1.deriv
    · exact (hderiv hW hZ hWR hfW x hx t ht hgtW.le htZ.le).1.deriv
  refine ⟨g, hgc.mono hsub, hga.mono hsub, hgl, hdc, hstart, fun t ht =>
    ⟨hgr t ht, (hpoint t (hsub ht)).2.2.2.2.1,
      (hpoint t (hsub ht)).2.2.1.hasDerivAt.differentiableAt,
      (hpoint t (hsub ht)).2.2.2.2.2.1, (hpoint t (hsub ht)).2.2.2.1,
      (hpoint t (hsub ht)).2.2.2.2.2.2.trans (by linarith)⟩, ?_⟩
  intro U V hU hV hUR hUU hfU x hx
  have hbelow (t : ℝ) (ht : T ≤ t) (u : Icc 0 U) (v : Icc 0 V)
      (hu : (u : ℝ) ≤ g t) (hv : (v : ℝ) ≤ t) :
      Y ≤ x.1 u v 0 ∧ ((u : ℝ) = g t → (v : ℝ) = t → x.1 u v 0 = Y) := by
    have hpt := hpoint t (hsub ht)
    have hgε : g t ∈ Ioo 0 ε := ⟨hpt.1.1, hpt.1.2.trans (half_lt_self hε)⟩
    obtain ⟨hgt, _hj, _hD, _hb, _hC, W, Z, hW, hZ, hWR, hfW, z, hz, hgW, htgZ,
      _hWε, _hfloor, hhit, _hlneg, _hnlo, _hnhi, _hτ, _hlam, _hk, _hscalar, hpre, _hrest⟩ :=
      hwitness (g t) hgε
    have huW : (u : ℝ) ∈ Icc 0 W := ⟨u.property.1, hu.trans hgW.le⟩
    have hvZ : (v : ℝ) ∈ Icc 0 Z := ⟨v.property.1, hv.trans (hpt.2.1.symm.trans_le htgZ.le)⟩
    have hvA : (v : ℝ) ≤ arrival (g t) := hv.trans_eq hpt.2.1.symm
    have ho := (hz.horizon_overlap hW hZ hWR hU hV hUR hc hi hrc hr0 hp hfW hfU hx
      huW u.property hvZ v.property).1
    have he : z.1 ⟨u, huW⟩ ⟨v, hvZ⟩ 0 = x.1 u v 0 := congrArg (fun q : WaveVector => q 0) ho
    refine ⟨he ▸ (hpre ⟨u, huW⟩ hu ⟨v, hvZ⟩ hvA).1, ?_⟩
    intro hue hve
    have heu : (⟨u, huW⟩ : Icc 0 W) = ⟨g t, hgε.1.le, hgW.le⟩ := Subtype.ext hue
    have hev : (⟨v, hvZ⟩ : Icc 0 Z) = ⟨arrival (g t), hgt.le, htgZ.le⟩ :=
      Subtype.ext (hve.trans hpt.2.1.symm)
    rw [← he, heu, hev]
    exact hhit
  have hfloor (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ g (max T (v : ℝ))) :
      Y ≤ x.1 u v 0 := (hbelow _ (le_max_left _ _) u v hu (le_max_right _ _)).1
  constructor
  · intro u v hu
    let S := min U (g (max T (v : ℝ)))
    have hS : 0 ≤ S := le_min hU (hgr _ (show T ≤ max T (v : ℝ) from le_max_left _ _)).1.le
    have hSU : S ≤ U := min_le_left _ _
    have hSR : S < r 0 := hSU.trans_lt hUR
    let hfS := hfU.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hSU) le_rfl)
    let y := waveTranslate (a := 0) (U := S) (b := 0) (V := (v : ℝ))
      le_rfl (by linarith) le_rfl (by linarith only [v.property.2]) x
    have hy : IsWaveIntegral hS v.property.1 G.charge G.cosmological
        (incomingWaveCurve hS hSR hp hfS (horizonPhi h r 0))
        (horizonWaveVelocity G.mass G.charge G.cosmological (v : ℝ) hc hi hrc hr0)
        (incomingWaveVelocity hSR hp hfS) y :=
      hx.horizon_prefix hU hV hUR hS v.property.1 hSU v.property.2 hc hi hrc hr0 hp hfU
    have hloy (q : Icc 0 S) (t : Icc 0 (v : ℝ)) : Y ≤ y.1 q t 0 := by
      have hqt : (q : ℝ) ≤ g (max T (t : ℝ)) := q.property.2.trans ((min_le_right _ _).trans
        (hga.antitoneOn (hsub (show T ≤ max T (t : ℝ) from le_max_left _ _))
          (hsub (show T ≤ max T (v : ℝ) from le_max_left _ _)) (max_le_max_left T t.property.2)))
      have hh := hfloor ⟨q, q.property.1, q.property.2.trans hSU⟩
        ⟨t, t.property.1, t.property.2.trans v.property.2⟩ hqt
      change Y ≤ x.1 ⟨0 + q, by simpa using q.property.1, by simpa using q.property.2.trans hSU⟩
        ⟨0 + t, by simpa using t.property.1, by simpa using t.property.2.trans v.property.2⟩ 0
      simpa only [zero_add] using hh
    have hg := (hband p hp f hf₁ hfn₁ hcp S v hS v.property.1 hSR hfS y hy
      (hSU.trans (hUU.trans (min_le_left _ _))) hloy).2.1
      ⟨u, u.property.1, le_min u.property.2 hu⟩ ⟨v, v.property.1, le_rfl⟩
    have hn := hy.horizon_overlap_nu hS v.property.1 hSR hU hV hUR hc hi hrc hr0 hp hfS hfU hx
      ⟨u.property.1, le_min u.property.2 hu⟩ u.property ⟨v.property.1, le_rfl⟩ v.property
    have hl := (hy.horizon_overlap hS v.property.1 hSR hU hV hUR hc hi hrc hr0 hp hfS hfU hx
      ⟨u.property.1, le_min u.property.2 hu⟩ u.property ⟨v.property.1, le_rfl⟩ v.property).2
    rw [hn, hl] at hg
    refine ⟨hfloor u v hu, ?_, hg.2.1⟩
    have hνneg : radialNuField hV G.charge G.cosmological
        (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose u v < 0 := by
      have hh := hg.2.2.1
      have hnpos := mul_pos _hnb (Real.exp_pos (G.outerRate * v))
      linarith only [hh, hnpos]
    rw [abs_of_neg hνneg]
    exact hg.2.2.2.1
  · constructor
    · intro t ht hgtU
      have hgt : g t ∈ Icc 0 U := ⟨(hgr t ht.1).1.le, hgtU⟩
      have htv : t ∈ Icc 0 V := ⟨hT.le.trans ht.1, ht.2⟩
      have hh := (hbelow t ht.1 ⟨g t, hgt⟩ ⟨t, htv⟩ le_rfl le_rfl).2 rfl rfl
      simpa only [intervalExtension_apply, projIcc_of_mem hU hgt, projIcc_of_mem hV htv] using hh
    · intro u v hu hlevel hlam
      have huε : (u : ℝ) < ε / 2 := u.property.2.trans_lt (hUU.trans_lt hUcε)
      obtain ⟨ha, _hj, _hD, _hb, _hC, W, Z, hW, hZ, hWR, hfW, z, hz, huW, haZ,
        _hWε, _hfloor, hhit, hlneg, _⟩ :=
        hwitness u ⟨hu, huε.trans (half_lt_self hε)⟩
      have he := hz.trapped_level_time_unique hW hZ hWR hU hV hUR hc hi hrc hr0 hφ hrd
        hp hfW hfU hx ⟨hu.le, huW.le⟩ u.property ⟨ha.le, haZ.le⟩ v.property hhit hlevel hlneg hlam
      exact (congrArg g he.symm).trans (hinv u ⟨hu, huε⟩)

end CauchyHorizon.Background
