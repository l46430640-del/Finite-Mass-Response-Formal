import CauchyHorizon.Characteristic.BottomConvergence
import CauchyHorizon.Characteristic.HistoryConvergence
import CauchyHorizon.Characteristic.BandCoordinates
import CauchyHorizon.Analysis.EscapingProfile

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CauchyHorizon.Tests

-- The approximating radius functions need not be injective for inverse stability.
example {R : ℕ → C(Icc (0 : ℝ) 1, ℝ)}
    (hlim : Tendsto R atTop (𝓝 ⟨Subtype.val, continuous_subtype_val⟩))
    {u : ℕ → Icc (0 : ℝ) 1} (hhit : ∀ n, R n (u n) = 1 / 2) :
    Tendsto u atTop (𝓝 (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1)) := by
  let χ := fun n => ContinuousMap.const Unit (u n)
  let χ₀ := ContinuousMap.const Unit (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1)
  have hh : Tendsto χ atTop (𝓝 χ₀) := continuous_inverse_coordinates_tendsto
    Subtype.val_injective hlim (fun n _ => hhit n)
  exact (continuous_eval_const ()).tendsto χ₀ |>.comp hh

-- Escaping signed profiles discharge the support and model-amplitude premises at p = 4.
set_option maxHeartbeats 2000000 in
example (B : Background) {U V Y Z ℓ Ch phase : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    {ρ J : ℝ} (hρ : 0 < ρ) (hJ : 0 ≤ J) {P : ℕ → ℝ → ℝ} {m : ℕ → ℝ}
    (hfront : Tendsto m atTop atTop) (hsupport : ∀ n t, t ≤ m n → P n t = 0)
    (hf : ∀ n, MemLp (logarithmicIncoming B.criticalExponent ℓ (P n)) 4 (volume.restrict (Icc 0 U)))
    (hfn : ∀ n, (eLpNorm (logarithmicIncoming B.criticalExponent ℓ (P n)) 4
      (volume.restrict (Icc 0 U))).toReal ≤ J)
    (hlim : Tendsto (fun n => (eLpNorm (logarithmicIncoming B.criticalExponent ℓ (P n)) 4
      (volume.restrict (Icc 0 U))).toReal) atTop (𝓝 0))
    {x : ℕ → WaveState U V} {y : WaveState U V}
    (hx : ∀ n, IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_rfl (hf n) (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR le_rfl (hf n)) (x n))
    (hy : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_rfl (f := 0) (p := 4) MemLp.zero (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR le_rfl (f := 0) (p := 4) MemLp.zero) y)
    (hxr : ∀ n u v, ρ ≤ (x n).1 u v 0) (hyr : ∀ u v, ρ ≤ y.1 u v 0)
    (hY : B.inner < Y) (hYZ : Y < Z) (hZ : Z < B.event) (v : Icc 0 V)
    (χ : ℕ → C(Icc (0 : ℝ) (Z - Y), Icc (0 : ℝ) U))
    (χ₀ : C(Icc (0 : ℝ) (Z - Y), Icc (0 : ℝ) U))
    (hχ : ∀ n w, (x n).1 (χ n w) v 0 = Z - w)
    (hχ₀ : ∀ w, y.1 (χ₀ w) v 0 = Z - w)
    (hχpos : ∀ w, 0 < (χ₀ w : ℝ)) (hL₀ : ∀ w, y.2.1 (χ₀ w) v 0 ≠ 0)
    (W : C(Icc (0 : ℝ) (Z - Y), ℝ)) :
    let ν := fun n => radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_rfl (hf n) (horizonPhi h r 0)) (x n).1 (hx n).choose
    let ν₀ := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_rfl (f := 0) (p := 4) MemLp.zero (horizonPhi h r 0)) y.1 hy.choose
    let ζ := fun n w => (r 0 - (χ n w : ℝ)) * logarithmicIncoming B.criticalExponent ℓ (P n) (χ n w) +
      scalarTransportCorrection hV (ν n) (x n).2.1 (χ n w) v
    let q := fun n w => Real.exp (B.innerRate * v) * (χ n w : ℝ) * ζ n w /
      B.criticalWeight (Z - w) - W w * (Ch * P n (B.outerRate * v + ℓ + phase))
    let q₀ := fun w => Real.exp (B.innerRate * v) * (χ₀ w : ℝ) *
      scalarTransportCorrection hV ν₀ y.2.1 (χ₀ w) v / B.criticalWeight (Z - w)
    let F := fun n w => (-1 / (x n).2.1 (χ n w) v 0) * q n w ^ 2
    let F₀ := fun w => (-1 / y.2.1 (χ₀ w) v 0) * q₀ w ^ 2
    Tendsto χ atTop (𝓝 χ₀) ∧ TendstoUniformly F F₀ atTop ∧
      Tendsto (fun n => ∫ w in (0 : ℝ)..(Z - Y), F n (projIcc 0 (Z - Y) (sub_nonneg.2 hYZ.le) w)) atTop
        (𝓝 (∫ w in (0 : ℝ)..(Z - Y), F₀ (projIcc 0 (Z - Y) (sub_nonneg.2 hYZ.le) w))) := by
  intro ν ν₀ ζ q q₀ F F₀
  have hshift : Tendsto (fun n => m n - ℓ) atTop atTop := by
    apply tendsto_atTop.2
    intro t
    exact ((tendsto_atTop.1 hfront) (t + ℓ)).mono (fun _ hn => by linarith only [hn])
  obtain ⟨hzero, hprofile⟩ := logarithmicIncoming_eventually_zero B.criticalExponent
    hshift hsupport
  have hA : Tendsto (fun n => Ch * P n (B.outerRate * v + ℓ + phase)) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hprofile (B.outerRate * v + phase)] with n hn
    have hh := hn (B.outerRate * v + phase) le_rfl
    rw [show ℓ + (B.outerRate * (v : ℝ) + phase) = B.outerRate * v + ℓ + phase by ring] at hh
    simp only [hh, mul_zero]
  exact IsWaveIntegral.horizon_bottom_tendsto B hU hU1 hV hUR hc hi hrc hr0 hφ hrd hρ hJ
    (p := 4) le_rfl hf hfn hlim
    (fun η hη => (hzero η hη).mono (fun _ hn u hu => hn u hu.1))
    hx hy hxr hyr hY hYZ hZ v χ χ₀ hχ hχ₀ hχpos hL₀ W hA

-- Joint radius-time inversion controls moving curves, without injectivity of the approximants.
example {R : ℕ → C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ × ℝ)}
    (hlim : Tendsto R atTop (𝓝 ⟨fun x => ((x.1 : ℝ), (x.2 : ℝ)), by fun_prop⟩))
    {χ : ℕ → C(Icc (0 : ℝ) 1, Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1)}
    (hhit : ∀ n t, R n (χ n t) = (1 / 2, (t : ℝ))) :
    Tendsto χ atTop (𝓝 ((ContinuousMap.const _ (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1)).prodMk
      (ContinuousMap.id _))) := by
  refine continuous_inverse_coordinates_tendsto ?_ hlim ?_
  · intro x y hxy
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hxy)) (Subtype.ext (congrArg Prod.snd hxy))
  · exact hhit

-- Actual band coordinates supply the moving-history premises, including p=4.
set_option maxHeartbeats 4000000 in
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ : ℝ, ∃ σ : Ioi (0 : ℝ) → ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧
          ∀ (f : ℕ → ℝ → ℝ), (∀ n, MemLp (f n) 4 (volume.restrict (Icc 0 δ))) →
            (∀ n, (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A) →
            Tendsto (fun n => (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u ∈ Icc η δ, f n u = 0) →
            ∀ (U V a b : ℝ) (hUp : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              σ ⟨U, hUp⟩ ≤ a → a ≤ b → b < V →
                ∀ (hfU : ∀ n, MemLp (f n) 4 (volume.restrict (Icc 0 U)))
                  (x : ℕ → WaveState U V) (y : WaveState U V)
                  (_hx : ∀ n, IsWaveIntegral hUp.le hV B.charge B.cosmological
                    (incomingWaveCurve hUp.le hUR le_rfl (hfU n) (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR le_rfl (hfU n)) (x n))
                  (_hy : IsWaveIntegral hUp.le hV B.charge B.cosmological
                    (incomingWaveCurve hUp.le hUR le_rfl (f := 0) (p := 4) MemLp.zero (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR le_rfl (f := 0) (p := 4) MemLp.zero) y),
                  ∀ ρ : ℝ, 0 < ρ → (∀ n u v, ρ ≤ (x n).1 u v 0) → (∀ u v, ρ ≤ y.1 u v 0) →
                    ∃ χ : ℕ → C(Icc a b, Icc (0 : ℝ) U), ∃ χ₀ : C(Icc a b, Icc (0 : ℝ) U),
                      (∀ n t, 0 < (χ n t : ℝ) ∧ (x n).1 (χ n t) (projIcc 0 V hV t) 0 = Y) ∧
                      (∀ t, 0 < (χ₀ t : ℝ) ∧ y.1 (χ₀ t) (projIcc 0 V hV t) 0 = Y) ∧
                      Tendsto χ atTop (𝓝 χ₀) ∧
                      TendstoUniformly
                        (fun n (t : Icc a b) => Real.exp (B.innerRate * (t : ℝ)) *
                          (Y * (x n).2.1 (χ n t) (projIcc 0 V hV t) 1))
                        (fun t : Icc a b => Real.exp (B.innerRate * (t : ℝ)) *
                          (Y * y.2.1 (χ₀ t) (projIcc 0 V hV t) 1)) atTop := by
  intro hi hr0
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ :=
    B.exists_band_coordinates hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₁, T, _τ, σ, hU₁, hUδ, hT, _hτ, hσ, hcoords⟩ := hband Y Z hY hYZ hYR hZ
  refine ⟨min U₁ 1, σ, lt_min hU₁ zero_lt_one, (min_le_left _ _).trans hUδ, ?_⟩
  intro f hf hfn hlim hsupport U V a b hUp hV hUR hUU hσa hab hbV hfU x y hx hy ρ hρ hxr hyr
  have hUU₁ := hUU.trans (min_le_left _ _)
  have hU1 := hUU.trans (min_le_right _ _)
  have hUδ' := hUU₁.trans hUδ
  have ha : 0 ≤ a := hT.le.trans ((hσ ⟨U, hUp⟩).trans hσa)
  let v := fun t : Icc a b => (⟨t, ha.trans t.property.1, t.property.2.trans hbV.le⟩ : Icc 0 V)
  have hv (t : Icc a b) : projIcc 0 V hV (t : ℝ) = v t := projIcc_of_mem hV (v t).property
  have hseq (n : ℕ) := hcoords 4 le_rfl (f n) (hf n) (hfn n) U V hUp.le hV hUR hUU₁
    (hfU n) (x n) (hx n) hUp a b hσa hab hbV
  choose ψ hψc _hψd hψ using hseq
  obtain ⟨ψ₀, hψ₀c, _hψ₀d, hψ₀⟩ := hcoords 4 le_rfl 0 MemLp.zero (by simpa using hA)
    U V hUp.le hV hUR hUU₁ MemLp.zero y hy hUp a b hσa hab hbV
  have hpt (n : ℕ) (t : Icc a b) := hψ n (Y, t) ⟨⟨le_rfl, hYZ.le⟩, t.property⟩
  have hpt₀ (t : Icc a b) := hψ₀ (Y, t) ⟨⟨le_rfl, hYZ.le⟩, t.property⟩
  let χ := fun n => (⟨fun t : Icc a b => ⟨ψ n (Y, t), (hpt n t).1.1.le, (hpt n t).1.2.le⟩,
    ((hψc n).comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun t => ⟨⟨le_rfl, hYZ.le⟩, t.property⟩)).subtype_mk _⟩ : C(Icc a b, Icc (0 : ℝ) U))
  let χ₀ : C(Icc a b, Icc (0 : ℝ) U) :=
    ⟨fun t => ⟨ψ₀ (Y, t), (hpt₀ t).1.1.le, (hpt₀ t).1.2.le⟩,
      (hψ₀c.comp_continuous (continuous_const.prodMk continuous_subtype_val)
        (fun t => ⟨⟨le_rfl, hYZ.le⟩, t.property⟩)).subtype_mk _⟩
  have hχ (n : ℕ) (t : Icc a b) : (x n).1 (χ n t) (v t) 0 = Y := by
    have hu : projIcc 0 U hUp.le (ψ n (Y, t)) = χ n t := projIcc_of_mem hUp.le (χ n t).property
    simpa only [hu, hv] using (hpt n t).2.1
  have hχ₀ (t : Icc a b) : y.1 (χ₀ t) (v t) 0 = Y := by
    have hu : projIcc 0 U hUp.le (ψ₀ (Y, t)) = χ₀ t := projIcc_of_mem hUp.le (χ₀ t).property
    simpa only [hu, hv] using (hpt₀ t).2.1
  have hnorm (n : ℕ) := scalar_prefix_norm_le hUδ' (hf n)
  have hsmall := IsWaveIntegral.horizon_scalar_history_tendsto B hUp.le hU1 hV hUR ha hab hbV.le
    hc hi hrc hr0 hφ hrd hρ hA (p := 4) le_rfl hfU (fun n => (hnorm n).trans (hfn n))
    (squeeze_zero (fun _ => ENNReal.toReal_nonneg) hnorm hlim)
    (fun η hη => (hsupport η hη).mono (fun n hn u hu => hn u ⟨hu.1, hu.2.trans hUδ'⟩))
    hx hy hxr hyr χ χ₀ hχ hχ₀ (fun t => (hpt₀ t).1.1)
  refine ⟨χ, χ₀, ?_, ?_, hsmall.1, ?_⟩
  · intro n t
    exact ⟨(hpt n t).1.1, (hv t) ▸ hχ n t⟩
  · intro t
    exact ⟨(hpt₀ t).1.1, (hv t) ▸ hχ₀ t⟩
  · simpa only [hv] using hsmall.2.1

end CauchyHorizon.Tests
