import CauchyHorizon.Characteristic.OuterArrival
import CauchyHorizon.Analysis.ArrivalEnergy

/-! The direct incoming radiation on an actual fixed-radius arrival curve. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 800000 in
theorem exists_outer_profile_trace_energy (G : Background) {s H dH A b k : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event)
    (hA : 0 ≤ A) (hb : 0 < b) (hb1 : b < 1) (hcrit : k = G.outerRate * b) (hks : k ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hout
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y T J η C : ℝ, 0 < δ ∧ δ ≤ r 0 / 4 ∧ Y ∈ Ioo G.inner G.event ∧
      0 ≤ T ∧ 0 < J ∧ J < δ / 2 ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (ℓ : ℝ) (B : ℝ →ᵇ ℝ)
        (_hB : Integrable (fun t => B t ^ 2))
        (_hf : MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 δ))),
        (eLpNorm (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        k ≤ G.outerRate * (1 - 1 / p.toReal) →
        ∃ g : ℝ → ℝ, ContinuousOn g (Ioi T) ∧ StrictAntiOn g (Ioi T) ∧ Tendsto g atTop (𝓝 0) ∧
          (∀ l w : ℝ, T < l → l ≤ w →
            (∫ t in l..w, (g t * Real.exp (k * t) * (r 0 - g t) *
              logarithmicIncoming b ℓ B (g t)) ^ 2) ≤ C * ∫ t, B t ^ 2) ∧
          ∀ t ∈ Ioi T, 0 < g t ∧ g t * Real.exp (G.outerRate * t) ≤ J ∧ η ≤ -deriv g t / g t ∧
            ∃ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hfU : MemLp (logarithmicIncoming b ℓ B) p (volume.restrict (Icc 0 U)))
              (x : WaveState U V)
              (hx : IsWaveIntegral hU hV G.charge G.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
                (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR hp hfU) x) (u : Icc 0 U) (v : Icc 0 V),
              (u : ℝ) = g t ∧ (v : ℝ) = t ∧ (u : ℝ) ∈ Ioo 0 U ∧ (v : ℝ) ∈ Ioo 0 V ∧
                x.1 u v 0 = Y ∧ U * Real.exp (G.outerRate * V) = δ ∧
                let ν := radialNuField hV G.charge G.cosmological
                  (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose
                HasDerivAt g (-x.2.1 u v 0 / ν u v) t ∧
                  (-ν u v) * (-deriv g t) = -x.2.1 u v 0 := by
  dsimp only
  have hk : 0 < k := by rw [hcrit]; exact mul_pos G.outerRate_pos hb
  have hka : k < G.outerRate := by rw [hcrit]; nlinarith only [G.outerRate_pos, hb1]
  obtain ⟨δ, Y, T, j, J, η, Q, ε, hδ, hδr, hY, hT, hj, hJ, hJδ, hη, hQ, hε, hsolve⟩ :=
    G.exists_outer_arrival hs hH hdH hdHR hc hout hrc hrb hrd hrdec hOut hk.le hka hks hA
  let C := (b * r 0 * J ^ b) ^ 2 / η
  refine ⟨δ, Y, T, J, η, C, hδ, hδr, hY, hT, hJ, hJδ, hη, by dsimp only [C]; positivity, ?_⟩
  intro p hp ℓ B hB hf hfn hkp
  obtain ⟨g, inv, hgc, hga, hgl, _hic, _hil, _hir, _hil', hpoint⟩ :=
    hsolve p hp (logarithmicIncoming b ℓ B) hf hfn hkp
  have hdiff (t : ℝ) (ht : t ∈ Ioi T) : DifferentiableAt ℝ g t := by
    obtain ⟨U, V, hU, hV, hUR, hfU, x, hx, u, v,
      _hu, _hv, _hui, _hvi, _hr, _hw, hd, _hjac⟩ := (hpoint t ht).2.2.2.2.2
    exact hd.differentiableAt
  refine ⟨g, hgc, hga, hgl, ?_, fun t ht =>
    ⟨(hpoint t ht).1, (hpoint t ht).2.2.1, (hpoint t ht).2.2.2.1, (hpoint t ht).2.2.2.2.2⟩⟩
  intro l w hl hw
  have hsub : Icc l w ⊆ Ioi T := fun _ ht => hl.trans_le ht.1
  have hgr (t : ℝ) (ht : t ∈ Icc l w) : g t ≤ r 0 := by
    have hpt := hpoint t (hsub ht)
    have he : 1 ≤ Real.exp (G.outerRate * t) := Real.one_le_exp_iff.2
      (mul_nonneg G.outerRate_pos.le (hT.trans (hsub ht).le))
    have hh : g t ≤ J := (le_mul_of_one_le_right hpt.1.le he).trans hpt.2.2.1
    have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
    linarith only [hh, hJδ, hδr, hrp]
  exact logarithmicIncoming_trace_energy hw hb hJ hη hcrit (hgc.mono hsub)
    (fun t ht => hdiff t (hsub ht)) (fun t ht => (hpoint t (hsub ht)).1) hgr
    (fun t ht => (hpoint t (hsub ht)).2.2.1) (fun t ht => (hpoint t (hsub ht)).2.2.2.1) B hB

end CauchyHorizon.Background
