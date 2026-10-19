import CauchyHorizon.Analysis.PhaseEnergy
import CauchyHorizon.Characteristic.OuterPhase

open Set MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace CauchyHorizon.Tests

-- Constant translations retain the sharp displacement-squared factor, including zero displacement.
example {a d h l S : ℝ} (ha : 0 < a) (hlS : l ≤ S) (P D : ℝ →ᵇ ℝ)
    (hd : ∀ x, HasDerivAt P (D x) x) (hD : Integrable (fun x => D x ^ 2)) :
    (∫ t in l..S, (P (a * t + d + h) - P (a * t + d)) ^ 2) ≤
      h ^ 2 / a * ∫ x, D x ^ 2 := by
  have hdφ (t : ℝ) (_ht : t ∈ Icc l S) : HasDerivAt (fun w => a * w + d) a t :=
    (((hasDerivAt_id t).const_mul a).add_const d).congr_deriv (by simp)
  have hdψ (t : ℝ) (ht : t ∈ Icc l S) : HasDerivAt (fun w => a * w + d + h) a t :=
    (hdφ t ht).add_const h
  have hh := (phaseChange_l2_bound hlS ha (abs_nonneg h) (by fun_prop) (by fun_prop)
    hdφ hdψ (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun t _ => by simp only [add_sub_cancel_left, le_refl]) P.continuous D.continuous hd hD).2
  simpa only [sq_abs] using hh

-- All phase premises come from the actual p = 4 near-event curve; the cutoff precedes the data.
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
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ₀ α : ℝ, 0 < δ₀ ∧ 0 < α ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ Y T : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
        Y = B.event - α * δ ∧ Y ∈ Ioo B.inner B.event ∧ 0 < T ∧ (∀ ε, T ≤ τ ε) ∧
        ∀ (f : ℝ → ℝ), MemLp f 4 (volume.restrict (Icc 0 δ)) →
          (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧
            (∀ t ∈ Ici T, 0 < g t ∧
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
                (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (_hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl hfU) x),
                g t ≤ U → t ≤ V → x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 = Y) ∧
            ∀ (ε : Ioi (0 : ℝ)) (ℓ : ℝ) (P D : ℝ →ᵇ ℝ),
              (∀ x, HasDerivAt P (D x) x) → Integrable (fun x => D x ^ 2) →
              let ψ := fun t => ℓ - Real.log (g t)
              let φ := fun t => B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Y)
              ∀ l S : ℝ, τ ε ≤ l → l ≤ S →
                MemLp (fun t => P (ψ t) - P (φ t)) 2 (volume.restrict (Ici l)) ∧
                (∫ t in Ici l, (P (ψ t) - P (φ t)) ^ 2) ≤
                  (2 * (ε : ℝ) ^ 2 / B.outerRate) * ∫ x, D x ^ 2 ∧
                (∫ t in l..S, ((7 / 4 : ℝ) * terminalGreen (by norm_num : (0 : ℝ) < 7 / 4) P (ψ t) - P (φ t)) ^ 2) ≤
                  (4 / B.outerRate) * ((4 / 7 : ℝ) ^ 2 + (ε : ℝ) ^ 2) * ∫ x, D x ^ 2 := by
  intro hi hr0 cν
  have ha := B.outerRate_pos
  obtain ⟨δ₀, α, β, η, hδ₀, _hδ₀r, hα, _hβ, _hη, hfamily⟩ :=
    B.exists_outer_phase_family hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ₀, α, hδ₀, hα, ?_⟩
  intro δ hδ hδδ
  obtain ⟨Y, T, τ₀, hYeq, hY, hT, hτ₀, hsolve⟩ := hfamily δ hδ hδδ
  let e := fun ε : Ioi (0 : ℝ) => (⟨min (ε : ℝ) (B.outerRate / 2),
    lt_min ε.property (half_pos ha)⟩ : Ioi (0 : ℝ))
  let τ := fun ε => τ₀ (e ε)
  refine ⟨Y, T, τ, hYeq, hY, hT, fun ε => hτ₀ (e ε), ?_⟩
  intro f hf hfn
  obtain ⟨g, hgc, _hga, _hgl, hpoint⟩ := hsolve 4 le_rfl f hf hfn
  refine ⟨g, hgc, ?_, ?_⟩
  · intro t ht
    refine ⟨(hpoint t ht).1.1, ?_⟩
    intro U V hU hV hUR hfU x hx hgu htv
    exact ((hpoint t ht).2.2.2.2.2.2.2 U V hU hV hUR hfU x hx hgu htv).1
  · intro ε ℓ P D hd hD ψ φ l S hl hlS
    have hsub : Ici l ⊆ Ici T := fun _ ht => (hτ₀ (e ε)).trans (hl.trans ht)
    have hψc : ContinuousOn ψ (Ici l) :=
      continuousOn_const.sub ((hgc.mono hsub).log (fun t ht => (hpoint t (hsub ht)).1.1.ne'))
    have hφc : ContinuousOn φ (Ici l) := by dsimp only [φ]; fun_prop
    have hdψ (t : ℝ) (ht : t ∈ Ici l) : HasDerivAt ψ (-deriv g t / g t) t := by
      have hpt := hpoint t (hsub ht)
      simpa only [neg_div] using (hpt.2.1.hasDerivAt.log hpt.1.1.ne').const_sub ℓ
    have hdφ (t : ℝ) (_ht : t ∈ Ici l) : HasDerivAt φ B.outerRate t := by
      exact (((((hasDerivAt_id t).const_mul B.outerRate).add_const ℓ).add_const (Real.log cν)).sub_const
        (Real.log (B.z Y))).congr_deriv (by simp)
    have hphase (t : ℝ) (ht : t ∈ Ici l) :
        |ψ t - φ t| ≤ ε ∧ B.outerRate / 2 ≤ -deriv g t / g t := by
      have hpt := hpoint t (hsub ht)
      have hh := hpt.2.2.2.2.2.2.1 (e ε) (hl.trans ht)
      have he : ψ t - φ t = Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t)))) := by
        rw [Real.log_div (B.z_pos hY).ne' (mul_pos hpt.1.1 (mul_pos (Real.exp_pos _) (Real.exp_pos _))).ne',
          Real.log_mul hpt.1.1.ne' (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne',
          Real.log_mul (Real.exp_pos _).ne' (Real.exp_ne_zero _)]
        dsimp only [ψ, φ]
        simp only [cν, Real.log_exp]
        ring
      have hclose := ((le_add_of_nonneg_right (abs_nonneg _)).trans_lt hh).le.trans
        (show (e ε : ℝ) ≤ ε from min_le_left _ _)
      have hspeed := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt hh |>.trans_le
        (show (e ε : ℝ) ≤ B.outerRate / 2 from min_le_right _ _)
      refine ⟨he ▸ hclose, ?_⟩
      have hh' := (abs_lt.1 hspeed).1
      linarith only [hh']
    have hbφ (t : ℝ) (_ht : t ∈ Ici l) : B.outerRate / 2 ≤ B.outerRate := half_le_self ha.le
    have h₁ := phaseChange_l2_halfline (half_pos ha) ε.property.le hφc hψc hdφ hdψ hbφ
      (fun t ht => (hphase t ht).2) (fun t ht => (hphase t ht).1) P.continuous D.continuous hd hD
    have h₂ := (terminalGreen_phase_error_energy hlS (half_pos ha) ε.property.le
      (by norm_num : (0 : ℝ) < 7 / 4) (hφc.mono Icc_subset_Ici_self) (hψc.mono Icc_subset_Ici_self)
      (fun t ht => hdφ t ht.1) (fun t ht => hdψ t ht.1) (fun t ht => hbφ t ht.1)
      (fun t ht => (hphase t ht.1).2) (fun t ht => (hphase t ht.1).1) P D hd hD).2
    refine ⟨h₁.1, ?_, ?_⟩
    · exact h₁.2.trans_eq (by ring)
    · convert h₂ using 1
      ring

end CauchyHorizon.Tests
