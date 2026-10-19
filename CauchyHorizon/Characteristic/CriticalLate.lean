import CauchyHorizon.Characteristic.CommonExistence
import CauchyHorizon.Characteristic.LateScalarClosure
import CauchyHorizon.Characteristic.LateConformal
import CauchyHorizon.Reduced.LongitudinalTail
import CauchyHorizon.Characteristic.LateLapse
import CauchyHorizon.Reduced.ConformalRemainder
import CauchyHorizon.Analysis.CornerWeight
import CauchyHorizon.Reduced.BoundaryTrace
import CauchyHorizon.Reduced.RadialBoundary
import CauchyHorizon.Reduced.ScalarBoundary
import CauchyHorizon.Reduced.BoundaryConstraint
import CauchyHorizon.Reduced.BoundarySign
import CauchyHorizon.Characteristic.ZeroScalarGlobal
import CauchyHorizon.Reduced.AmplitudeTrace
import CauchyHorizon.Reduced.BoundaryConvergence
import CauchyHorizon.Reduced.RadialConvergence
import CauchyHorizon.Reduced.MassCoefficient
import CauchyHorizon.Characteristic.FiniteStability
import CauchyHorizon.Characteristic.EarlyRadiationEnergy
import CauchyHorizon.Characteristic.GammaChart
import CauchyHorizon.Characteristic.FullRadiationEnergy
import CauchyHorizon.Characteristic.OpticalFluxClosure
import CauchyHorizon.Reduced.RadiationHalfline
import CauchyHorizon.Characteristic.MassBound
import CauchyHorizon.Characteristic.NestedRadiusSections
import CauchyHorizon.Characteristic.AuxiliaryRadiusCharts
import CauchyHorizon.Characteristic.CommonRadiation
import CauchyHorizon.Characteristic.AuxiliaryRadiationHalfline
import CauchyHorizon.Characteristic.AuxiliaryRadiationTail
import CauchyHorizon.Characteristic.GammaTransmissionTail
import CauchyHorizon.Characteristic.RadiationComparison
import CauchyHorizon.Characteristic.MassDensityComparison
import CauchyHorizon.Characteristic.MassResponse
import CauchyHorizon.Characteristic.MassProfile

/-! A compatible critical development with closed late geometry and radiation energy. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace CauchyHorizon.Background

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 4096 in
theorem exists_critical_late_wave (B : Background) {s l H Hlo dH A Apt Ebudget : ℝ} {h r : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 4 ≤ p) (hpfin : p ≠ ∞)
    (hcrit : B.innerRate = (1 - 1 / p.toReal) * B.outerRate)
    (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hHlo : 0 < Hlo) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hApt : 0 ≤ Apt)
    (hEbudget : 0 ≤ Ebudget)
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hlo : ∀ t ∈ Ici (0 : ℝ), Hlo * Real.exp (-l * t) ≤ h t)
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (Ucap : ℝ) (hUcap : 0 < Ucap) :
    let hi := horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ U Y Yr β L τ j D cL N C Hs ηL Ldec ηO Odec ηE Edec Rmatch Olo Ohi Tr jr Dr ηr Cr E₀ E₁ F₀ F₁ Drlo Drhi Er₀ Er₁ Mbound Ed : ℝ,
      0 < δ ∧ B.inner < Y ∧ 0 < β ∧ β < 1 / 8 ∧ 0 < L ∧ 0 < τ ∧
      0 < j ∧ 0 < D ∧ 0 < cL ∧ cL < B.innerRate ∧ l < 2 * s + cL ∧ 0 < N ∧ 0 < C ∧
      0 < Hs ∧ N < Hs / 2 ∧ 0 < ηL ∧ 0 < Ldec ∧ 0 < ηO ∧ 0 < Odec ∧ 0 < ηE ∧ 0 < Edec ∧
      0 < Rmatch ∧ 0 < Olo ∧ 0 < Ohi ∧
      Yr ∈ Ioo B.inner B.event ∧ Yr < Y ∧ 0 < Tr ∧ 0 < jr ∧ 0 < Dr ∧ 0 < ηr ∧ 0 < Cr ∧
      0 ≤ E₀ ∧ 0 ≤ E₁ ∧ 0 ≤ F₀ ∧ 0 ≤ F₁ ∧ 0 < Drlo ∧ 0 < Drhi ∧ 0 ≤ Er₀ ∧ 0 ≤ Er₁ ∧ 0 ≤ Mbound ∧ 0 ≤ Ed ∧
      L * j ^ (-(τ / (B.outerRate / (1 + β)))) * U ^ (τ / (B.outerRate / (1 + β))) <
        (B.innerRate - cL) / 2 ∧
      U ≤ Ucap ∧
      ∃ hU : 0 < U, ∃ hUδ : U ≤ δ, ∃ hUR : U < r 0,
      ∃ Laux : ℝ, 0 < Laux ∧
      ∃ Taux : Ioo B.inner Yr → ℝ, (∀ Y', 0 < Taux Y') ∧
      ∃ Saux : Ioo B.inner Yr → ℝ, (∀ Y', 0 < Saux Y') ∧
      ∃ Tmatch : Ioo B.inner Yr → ℝ, (∀ Y', 0 < Tmatch Y') ∧
      ∃ hm : B.criticalExponent < 1,
      ∀ f : ℕ → ℝ → ℝ, ∀ hf : ∀ n, MemLp (f n) p (volume.restrict (Icc 0 δ)),
        (∀ n, (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal ≤ A) →
        (∀ n, ∀ᵐ t ∂volume.restrict (Icc 0 δ), |f n t| ≤ Apt * t ^ (-1 / p.toReal)) →
        let hfU := fun n => (hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hUδ) le_rfl)
        ∃ arrival : ℕ → ℝ → ℝ, ∃ X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T,
          (∀ n, ContinuousOn (arrival n) (Ioc 0 U) ∧ StrictAntiOn (arrival n) (Ioc 0 U) ∧
            Tendsto (arrival n) (𝓝[>] (0 : ℝ)) atTop ∧ ∀ u ∈ Ioc 0 U, 0 < arrival n u) ∧
          (∀ n u, u ∈ Ioc 0 U → j ≤ u * Real.exp (B.outerRate * arrival n u) ∧
            u * Real.exp (B.outerRate * arrival n u) ≤ D) ∧
          (∀ n (T : Ici (0 : ℝ)), IsWaveIntegral hU.le T.property B.charge B.cosmological
            (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
            (incomingWaveVelocity hUR hp (hfU n)) (X n T)) ∧
          (∀ n T q v, 3 * B.inner / 4 ≤ (X n T).1 q v 0) ∧
          (∀ n (T : Ici (0 : ℝ)) (u : Icc 0 U), 0 < (u : ℝ) → ∀ v : Icc 0 (T : ℝ),
            ((v : ℝ) = arrival n u → (X n T).1 u v 0 = Y) ∧
            ((v : ℝ) ≤ arrival n u → Y ≤ (X n T).1 u v 0)) ∧
          (∀ (Y' : Ioo B.inner Yr) (n : ℕ), ∃ ψ : ℝ → ℝ,
            ContinuousOn ψ (Ici (Taux Y')) ∧
            (∀ t ∈ Ici (Taux Y'), t < ψ t ∧ ψ t ≤ (1 + β) * t) ∧
            ∀ (V : Ici (0 : ℝ)) (t : ℝ), Taux Y' ≤ t → ψ t ≤ V → ∀ u : Icc 0 U,
              (X n V).1 u (projIcc 0 (V : ℝ) V.property t) 0 = Yr →
                (X n V).1 u (projIcc 0 (V : ℝ) V.property (ψ t)) 0 = Y' ∧
                ∀ hr : ∀ q v, (X n V).1 q v 0 ≠ 0,
                  let ν := radialNuField V.property B.charge B.cosmological
                    (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n V).1 hr
                  let v := projIcc 0 (V : ℝ) V.property (ψ t)
                  Real.exp (-1) * (-B.F Y') / B.outerRate ≤ (u : ℝ) * (-ν u v) ∧
                  (u : ℝ) * (-ν u v) ≤ Real.exp 1 * (-B.F Y') / B.outerRate ∧
                  0 < -(X n V).2.1 u v 0 ∧ -(X n V).2.1 u v 0 ≤ Laux * ((Y' : ℝ) - B.inner)) ∧
          (∀ (ℓ : ℕ → ℝ) (P : ℕ → ℝ →ᵇ ℝ),
            (∀ n, f n = logarithmicIncoming (1 - 1 / p.toReal) (ℓ n) (P n)) →
            (∀ n, Integrable (fun t => P n t ^ 2)) →
            (∀ n, (∫ t, P n t ^ 2) ≤ Ebudget) →
            ∃ g : ℕ → ℝ → ℝ,
              (∀ n, ContinuousOn (g n) (Ici Tr) ∧ StrictAntiOn (g n) (Ici Tr) ∧
                Tendsto (g n) atTop (𝓝 0) ∧ ContinuousOn (deriv (g n)) (Ici Tr) ∧ U < g n Tr ∧
                ∀ t ∈ Ici Tr, 0 < g n t ∧ g n t * Real.exp (B.outerRate * t) ≤ Dr ∧
                  DifferentiableAt ℝ (g n) t ∧ ηr ≤ -deriv (g n) t / g n t ∧
                  jr ≤ g n t * Real.exp (B.outerRate * t) ∧ -deriv (g n) t / g n t ≤ Cr) ∧
              (∀ (Y' : Ioo B.inner Yr) (n : ℕ) (V : Ici (0 : ℝ))
                (hr : ∀ q v, (X n V).1 q v 0 ≠ 0),
                AuxiliaryRadiationCharts B hU.le (X n V)
                  (radialNuField V.property B.charge B.cosmological
                    (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n V).1 hr)
                  (g n) Tr β Y' Laux (Saux Y')) ∧
              (∀ (m : ℕ → ℝ) (Q : ℕ → ℝ →ᵇ ℝ), P 0 = 0 →
                (∀ n t, HasDerivAt (P n) (Q n t) t) → (∀ n, Integrable (fun t => Q n t ^ 2)) →
                Tendsto (fun n => ∫ t, Q n t ^ 2) atTop (𝓝 0) →
                Tendsto (fun n => m n - ℓ n) atTop atTop → (∀ n t, t ≤ m n → P n t = 0) →
                Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
                (∀ (Y' : Ioo B.inner Yr) (lY : ℝ), Tmatch Y' ≤ lY →
                  let cν := Real.exp (∫ t in Ioi 0,
                    2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
                  let Ch := r 0 / (B.event * cν ^ B.criticalExponent)
                  let cθ := extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - Y') * Ch
                  let cζ := extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - Y') * Ch
                  ∃ gY θ ζ : ℕ → ℝ → ℝ,
                    (∀ n, ContinuousOn (gY n) (Ici lY) ∧ ContinuousOn (θ n) (Ici lY) ∧
                      ContinuousOn (ζ n) (Ici lY) ∧ MemLp (θ n) 2 (volume.restrict (Ici lY)) ∧
                        MemLp (ζ n) 2 (volume.restrict (Ici lY))) ∧
                    (∀ n t, lY ≤ t → ∀ (V : Ici (0 : ℝ)) (htV : t ∈ Icc 0 (V : ℝ)),
                      let u := projIcc 0 U hU.le (gY n t)
                      let v : Icc 0 (V : ℝ) := ⟨t, htV⟩
                      gY n t ∈ Ioo 0 U ∧ (X n V).1 u v 0 = Y' ∧
                        θ n t = Real.exp (B.innerRate * t) * ((Y' : ℝ) * (X n V).2.1 u v 1) ∧
                        ∀ hr : ∀ q v, (X n V).1 q v 0 ≠ 0,
                          let ν := radialNuField V.property B.charge B.cosmological
                            (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n V).1 hr
                          ζ n t = Real.exp (B.innerRate * t) * gY n t *
                            ((r 0 - gY n t) * f n (gY n t) +
                              scalarTransportCorrection V.property ν (X n V).2.1 u v) / B.criticalWeight Y') ∧
                    (∀ n,
                      let A := fun t => B.criticalWeight Y' /
                        (Real.exp (-1) * (-B.F Y') / B.outerRate) * |ζ n t|
                      ContinuousOn A (Ici lY) ∧ MemLp A 2 (volume.restrict (Ici lY)) ∧
                        (∀ (V : Ici (0 : ℝ)) (hr : ∀ q v, (X n V).1 q v 0 ≠ 0),
                          let ν := radialNuField V.property B.charge B.cosmological
                            (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n V).1 hr
                          ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 (V : ℝ), lY ≤ v →
                            (X n V).1 (projIcc 0 U hU.le u) v 0 = Y' →
                              Real.exp (B.innerRate * v) *
                                |(X n V).1 (projIcc 0 U hU.le u) v 0 * (X n V).2.2 u v 1| ≤
                                  (-ν (projIcc 0 U hU.le u) v) * A v) ∧
                        (∀ (V : Ici (0 : ℝ)) (l' : Icc 0 (V : ℝ)), lY ≤ l' → ∀ b₀ : Icc 0 (V : ℝ),
                          max (l' : ℝ) Tr ≤ (b₀ : ℝ) / (1 + β) → Saux Y' ≤ b₀ →
                            AuxiliaryRadiationEstimate B hU.le V.property (X n V) (gY n) (g n) β Y' Laux
                              l' b₀ A) ∧
                        ∀ l' b₀ : ℝ, lY ≤ l' → max l' Tr ≤ b₀ / (1 + β) → Saux Y' ≤ b₀ →
                          AuxiliaryRadiationHalfline B hU.le (X n) (gY n) (g n) β Y' Laux l' b₀ A) ∧
                    (∀ d : ℝ,
                      (∀ n, MemLp (fun t => θ n t - θ 0 t - cθ * P n (B.outerRate * t + ℓ n + d))
                          2 (volume.restrict (Ici lY)) ∧
                        MemLp (fun t => ζ n t - ζ 0 t - cζ * P n (B.outerRate * t + ℓ n + d))
                          2 (volume.restrict (Ici lY))) ∧
                      Tendsto (fun n => ∫ t in Ici lY,
                        (θ n t - θ 0 t - cθ * P n (B.outerRate * t + ℓ n + d)) ^ 2 +
                          (ζ n t - ζ 0 t - cζ * P n (B.outerRate * t + ℓ n + d)) ^ 2) atTop (𝓝 0)) ∧
                    AuxiliaryRadiationTail B hU.le X gY g β Y' Laux lY Tr (Saux Y')
                      (cζ ^ 2 * (Ebudget / B.outerRate)) (Er₀ + Er₁ * Ebudget)) ∧
                let cν := Real.exp (∫ t in Ioi 0,
                  2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
                let Ch := r 0 / (B.event * cν ^ B.criticalExponent)
                RadiationGammaTransmissionTail B hU.le X g
                  (fun n t => P n (B.outerRate * t + ℓ n)) β (B.transmission hm * Ch) ∧
                ∀ ε (hε : 0 < ε), ε ≤ U →
                  let F := radiationComparisonRow hε.le B.innerRate (B.transmission hm * Ch)
                    X (fun n t => P n (B.outerRate * t + ℓ n))
                  ((∀ n, MemLp (F n) 2 (volume.restrict (Ici 0))) ∧
                    Tendsto (fun n => ∫ t in Ici (0 : ℝ), ‖F n t‖ ^ 2) atTop (𝓝 0)) ∧
                  ∃ hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0,
                    let ν := fun n (V : Ici (0 : ℝ)) => radialNuField V.property B.charge B.cosmological
                      (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n V).1 (hr n V)
                    RadiationMassDensity hε.le B.innerRate (B.transmission hm * Ch) X ν
                      (fun n t => P n (B.outerRate * t + ℓ n)) ∧
                    RadiationMassResponse hε.le B.innerRate (B.transmission hm * Ch)
                      B.charge B.cosmological X ν hr (fun n t => P n (B.outerRate * t + ℓ n)) ∧
                    RadiationMassProfile hε.le B.innerRate B.outerRate (B.transmission hm * Ch)
                      B.charge B.cosmological X ν hr ℓ (fun n => P n)) ∧
              (∀ n (V : Ici (0 : ℝ)),
                ∃ (w : C(Icc 0 (V : ℝ), ℝ)) (hw0 : ∀ v, 0 ≤ w v),
                  (∀ v, w v = g n (max Tr (v : ℝ))) ∧ Antitone w ∧
                  (∀ v : Icc 0 (V : ℝ), Tr ≤ v → g n v ≤ U →
                    (X n V).1 (projIcc 0 U hU.le (g n v)) v 0 = Yr) ∧
                  RadiationGammaCharts hU.le V.property (X n V) (g n) Tr (1 + β) ηr Cr Yr ∧
                  (∀ t : ℝ, Tr ≤ t → g n t ≤ U → t ≤ V → arrival n (g n t) < t) ∧
                  (∀ t : ℝ, Tr ≤ t → g n t ≤ U → (1 + β) * t ≤ V →
                    let u := projIcc 0 U hU.le (g n t)
                    let a := projIcc 0 (V : ℝ) V.property t
                    Drlo * g n t ≤ -(X n V).2.1 u a 0 / Real.exp ((X n V).1 u a 2) ∧
                    -(X n V).2.1 u a 0 / Real.exp ((X n V).1 u a 2) ≤ Drhi * g n t ∧
                    (∫ v in t..(1 + β) * t, intervalExtension V.property ((X n V).1 u) v 0 *
                      (intervalExtension V.property ((X n V).2.1 u) v 1) ^ 2 /
                        (-intervalExtension V.property ((X n V).2.1 u) v 0)) ≤ 1 / 16 ∧
                    ∀ hr : ∀ q v, (X n V).1 q v 0 ≠ 0,
                      let ν := radialNuField V.property B.charge B.cosmological
                        (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n V).1 hr
                      ∀ a' b' : Icc 0 (V : ℝ), t ≤ a' → a' ≤ b' → (b' : ℝ) ≤ (1 + β) * t →
                        B.inner / 2 ≤ (X n V).1 u b' 0 ∧
                        |ν u b'| ≤ (2 * Real.exp 2) * (-ν u a') * Real.exp (-2 * B.innerRate * ((b' : ℝ) - a')) ∧
                        |(X n V).2.1 u b' 0| ≤ (Real.exp (2 + 1 / 16) * (-(X n V).2.1 u a' 0)) *
                          Real.exp (-2 * B.innerRate * ((b' : ℝ) - a'))) ∧
                  (∀ t : ℝ, Tr ≤ t → g n t ≤ U → ∀ v : Icc 0 (V : ℝ), (1 + β) * t ≤ v →
                    let u := projIcc 0 U hU.le (g n t)
                    (∫ w in t..(v : ℝ), intervalExtension V.property ((X n V).1 u) w 0 *
                      (intervalExtension V.property ((X n V).2.1 u) w 1) ^ 2 /
                        (-intervalExtension V.property ((X n V).2.1 u) w 0)) ≤ 1 / 8) ∧
                  (let S := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 (V : ℝ)) U)
                      (fun _ => hU.le) 0 B.innerRate 0 (X n V);
                    (∫ t in (0 : ℝ)..(V : ℝ), (S (projIcc 0 (V : ℝ) V.property t)) ^ 2) ≤
                      Er₀ + Er₁ * ∫ t, P n t ^ 2) ∧
                  let W : C(Icc 0 (V : ℝ), ℝ) :=
                    ⟨fun v => w (projIcc 0 (V : ℝ) V.property ((v : ℝ) / (1 + β))), by fun_prop⟩
                  ((∫ t in (0 : ℝ)..(V : ℝ),
                    (Real.exp (B.innerRate * β / (1 + β) * t) *
                      ‖lateRadiationDifferenceRows hU.le W B.innerRate (X n V)
                        (projIcc 0 (V : ℝ) V.property t)‖) ^ 2) ≤ Ed) ∧
                  let hW0 := fun v : Icc 0 (V : ℝ) => hw0 (projIcc 0 (V : ℝ) V.property ((v : ℝ) / (1 + β)))
                  let M := movingSpatialRadiationEnvelope W hW0 0 B.innerRate 0 (X n V)
                  let Z := fun t v : ℝ => g n t * Real.exp (B.innerRate * t) *
                    (intervalExtension V.property (intervalExtension hU.le (X n V).1 (g n t)) v 0 *
                      derivWithin (fun u => intervalExtension V.property (intervalExtension hU.le (X n V).1 u) v 1)
                        (Icc 0 U) (g n t))
                  (∫ t in (0 : ℝ)..(V : ℝ), (M (projIcc 0 (V : ℝ) V.property t)) ^ 2) ≤
                    E₀ + E₁ * ∫ t, P n t ^ 2 ∧
                  ∀ a b : ℝ, Tr ≤ a → a ≤ b → (1 + β) * b ≤ V → g n a ≤ U →
                    (∫ t in a..b, (Z t ((1 + β) * t)) ^ 2) ≤
                      2 * (F₀ + F₁ * ∫ t, P n t ^ 2) +
                        2 * ((2 * Real.exp 1) * Dr / (B.inner / 2) / (3 * B.innerRate)) ^ 2 *
                          (E₀ + E₁ * ∫ t, P n t ^ 2)) ∧
              (∀ n, Continuous (radiationRow B.innerRate (X n)) ∧
                MemLp (radiationRow B.innerRate (X n)) 2 (volume.restrict (Ici 0)) ∧
                (∫ t in Ici (0 : ℝ), ‖radiationRow B.innerRate (X n) t‖ ^ 2) ≤
                  Er₀ + Er₁ * ∫ t, P n t ^ 2) ∧
              (∀ n, LateRadiationHalfline hU.le B.innerRate β Tr
                (B.innerRate * β / (1 + β)) Ed (X n) (g n)) ∧
              ∃ hr : ∀ n (V : Ici (0 : ℝ)) u v, (X n V).1 u v 0 ≠ 0,
                ∀ n (V : Ici (0 : ℝ)) (u : Icc 0 U) (v : Icc 0 (V : ℝ)),
                  let ν := radialNuField V.property B.charge B.cosmological
                    (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n V).1 (hr n V)
                  |massField B.charge B.cosmological (X n V).1 (X n V).2.1 ν (hr n V) u v| ≤ Mbound) ∧
          (∀ n (T : Ici (0 : ℝ)) (q : Icc 0 U), 0 < (q : ℝ) → (1 + β) * arrival n q ≤ T →
            let γ := (1 + β) * arrival n q
            let v := projIcc 0 (T : ℝ) T.property γ
            |(X n T).2.1 q v 2 + 2 * B.innerRate| ≤ L * Real.exp (-τ * γ) ∧
              |(X n T).2.1 q v 0| ≤ L * Real.exp (-τ * γ)) ∧
          (∀ n (T : Ici (0 : ℝ)),
            ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 (T : ℝ),
              0 < u → (1 + β) * arrival n u ≤ v →
              |(X n T).2.2 u v 1| ≤ 2 * C * |f n u| +
                (2 * C + (2 * N * Hs / ((3 * B.inner / 4) * cL)) *
                  j ^ (-(cL * (1 + β) / B.outerRate))) *
                  u ^ (-1 + (B.innerRate / B.outerRate) * β + cL * (1 + β) / B.outerRate)) ∧
          (∀ n (T : Ici (0 : ℝ)),
            ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ v →
              |(X n T).2.1 u v 1| ≤ Hs / 2 * Real.exp (-cL * v) ∧
              |(X n T).2.1 u v 2 + 2 * B.innerRate| < (B.innerRate - cL) / 2) ∧
          (∀ n (T : Ici (0 : ℝ)),
            ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ v →
              |(X n T).2.1 u v 0| ≤ Ldec * Real.exp (-ηL * v)) ∧
          (∀ n (T : Ici (0 : ℝ)) (u : Icc 0 U), 0 < (u : ℝ) →
            ∀ a b : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ a → a ≤ b →
              |(X n T).1 u b 0 - (X n T).1 u a 0| ≤ Ldec / ηL * Real.exp (-ηL * a)) ∧
          (∀ n (T : Ici (0 : ℝ)),
            ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ v →
              Real.exp ((X n T).1 u v 2) ≤ Odec * (u : ℝ) ^ ((B.innerRate / B.outerRate) * β / 2 - 1) *
                Real.exp (-ηO * v)) ∧
          (∀ n (T : Ici (0 : ℝ)),
            ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ v →
              |(X n T).2.1 u v 2 + 2 * B.innerRate| ≤ Edec * Real.exp (-ηE * v)) ∧
          (∀ n (T : Ici (0 : ℝ)) (u : Icc 0 U), 0 < (u : ℝ) →
            ∀ a b : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ a → a ≤ b →
              |(X n T).1 u b 2 - (X n T).1 u a 2 + 2 * B.innerRate * ((b : ℝ) - a)| ≤
                Edec / ηE * Real.exp (-ηE * a)) ∧
          (∀ n (T : Ici (0 : ℝ)) (u : Icc 0 U), 0 < (u : ℝ) →
            ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ v →
              let a := projIcc 0 (T : ℝ) T.property (arrival n u)
              |(X n T).1 u v 2 - (X n T).1 u a 2 + 2 * B.innerRate * ((v : ℝ) - arrival n u)| ≤ Rmatch ∧
              Real.exp (-Rmatch) * (Real.exp ((X n T).1 u a 2) *
                Real.exp (-2 * B.innerRate * ((v : ℝ) - arrival n u))) ≤ Real.exp ((X n T).1 u v 2) ∧
              Real.exp ((X n T).1 u v 2) ≤ Real.exp Rmatch * (Real.exp ((X n T).1 u a 2) *
                Real.exp (-2 * B.innerRate * ((v : ℝ) - arrival n u))) ∧
              Olo ≤ (u : ℝ) * Real.exp ((X n T).1 u a 2) ∧
              (u : ℝ) * Real.exp ((X n T).1 u a 2) ≤ Ohi ∧
              Olo * (u : ℝ) ≤ -(X n T).2.1 u a 0 / Real.exp ((X n T).1 u a 2) ∧
              -(X n T).2.1 u a 0 / Real.exp ((X n T).1 u a 2) ≤ Ohi * (u : ℝ) ∧
              (Real.exp (-Rmatch) * Olo * j ^ (2 * B.innerRate / B.outerRate)) *
                ((u : ℝ) ^ (-1 - 2 * B.innerRate / B.outerRate) * Real.exp (-2 * B.innerRate * v)) ≤
                  Real.exp ((X n T).1 u v 2) ∧
              Real.exp ((X n T).1 u v 2) ≤ (Real.exp Rmatch * Ohi * D ^ (2 * B.innerRate / B.outerRate)) *
                ((u : ℝ) ^ (-1 - 2 * B.innerRate / B.outerRate) * Real.exp (-2 * B.innerRate * v))) ∧
          (∀ ε (hε : 0 < ε), ε ≤ U →
            ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∃ Z : ℕ → C(Icc ε U, WaveVector),
              (∀ n, Tendsto (renormalizedWaveRow hε.le B.innerRate (X n)) atTop (𝓝 (Z n))) ∧
              (∀ n t, T₀ ≤ t →
                ‖renormalizedWaveRow hε.le B.innerRate (X n) t - Z n‖ ≤
                  (Ldec / ηL + (Hs / 2) / cL + Edec / ηE) *
                    Real.exp (-(min ηL (min cL ηE)) * t)) ∧
              (∀ n u, 3 * B.inner / 4 ≤ Z n u 0) ∧
              (∀ n (u : Icc ε U), 0 < Real.exp (Z n u 2) ∧
                Tendsto (fun t => Real.exp (2 * B.innerRate * t) *
                  Real.exp ((X n ⟨max 0 t, le_max_left (0 : ℝ) t⟩).1
                    ⟨u, hε.le.trans u.property.1, u.property.2⟩
                    ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ 2)) atTop (𝓝 (Real.exp (Z n u 2)))) ∧
              ∃ Alo Ahi : ℝ, 0 < Alo ∧ 0 < Ahi ∧
                (∀ n u, Alo ≤ waveAmplitude (Z n) u ∧ waveAmplitude (Z n) u ≤ Ahi) ∧
                (∀ n t, T₀ ≤ t → ∀ u,
                  Alo ≤ waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t) u ∧
                    waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t) u ≤ Ahi) ∧
                (∀ n, Tendsto (fun t => waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t))
                  atTop (𝓝 (waveAmplitude (Z n)))) ∧
                (∀ n t, T₀ ≤ t →
                  ‖waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t) - waveAmplitude (Z n)‖ ≤
                    Ahi * (Ldec / ηL + (Hs / 2) / cL + Edec / ηE) *
                      Real.exp (-(min ηL (min cL ηE)) * t)) ∧
                (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
                  Tendsto Z atTop (𝓝 (Z 0)) ∧
                  TendstoUniformlyOn (fun n => renormalizedWaveRow hε.le B.innerRate (X n))
                    (renormalizedWaveRow hε.le B.innerRate (X 0)) atTop (Ici 0) ∧
                  Tendsto (fun n => waveAmplitude (Z n)) atTop (𝓝 (waveAmplitude (Z 0))) ∧
                  TendstoUniformlyOn (fun n t => waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t))
                    (fun t => waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X 0) t)) atTop (Ici 0))) ∧
          (∃ hr : ∀ n (T : Ici (0 : ℝ)) u v, (X n T).1 u v 0 ≠ 0,
            let ν := fun n (T : Ici (0 : ℝ)) => radialNuField T.property B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hr n T)
            let W := fun n (T : Ici (0 : ℝ)) => radialProductField T.property B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hr n T)
            let ζ := fun n (T : Ici (0 : ℝ)) => scalarTransportCorrection T.property (ν n T) (X n T).2.1
            (∀ n (T : Ici (0 : ℝ)) (u : Icc 0 U), 0 < (u : ℝ) → ∀ v : Icc 0 (T : ℝ),
              (1 + β) * arrival n u ≤ v →
                |ν n T u v| ≤ 2 * N * (u : ℝ) ^ ((B.innerRate / B.outerRate) * β - 1)) ∧
            (∀ ε (hε : 0 < ε), ε ≤ U →
              ∃ T₀ Cw Cν : ℝ, 0 ≤ T₀ ∧ 0 ≤ Cw ∧ 0 ≤ Cν ∧
                ∃ Zw Zν : ℕ → C(Icc ε U, ℝ),
                  (∀ n, Tendsto (scalarBoundaryRow hε.le (W n)) atTop (𝓝 (Zw n))) ∧
                  (∀ n t, T₀ ≤ t → ‖scalarBoundaryRow hε.le (W n) t - Zw n‖ ≤ Cw * Real.exp (-(2 * B.innerRate) * t)) ∧
                  (∀ n, Tendsto (scalarBoundaryRow hε.le (ν n)) atTop (𝓝 (Zν n))) ∧
                  (∀ n t, T₀ ≤ t → ‖scalarBoundaryRow hε.le (ν n) t - Zν n‖ ≤
                    Cν * Real.exp (-(min (2 * B.innerRate) ηL) * t)) ∧
                  (∀ n u, Zν n u ≤ 0) ∧
                  (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
                    Tendsto Zw atTop (𝓝 (Zw 0)) ∧
                    TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (W n))
                      (scalarBoundaryRow hε.le (W 0)) atTop (Ici 0) ∧
                    Tendsto Zν atTop (𝓝 (Zν 0)) ∧
                    TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (ν n))
                      (scalarBoundaryRow hε.le (ν 0)) atTop (Ici 0)) ∧
                  (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
                    MassCoefficientControl (fun n => massCoefficientRow hε.le B.innerRate (X n) (ν n)))) ∧
            (∀ ε (hε : 0 < ε), ε ≤ U →
              ∃ T₀ Cζ : ℝ, 0 ≤ T₀ ∧ 0 ≤ Cζ ∧ ∃ Zζ : ℕ → C(Icc ε U, ℝ),
                (∀ n, Tendsto (scalarBoundaryRow hε.le (ζ n)) atTop (𝓝 (Zζ n))) ∧
                (∀ n t, T₀ ≤ t → ‖scalarBoundaryRow hε.le (ζ n) t - Zζ n‖ ≤
                  Cζ * Real.exp (-cL * t)) ∧
                (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
                  Tendsto Zζ atTop (𝓝 (Zζ 0)) ∧
                  TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (ζ n))
                    (scalarBoundaryRow hε.le (ζ 0)) atTop (Ici 0))) ∧
            (f 0 = 0 → ∀ ε (hε : 0 < ε) (hεU : ε ≤ U),
              TransverseBoundaryGeometry hε.le hεU B.innerRate (X 0) (ν 0))) ∧
          (∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T),
            waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
              le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X n T) = X n S) ∧
          (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            ∀ T : Ici (0 : ℝ), Tendsto (fun n => X n T) atTop (𝓝 (X 0 T))) := by
  dsimp only
  obtain ⟨cL, c, β, ε, hcL, hcLk, htail, heq, hc0, hck, hcs, hβ, hβ8, hlink,
    hε, hε8, _hεβ, hnu, hℓ, hJ, hQ⟩ := exists_linked_inner_parameters B.innerRate_pos hks hl
  have hεk : ε < B.innerRate := by linarith only [hε8, B.innerRate_pos]
  have hpR : (4 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hpfin hp
  let q := Real.conjExponent p.toReal
  have hpq : p.toReal.HolderConjugate q := .conjExponent (by linarith only [hpR])
  have hkq : B.innerRate = (1 / q) * B.outerRate := by
    simpa only [one_div, hpq.one_sub_inv] using hcrit
  have hka : B.innerRate < B.outerRate := by
    rw [hcrit]
    have hh : 0 < 1 / p.toReal := one_div_pos.2 (by linarith only [hpR])
    nlinarith only [mul_pos hh B.outerRate_pos]
  have hca := hck.trans hka
  obtain ⟨Wsign, hWsign, hSign⟩ := B.exists_zero_scalar_positive
    (B.innerRate_pos.trans hks) hcL.le (hcLk.trans hka) (hcLk.trans hks).le
    htail hH hHlo hdH hdHR hc hb hlo hrc hrb hrd hrdec hOut
  have hcb : c ≤ B.outerRate * (1 - 1 / p.toReal) := by
    rw [mul_comm, ← hcrit]
    exact hck.le
  obtain ⟨δc, Δ, Y, U₀, N, C, L, τ, j, D, R₀, Olo, Ohi, hδc, hδcr, _hΔ, hΔr, hY, hU₀, hU₀δc, _hU1,
    hN, hC, hL, hτ, hj, hD, hdν, _hsmall, hR₀, hOlo, hOhi, hsolve⟩ :=
    B.exists_common_wave (B.innerRate_pos.trans hks) hH hdH hdHR hA hApt hc0 hca hcs.le
      hε hεk hε hβ hℓ hJ hQ hp hcb hc hb hrc hrb hrinit hrd hrdec hOut
  have hb0 : 0 < 1 - 1 / p.toReal := by
    have hh : 1 / p.toReal < 1 := (div_lt_one (by linarith only [hpR])).2 (by linarith only [hpR])
    linarith only [hh]
  have hb1 : 1 - 1 / p.toReal < 1 := by
    have hh : 0 < 1 / p.toReal := one_div_pos.2 (by linarith only [hpR])
    linarith only [hh]
  have hbeq : B.criticalExponent = 1 - 1 / p.toReal := by
    change B.innerRate / B.outerRate = 1 - 1 / p.toReal
    exact (div_eq_iff B.outerRate_pos.ne').2 hcrit
  have hm : B.criticalExponent < 1 := hbeq.trans_lt hb1
  obtain ⟨δm, Rm, hδm, hRm, hmatching⟩ := B.exists_common_radius_radiation
    (B.innerRate_pos.trans hks) hH hdH hdHR hA hEbudget hm hks hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δa, Ra, La, _hδa, _hδar, hRa, hLa, hsections⟩ := B.exists_nested_radius_sections
    (B.innerRate_pos.trans hks) hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨δq, Rq, Lq, _hδq, hRq, _hLq, hcharts⟩ := B.exists_auxiliary_radius_charts
    (B.innerRate_pos.trans hks) hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  let Laux := max La Lq
  have hLaux : 0 < Laux := hLa.trans_le (le_max_left _ _)
  obtain ⟨δr, Yr, Ur, Tr, jr, Dr, ηr, Cr, E₀, E₁, F₀, F₁, Drlo, Drhi,
    hδr, _hδrr, hYr, hYcap, hUr, _hUrδ,
    hTr, hjr, hDr, hηr, hCr, hE₀, hE₁, hF₀, hF₁, hDrlo, hDrhi, henergy⟩ :=
    B.exists_early_radiation_energy (B.innerRate_pos.trans hks) hH hdH hdHR hA hApt hc0 hca hcs.le
      hε hεk hε hβ.le hℓ hJ hQ hb0 hb1 (by simpa only [mul_comm] using hcrit) hks hp hcb
      (by rw [mul_comm, ← hcrit]) hc hb hrc hrb hrinit hrd hrdec hOut
      (min ((B.inner + Y) / 2) (min Ra (min Rq Rm)))
      (lt_min (by linarith only [hY]) (lt_min hRa.1 (lt_min hRq.1 hRm.1)))
  have hYrY : Yr < Y := by linarith only [hYcap.trans (min_le_left _ _), hY]
  have hYrRa : Yr ≤ Ra := (hYcap.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hYrRq : Yr ≤ Rq := ((hYcap.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hYrRm : Yr ≤ Rm := ((hYcap.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  let δ := max δc (max δr (max δa (max δq δm)))
  have hδcδ : δc ≤ δ := le_max_left _ _
  have hδrδ : δr ≤ δ := (le_max_left _ _).trans (le_max_right _ _)
  have hδaδ : δa ≤ δ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hδqδ : δq ≤ δ := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hδmδ : δm ≤ δ := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hδ : 0 < δ := hδc.trans_le (le_max_left _ _)
  have hU₀δ : U₀ ≤ δ := hU₀δc.trans (le_max_left _ _)
  have hdn := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnu B.outerRate_pos.le) hβ.le
  have hgap : (B.innerRate / B.outerRate) * β + cL * (1 + β) / B.outerRate ≤ c / B.outerRate := by
    calc
      _ = (cL + (B.innerRate + cL) * β) / B.outerRate := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hlink.le B.outerRate_pos.le
  have hρ : 0 < 3 * B.inner / 4 := by positivity [B.inner_pos]
  have hα : 0 < 1 + β := by linarith only [hβ]
  let sL := cL * (1 + β) / B.outerRate
  let dL := (B.innerRate / B.outerRate) * β
  let σ := (B.innerRate + cL) * (1 + β) / B.outerRate
  let K := (2 * N / ((3 * B.inner / 4) * cL)) * j ^ (-sL)
  let L₀ := L * (D / j) ^ σ
  let Q := (3 * B.inner / 2) / (B.innerRate - cL)
  have hsL : 0 < sL := by dsimp only [sL]; positivity [B.outerRate_pos]
  have hdL : 0 < dL := by dsimp only [dL]; positivity [B.innerRate_pos, B.outerRate_pos]
  have hsq : sL < 1 / q := by
    have hh : c / B.outerRate < 1 / q := (div_lt_iff₀ B.outerRate_pos).2 (by rw [← hkq]; exact hck)
    linarith only [hgap, hdL, hh]
  have hσ : 1 / q < σ := by
    apply (lt_div_iff₀ B.outerRate_pos).2
    nlinarith only [hkq, hcL, mul_pos (add_pos B.innerRate_pos hcL) hβ]
  obtain ⟨Hs, Ws, hHs, hNH, hWs, hWsU, himprove⟩ := exists_late_scalar_improvement
    (p := p) (q := q) (ρ := 3 * B.inner / 4) (N := N) (C := 2 * C) (K := K)
    (L := L₀) (Q := Q) (D := D) (A := A) (d := B.outerRate / (1 + β)) (c := cL)
    (s := sL) (δ := dL) (σ := σ) hp hpq
    hρ hN.le (by positivity) (by dsimp only [K]; positivity) (by dsimp only [L₀]; positivity)
    (by dsimp only [Q]; positivity [B.inner_pos, sub_pos.2 hcLk]) hA hcL hsL
    (by dsimp only [sL]; field_simp [B.outerRate_pos.ne', hα.ne']) hdL
    hsq hσ (lt_min hU₀ (lt_min hUr hδm))
  have hPc : ContinuousOn (fun r => conformalPotential r B.charge)
      (Icc (3 * B.inner / 4) (3 * B.inner / 2)) := by
    intro r hr
    have hr0 := hρ.trans_le hr.1
    unfold conformalPotential
    fun_prop (disch := positivity)
  obtain ⟨P₀, hP₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hPc
  let P := max P₀ 0
  have hP : 0 ≤ P := le_max_right _ _
  have hpot (r : ℝ) (hr : r ∈ Icc (3 * B.inner / 4) (3 * B.inner / 2)) :
      |conformalPotential r B.charge| ≤ P := by
    have hh : |conformalPotential r B.charge| ≤ P₀ := by simpa only [Real.norm_eq_abs] using hP₀ r hr
    exact hh.trans (le_max_left _ _)
  let dN := (2 * (2 / 3) * (B.innerRate - ε) / B.outerRate) * β
  let Llate := L₀ + Q * Hs ^ 2
  let G := 2 * C + K * Hs
  have hL₀ : 0 ≤ L₀ := by dsimp only [L₀]; positivity
  have hQ₀ : 0 ≤ Q := by dsimp only [Q]; positivity [B.inner_pos, sub_pos.2 hcLk]
  have hG : 0 ≤ G := by dsimp only [G, K]; positivity
  let ηL := min τ (2 * cL)
  let Ldec := L + Q * Hs ^ 2
  have hηL : 0 < ηL := lt_min hτ (by positivity)
  have hLdec : 0 < Ldec := add_pos_of_pos_of_nonneg hL (mul_nonneg hQ₀ (sq_nonneg _))
  let ηO := (B.outerRate / (1 + β)) * (dL / 2)
  let Odec := 8 * N * D ^ (dL / 2)
  have hηO : 0 < ηO := by dsimp only [ηO]; positivity [B.outerRate_pos]
  have hOdec : 0 < Odec := by dsimp only [Odec]; positivity
  have hηOq : ηO ≤ B.innerRate + cL := by
    have he : ηO = B.innerRate * β / (2 * (1 + β)) := by
      dsimp only [ηO, dL]; field_simp [B.outerRate_pos.ne', hα.ne']
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + β))).2
    nlinarith only [B.innerRate_pos, hcL, mul_pos B.innerRate_pos hβ, mul_pos hcL hα]
  let ηE := min τ (min ηO (min ηL cL))
  let Egeom := (Odec * P + 2 * Ldec * (2 * N) / (3 * B.inner / 4) ^ 2) * Ws ^ (dL / 2) / (dL / 2)
  let Escalar := Hs * (2 * C * A * Ws ^ (1 / q) + G * Ws ^ (dL + sL) / (dL + sL))
  let Edec := L + Egeom + Escalar
  have hηE : 0 < ηE := lt_min hτ (lt_min hηO (lt_min hηL hcL))
  have hEgeom : 0 ≤ Egeom := by dsimp only [Egeom]; positivity
  have hEscalar : 0 ≤ Escalar := by dsimp only [Escalar]; positivity
  have hEdec : 0 < Edec := add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hL hEgeom) hEscalar
  let Rmatch := R₀ + Edec / ηE
  have hRmatch : 0 < Rmatch := by dsimp only [Rmatch]; positivity
  let CoRad := Real.exp Rmatch * Ohi * D ^ (2 * B.innerRate / B.outerRate)
  let Lrad := Drhi * CoRad * Real.exp (1 / 4)
  let crad := (Lrad * Cr / (1 + β) * jr ^ (-(2 * B.innerRate / B.outerRate))) / (3 * B.inner / 4)
  let drad := (Lrad * (2 * N) * Cr / (1 + β) *
    jr ^ (-(2 * B.innerRate / B.outerRate - B.innerRate / B.outerRate * β))) /
      ((3 * B.inner / 4) ^ 2 * (2 * B.innerRate - 3 * (B.innerRate * β / (1 + β))))
  have hRadGap : 0 < 2 * B.innerRate - 3 * (B.innerRate * β / (1 + β)) := by
    have hh : 3 * (B.innerRate * β) < 2 * B.innerRate * (1 + β) := by
      nlinarith only [mul_pos B.innerRate_pos (show 0 < 2 - β by linarith only [hβ8])]
    have hh' : 3 * (B.innerRate * β / (1 + β)) < 2 * B.innerRate := by
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hα).2 hh
    exact sub_pos.2 hh'
  have hCoRad : 0 ≤ CoRad := by dsimp only [CoRad]; positivity
  have hLrad : 0 ≤ Lrad := by dsimp only [Lrad]; positivity
  have hdrad : 0 ≤ drad := by dsimp only [drad]; positivity
  let Brad := 8 * (1 + β) * (crad / B.innerRate) ^ 2
  let Ggamma := (2 * Real.exp 1) * Dr / (B.inner / 2) / (3 * B.innerRate)
  let Er₀ := 9 * E₀ + Brad * (2 * F₀ + 2 * Ggamma ^ 2 * E₀)
  let Er₁ := 9 * E₁ + Brad * (2 * F₁ + 2 * Ggamma ^ 2 * E₁)
  have hBrad : 0 ≤ Brad := by dsimp only [Brad]; positivity
  have hEr₀ : 0 ≤ Er₀ := by dsimp only [Er₀]; positivity
  have hEr₁ : 0 ≤ Er₁ := by dsimp only [Er₁]; positivity
  let ξrad := B.innerRate * β / (1 + β)
  have hξrad : 0 < ξrad := by dsimp only [ξrad]; positivity [B.innerRate_pos]
  have hξradk : ξrad < B.innerRate := by
    apply (div_lt_iff₀ hα).2
    nlinarith only [B.innerRate_pos]
  let EeBudget := E₀ + E₁ * Ebudget
  let EgBudget := 2 * (F₀ + F₁ * Ebudget) + 2 * Ggamma ^ 2 * EeBudget
  let Ed := 2 * (crad / (B.innerRate - ξrad)) ^ 2 * ((1 + β) * EgBudget) +
    2 * (drad / (B.innerRate - ξrad)) ^ 2 * (8 * EeBudget + Brad * EgBudget)
  have hEd : 0 ≤ Ed := by dsimp only [Ed, EeBudget, EgBudget]; positivity
  obtain ⟨Wr, hWr, hWrWs, hsmallRad⟩ := exists_radiation_absorption_width
    B.outerRate_pos B.innerRate_pos hβ hjr hdrad hWs
  let CoLow := Real.exp (-Rmatch) * Olo * j ^ (2 * B.innerRate / B.outerRate)
  have hCoLow : 0 < CoLow := by dsimp only [CoLow]; positivity
  have hσ : 0 < 2 * B.innerRate / B.outerRate := by positivity [B.innerRate_pos, B.outerRate_pos]
  let Fflux := fun u : ℝ => u ^ (2 * B.innerRate / B.outerRate) /
    (Drlo * (3 * B.inner / 4) * CoLow) * (Er₀ + Er₁ * Ebudget)
  have hFflux : Continuous Fflux := by dsimp only [Fflux]; fun_prop (disch := positivity)
  have hFzero : Fflux 0 = 0 := by simp only [Fflux, Real.zero_rpow hσ.ne', zero_div, zero_mul]
  have hFsmall : ∀ᶠ u : ℝ in 𝓝 0, Fflux u < Real.exp (1 / 16) - 1 :=
    hFflux.continuousAt.tendsto.eventually_lt_const (by
      rw [hFzero]; exact sub_pos.2 (Real.one_lt_exp_iff.2 (by norm_num)))
  obtain ⟨Wf, hWf, hWfWr, hWfsmall⟩ := ((eventually_lt_nhds hWr).and hFsmall).exists_gt
  obtain ⟨U, hU, hUWfcap, hentrysmall, hconformal⟩ := exists_late_conformal_improvement
    (p := p) (q := q) (ρ := 3 * B.inner / 4) (N := 2 * N) (L := Llate) (H := Hs)
    (P := P) (C := 2 * C) (G := G) (d := dN) (s := dL + sL) (a := B.outerRate / (1 + β))
    (τ := τ) (E := L) (j := j) (A := A) (ε := (B.innerRate - cL) / 2) (k := B.innerRate)
    hp hpq hρ (by positivity)
    (by dsimp only [Llate]; positivity) hHs.le hP (by positivity) hG hdν (add_pos hdL hsL)
    (by positivity [B.outerRate_pos]) hτ hL.le hj hA (by positivity [sub_pos.2 hcLk])
    (lt_min hWf (lt_min hUcap hWsign))
  have hUWf := hUWfcap.trans (min_le_left Wf (min Ucap Wsign))
  have hUUcap := (hUWfcap.trans (min_le_right Wf (min Ucap Wsign))).trans (min_le_left _ _)
  have hUWsign := (hUWfcap.trans (min_le_right Wf (min Ucap Wsign))).trans (min_le_right _ _)
  have hUWr := hUWf.trans hWfWr.le
  have hsmallFlux (u : ℝ) (hu : 0 ≤ u) (huU : u ≤ U) : Fflux u ≤ Real.exp (1 / 16) - 1 :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow hu (huU.trans hUWf) hσ.le) (by positivity)) (by positivity)).trans hWfsmall.le
  have hUWs := hUWr.trans hWrWs
  have hUUr := ((hUWs.trans hWsU).trans (min_le_right _ _)).trans (min_le_left Ur δm)
  have hUδm := ((hUWs.trans hWsU).trans (min_le_right _ _)).trans (min_le_right Ur δm)
  have hUU := (hUWs.trans hWsU).trans (min_le_left U₀ (min Ur δm))
  have hUδ := hUU.trans hU₀δ
  have hUR : U < r 0 := by linarith only [hUU.trans (hU₀δc.trans hδcr), B.inner_pos.trans hrinit]
  have hdom : Ioc (0 : ℝ) U ⊆ Ioc 0 U₀ := Ioc_subset_Ioc le_rfl hUU
  obtain ⟨Minit, hMinit, hInitialMass⟩ := exists_uniform_initial_mass_bound
    (B.inner_pos.trans hrinit) hc (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
    (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
    (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb) hrd hρ hA
  let Qmass := (2 * N) * (Drhi * Real.exp (1 / 8))
  let Mlate := (3 * B.inner / 2) / 2 + B.charge ^ 2 / (2 * (3 * B.inner / 4)) +
    2 * (3 * B.inner / 2) * Qmass
  let Mbound := max Minit (max |B.mass| Mlate)
  have hQmass : 0 ≤ Qmass := by dsimp only [Qmass]; positivity
  have hMbound : 0 ≤ Mbound := hMinit.trans (le_max_left _ _)
  have haux (Y' : Ioo B.inner Yr) :=
    hsections Y' Yr β U Y'.property.1 Y'.property.2 hYrRa hβ hU
  choose Taux hTaux hauxSolve using haux
  have hchart (Y' : Ioo B.inner Yr) :=
    hcharts Y' Yr β U Tr Dr Y'.property.1 Y'.property.2 hYrRq hβ hU hTr.le
  choose Saux hSaux hchartSolve using hchart
  have hmatch (Y' : Ioo B.inner Yr) :=
    hmatching Y' Y'.property.1 (Y'.property.2.le.trans hYrRm)
  choose τmatch hτmatch hmatchSolve using hmatch
  let Tmatch := fun Y' => τmatch Y' ⟨U, hU⟩
  refine ⟨δ, U, Y, Yr, β, L, τ, j, D, cL, N, C, Hs, ηL, Ldec, ηO, Odec, ηE, Edec, Rmatch, Olo, Ohi,
    Tr, jr, Dr, ηr, Cr, E₀, E₁, F₀, F₁, Drlo, Drhi, Er₀, Er₁, Mbound, Ed,
    hδ, hY, hβ, hβ8, hL, hτ, hj, hD, hcL, hcLk, htail, hN, hC, hHs, hNH, hηL, hLdec, hηO, hOdec,
    hηE, hEdec, hRmatch, hOlo, hOhi, hYr, hYrY, hTr, hjr, hDr, hηr, hCr, hE₀, hE₁, hF₀, hF₁, hDrlo, hDrhi,
    hEr₀, hEr₁, hMbound, hEd, hentrysmall, hUUcap, hU, hUδ, hUR, Laux, hLaux, Taux, hTaux, Saux, hSaux,
    Tmatch, (fun Y' => hτmatch Y' ⟨U, hU⟩), hm, ?_⟩
  intro f hf hfn hpoint
  let hfU := fun n => (hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hUδ) le_rfl)
  have hprofiles (n : ℕ) := hsolve (f n)
    ((hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hδcδ) le_rfl))
    ((scalar_prefix_norm_le hδcδ (hf n)).trans (hfn n))
    (ae_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl hδcδ) le_rfl) (hpoint n))
  choose arrival hac haa hal hpos hscale hmatching hpre hex using hprofiles
  have hfamily (n : ℕ) (T : Ici (0 : ℝ)) := (hex n U T hU T.property hUR (hfU n) hUU).exists
  choose X hX using hfamily
  have hauxFamily (Y' : Ioo B.inner Yr) (n : ℕ) : ∃ ψ : ℝ → ℝ,
      ContinuousOn ψ (Ici (Taux Y')) ∧
      (∀ t ∈ Ici (Taux Y'), t < ψ t ∧ ψ t ≤ (1 + β) * t) ∧
      ∀ (V : Ici (0 : ℝ)) (t : ℝ), Taux Y' ≤ t → ψ t ≤ V → ∀ u : Icc 0 U,
        (X n V).1 u (projIcc 0 (V : ℝ) V.property t) 0 = Yr →
          (X n V).1 u (projIcc 0 (V : ℝ) V.property (ψ t)) 0 = Y' ∧
          ∀ hr : ∀ q v, (X n V).1 q v 0 ≠ 0,
            let ν' := radialNuField V.property B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n V).1 hr
            let v := projIcc 0 (V : ℝ) V.property (ψ t)
            Real.exp (-1) * (-B.F Y') / B.outerRate ≤ (u : ℝ) * (-ν' u v) ∧
            (u : ℝ) * (-ν' u v) ≤ Real.exp 1 * (-B.F Y') / B.outerRate ∧
            0 < -(X n V).2.1 u v 0 ∧ -(X n V).2.1 u v 0 ≤ Laux * ((Y' : ℝ) - B.inner) := by
    obtain ⟨ψ, hψc, hψb, hψp⟩ := hauxSolve Y' p hp (f n)
      ((hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hδaδ) le_rfl))
      ((scalar_prefix_norm_le hδaδ (hf n)).trans (hfn n))
    refine ⟨ψ, hψc, hψb, ?_⟩
    intro V t ht htV u hrad
    have hh := hψp U V hU.le V.property hUR (hfU n) (X n V) (hX n V).choose le_rfl t ht htV u hrad
    refine ⟨hh.1, ?_⟩
    intro hr
    have he := hh.2 hr
    exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.trans
      (mul_le_mul_of_nonneg_right (le_max_left La Lq) (sub_pos.2 Y'.property.1).le)⟩
  have hcompat (n : ℕ) (S T : Ici (0 : ℝ)) (hST : S ≤ T) :
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X n T) = X n S :=
    (hX n T).choose.horizon_prefix_unique hU.le T.property hUR hU.le S.property le_rfl hST
      hc (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
      (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne') hp (hfU n) (hfU n) (hX n S).choose
  have hfinite (hzero : f 0 = 0)
      (hlim : Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0))
      (T : Ici (0 : ℝ)) : Tendsto (fun n => X n T) atTop (𝓝 (X 0 T)) := by
    have hlimU : Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 U))).toReal) atTop (𝓝 0) :=
      squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => scalar_prefix_norm_le hUδ (hf n)) hlim
    apply IsWaveIntegral.horizon_tendsto_zero_incoming hU.le (hUU.trans _hU1) T.property hUR hc
      (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
      (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
      (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
      hrd hρ hA hp hfU (fun n => (scalar_prefix_norm_le hUδ (hf n)).trans (hfn n)) hlimU
      (fun n => (hX n T).choose) _ (fun n => (hX n T).choose_spec.1) (hX 0 T).choose_spec.1
    simpa only [hzero] using (hX 0 T).choose
  have hscalarImprove : ∀ n (T : Ici (0 : ℝ)),
      (∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n q ≤ v →
        |(X n T).2.1 q v 1| ≤ Hs * Real.exp (-cL * v)) →
      (∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n q ≤ v →
        (X n T).2.1 q v 2 ≤ -(B.innerRate + cL)) →
      ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ v →
        |(X n T).2.1 u v 1| ≤ Hs / 2 * Real.exp (-cL * v) := by
    intro n T hscalar hell
    have hqc : 2 * cL < B.innerRate + cL := by linarith only [hcLk]
    apply himprove U T (r 0) (horizonPhi h r 0) B.charge B.cosmological hU T.property hUR
      (f n) (hfU n) _ (X n T) (hX n T).choose hUWs ((scalar_prefix_norm_le hUδ (hf n)).trans (hfn n))
      (fun t => (1 + β) * arrival n t)
      (((hac n).mono hdom).const_mul _) (fun x hx y hy hxy =>
        mul_lt_mul_of_pos_left (haa n (hdom hx) (hdom hy) hxy) hα) ((hal n).const_mul_atTop hα)
    · intro z hz
      have he : B.outerRate / (1 + β) * ((1 + β) * arrival n z) = B.outerRate * arrival n z := by
        field_simp [hα.ne']
      simpa only [he] using (hscale n z (hdom hz)).2
    · exact (hX n T).choose_spec.1
    · intro z hz v hγ
      have hsc := ((hX n T).choose_spec.2.2.1 z hz (hγ.le.trans v.property.2)).1
      simp only [hγ, projIcc_of_mem T.property v.property] at hsc
      have hcLc : cL < c := by linarith only [heq, hcLk]
      have hs := hsc.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (neg_le_neg hcLc.le) v.property.1)) (by positivity : 0 ≤ N / 2))
      have hr : (X n T).1 z v 0 ≤ 3 * B.inner / 2 := by
        have hh := ((hX n T).choose_spec.2.1 z hz v hγ.le).2.1
        linarith only [hh, hΔr, B.inner_pos]
      rw [abs_mul, abs_of_pos (hρ.trans_le ((hX n T).choose_spec.1 z v))]
      exact (mul_le_mul hr hs (abs_nonneg _) (by positivity [B.inner_pos])).trans_eq (by ring)
    · intro z u hz hzu v hγ
      have hh := (hX n T).choose_spec.2.2.2.2.2 (B.innerRate + cL) cL Hs hcL hHs.le hqc
        hscalar hell z u hz hzu v hγ
      convert hh using 1
      dsimp only [Q, L₀]
      rw [show B.innerRate + cL - 2 * cL = B.innerRate - cL by ring]
      ring
    · filter_upwards [(hX n T).choose_spec.2.2.2.2.1 cL Hs hcL hHs.le hscalar] with t ht
      intro v ht0 htv
      convert (ht v ht0 htv).2 dL hdL hdn hgap using 1
      dsimp only [K, dL, sL]
      ring_nf
  have hconformalImprove : ∀ n (T : Ici (0 : ℝ)),
      (∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n q ≤ v →
        |(X n T).2.1 q v 1| ≤ Hs * Real.exp (-cL * v)) →
      (∀ q : Icc 0 U, 0 < (q : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n q ≤ v →
        (X n T).2.1 q v 2 ≤ -(B.innerRate + cL)) →
      ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ v →
        |(X n T).2.1 u v 2 + 2 * B.innerRate| < (B.innerRate - cL) / 2 := by
    intro n T hscalar hell
    have hqc : 2 * cL < B.innerRate + cL := by linarith only [hcLk]
    apply hconformal U T (r 0) (horizonPhi h r 0) B.charge B.cosmological hU T.property hUR
      (f n) (hfU n) _ (X n T) (hX n T).choose le_rfl ((scalar_prefix_norm_le hUδ (hf n)).trans (hfn n))
      (fun t => (1 + β) * arrival n t)
      (((hac n).mono hdom).const_mul _) (fun x hx y hy hxy =>
        mul_lt_mul_of_pos_left (haa n (hdom hx) (hdom hy) hxy) hα) ((hal n).const_mul_atTop hα)
    · intro z hz
      have he : B.outerRate / (1 + β) * ((1 + β) * arrival n z) = B.outerRate * arrival n z := by
        field_simp [hα.ne']
      simpa only [he] using (hscale n z (hdom hz)).1
    · intro z hz v hγ
      have hh := ((hX n T).choose_spec.2.2.1 z hz (hγ.le.trans v.property.2)).2.1
      simpa only [hγ, projIcc_of_mem T.property v.property] using hh
    · intro z u hz hzu v hγ
      have hu := hz.trans_le hzu
      have hk : (z : ℝ) ^ σ * (u : ℝ) ^ (-σ) ≤ 1 := by
        rw [Real.rpow_neg hu.le, ← div_eq_mul_inv]
        exact (div_le_one (Real.rpow_pos_of_pos hu _)).2
          (Real.rpow_le_rpow hz.le hzu (by dsimp only [σ]; positivity [B.innerRate_pos, B.outerRate_pos]))
      have he : Real.exp (-(2 * cL) * (v : ℝ)) ≤ 1 :=
        Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hcL]) v.property.1)
      have hh := (hX n T).choose_spec.2.2.2.2.2 (B.innerRate + cL) cL Hs hcL hHs.le hqc
        hscalar hell z u hz hzu v hγ
      have hh' : |(X n T).2.1 u v 0| ≤ L₀ * ((z : ℝ) ^ σ * (u : ℝ) ^ (-σ)) +
          Q * Hs ^ 2 * Real.exp (-(2 * cL) * v) := by
        convert hh using 1
        dsimp only [Q, L₀]
        rw [show B.innerRate + cL - 2 * cL = B.innerRate - cL by ring]
        ring
      exact (hh'.trans (add_le_add (mul_le_mul_of_nonneg_left hk hL₀)
        (mul_le_mul_of_nonneg_left he (by positivity)))).trans_eq (by dsimp only [Llate]; ring)
    · intro u hu v hγ
      have hg := (hX n T).choose_spec.2.1 u hu v hγ
      have hga := (hX n T).choose.interior_gauge hU.le T.property hUR hc
        (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
        (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
        (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
        hrd hp (hfU n) u v
      have homega := (div_le_iff_of_neg
        (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hga.2.2.1)).1 hga.2.2.2.2
      refine ⟨(hX n T).choose_spec.1 u v, ?_, ?_, ?_, ?_⟩
      · simpa only [dN, show dN - 1 = -1 + dN by ring] using hg.2.2
      · linarith only [homega]
      · have he := Real.exp_le_one_iff.2
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hcL.le) v.property.1)
        exact (hscalar u hu v hγ).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hHs.le)
      · apply hpot _ ⟨(hX n T).choose_spec.1 u v, ?_⟩
        linarith only [hg.2.1, hΔr, B.inner_pos]
    · filter_upwards [(hX n T).choose_spec.2.2.2.2.1 cL Hs hcL hHs.le hscalar] with t ht
      intro v ht0 htv
      convert (ht v ht0 htv).2 dL hdL hdn hgap using 1
      dsimp only [G, K, dL, sL]
      ring_nf
  have hvel (n : ℕ) (S T : Ici (0 : ℝ)) (hST : S ≤ T) (u : Icc 0 U) (v : Icc 0 (S : ℝ)) :
      (X n T).2.1 u ⟨v, v.property.1, v.property.2.trans hST⟩ = (X n S).2.1 u v := by
    have hh := congrArg (fun x : WaveState U (S : ℝ) => x.2.1 u v) (hcompat n S T hST)
    change (X n T).2.1 (intervalTranslate (a := 0) le_rfl (by simp) u)
      (intervalTranslate (A := (T : ℝ)) (a := 0) le_rfl
        (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) v) =
        (X n S).2.1 u v at hh
    simpa only [intervalTranslate, ContinuousMap.coe_mk, zero_add] using hh
  have hweight (w t A : ℝ) : Real.exp (cL * t) * |w| ≤ A ↔ |w| ≤ A * Real.exp (-cL * t) := by
    rw [show -cL * t = -(cL * t) by ring, Real.exp_neg, ← div_eq_mul_inv,
      le_div_iff₀ (Real.exp_pos _), mul_comm]
  have hclosed (n : ℕ) (T : Ici (0 : ℝ)) :
      ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ v →
        |(X n T).2.1 u v 1| ≤ Hs / 2 * Real.exp (-cL * v) ∧
        |(X n T).2.1 u v 2 + 2 * B.innerRate| < (B.innerRate - cL) / 2 := by
    let γ := fun u => (1 + β) * arrival n u
    let F := fun p : ℝ × Icc 0 U =>
      max (Real.exp (cL * p.1) * |(X n T).2.1 p.2 (projIcc 0 (T : ℝ) T.property p.1) 1| - Hs)
        ((X n T).2.1 p.2 (projIcc 0 (T : ℝ) T.property p.1) 2 + (B.innerRate + cL))
    have hvc (i : Fin 3) : Continuous (fun p : ℝ × Icc 0 U =>
        (X n T).2.1 p.2 (projIcc 0 (T : ℝ) T.property p.1) i) :=
      ((continuous_apply i).comp (X n T).2.1.uncurry.continuous).comp
        (continuous_snd.prodMk ((continuous_projIcc (h := T.property)).comp continuous_fst))
    have hFc : Continuous F :=
      (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul (hvc 1).abs).sub
        continuous_const).max ((hvc 2).add continuous_const)
    have hgamma0 (u) (hu : u ∈ Ioc 0 U) : 0 ≤ γ u :=
      (mul_pos hα (hpos n u (hdom hu))).le
    have hboot := continuous_entered_bootstrap_of_tendsto hU hFc
      (((hac n).mono hdom).const_mul _) (fun x hx y hy hxy =>
        mul_lt_mul_of_pos_left (haa n (hdom hx) (hdom hy) hxy) hα)
      ((hal n).const_mul_atTop hα) hgamma0 (by
        intro u hu huT
        have hγm : γ u ∈ Icc 0 (T : ℝ) := ⟨hgamma0 u ⟨hu, u.property.2⟩, huT⟩
        have hg := (hX n T).choose_spec.2.2.1 u hu huT
        have hcLc : cL < c := by linarith only [heq, hcLk]
        have hsc := hg.1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_right (neg_le_neg hcLc.le) hγm.1)) (by positivity : 0 ≤ N / 2))
        have hsw := (hweight _ (γ u) (N / 2)).2 hsc
        have haΓ : 0 < B.outerRate / (1 + β) := div_pos B.outerRate_pos hα
        have hscaleΓ : j ≤ (u : ℝ) * Real.exp ((B.outerRate / (1 + β)) * γ u) := by
          have he : (B.outerRate / (1 + β)) * γ u = B.outerRate * arrival n u := by
            dsimp only [γ]
            field_simp [hα.ne']
          simpa only [he] using (hscale n u (hdom ⟨hu, u.property.2⟩)).1
        have he := (arrival_exp_power haΓ hu hj hτ.le hscaleΓ).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu.le u.property.2
            (div_pos hτ haΓ).le) (by positivity))
        have hge : L * Real.exp (-τ * γ u) < (B.innerRate - cL) / 2 :=
          (mul_le_mul_of_nonneg_left he hL.le).trans_lt (by simpa only [mul_assoc] using hentrysmall)
        have hell := (le_abs_self _).trans_lt (hg.2.1.trans_lt hge)
        change max _ _ < 0
        exact max_lt_iff.2 ⟨by linarith only [hsw, hNH, hHs], by linarith only [hell, hcLk]⟩) (by
        intro t ht hpre u hu hut
        let S : Ici (0 : ℝ) := ⟨t, ht.1⟩
        have hbs (w : Icc 0 U) (hw : 0 < (w : ℝ)) (v : Icc 0 (S : ℝ)) (hwv : γ w ≤ v) :
            |(X n S).2.1 w v 1| ≤ Hs * Real.exp (-cL * v) ∧
              (X n S).2.1 w v 2 ≤ -(B.innerRate + cL) := by
          have hvT : (v : ℝ) ∈ Icc 0 (T : ℝ) := ⟨v.property.1, v.property.2.trans ht.2⟩
          have hh := hpre v ⟨v.property.1, v.property.2⟩ w hw hwv
          simp only [F, projIcc_of_mem T.property hvT] at hh
          rw [hvel n S T ht.2 w v] at hh
          exact ⟨(hweight _ _ _).1 (sub_nonpos.1 (max_le_iff.1 hh).1),
            by linarith only [(max_le_iff.1 hh).2]⟩
        let vS : Icc 0 (S : ℝ) := ⟨t, ht.1, le_rfl⟩
        have hs := hscalarImprove n S (fun w hw v hv => (hbs w hw v hv).1)
          (fun w hw v hv => (hbs w hw v hv).2) u hu vS hut
        have he := hconformalImprove n S (fun w hw v hv => (hbs w hw v hv).1)
          (fun w hw v hv => (hbs w hw v hv).2) u hu vS hut
        have hsw := (hweight _ t (Hs / 2)).2 hs
        have hel := (le_abs_self _).trans_lt he
        dsimp only [F]
        rw [projIcc_of_mem T.property ht, hvel n S T ht.2 u vS]
        exact max_lt_iff.2 ⟨by linarith only [hsw, hHs], by linarith only [hel, hcLk]⟩)
    have hbs (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 (T : ℝ)) (huv : γ u ≤ v) :
        |(X n T).2.1 u v 1| ≤ Hs * Real.exp (-cL * v) ∧
          (X n T).2.1 u v 2 ≤ -(B.innerRate + cL) := by
      have hh := (hboot v v.property u hu huv).le
      simp only [F, projIcc_of_mem T.property v.property] at hh
      exact ⟨(hweight _ _ _).1 (sub_nonpos.1 (max_le_iff.1 hh).1),
        by linarith only [(max_le_iff.1 hh).2]⟩
    intro u hu v huv
    exact ⟨hscalarImprove n T (fun w hw v hv => (hbs w hw v hv).1)
      (fun w hw v hv => (hbs w hw v hv).2) u hu v huv,
      hconformalImprove n T (fun w hw v hv => (hbs w hw v hv).1)
        (fun w hw v hv => (hbs w hw v hv).2) u hu v huv⟩
  have hlateLambda (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc 0 U) (hu : 0 < (u : ℝ))
      (v : Icc 0 (T : ℝ)) (huv : (1 + β) * arrival n u ≤ v) :
      |(X n T).2.1 u v 0| ≤ Ldec * Real.exp (-ηL * v) := by
    have hqc : 2 * cL < B.innerRate + cL := by linarith only [hcLk]
    have hγ0 : 0 ≤ (1 + β) * arrival n u := (mul_pos hα (hpos n u (hdom ⟨hu, u.property.2⟩))).le
    have hgm : (1 + β) * arrival n u ∈ Icc 0 (T : ℝ) := ⟨hγ0, huv.trans v.property.2⟩
    let a : Icc 0 (T : ℝ) := ⟨(1 + β) * arrival n u, hgm⟩
    have hg := ((hX n T).choose_spec.2.2.1 u hu (huv.trans v.property.2)).2.2.1
    simp only [projIcc_of_mem T.property hgm] at hg
    have hb := (hX n T).choose.lambda_damping_exp hU.le T.property hUR hc
      (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
      (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
      (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
      hrd hp (hfU n) hcL hqc hHs.le u a v huv (R := 3 * B.inner / 2) (by
        intro w hw
        have hh := ((hX n T).choose_spec.2.1 u hu w hw.1).2.1
        linarith only [hh, hΔr, B.inner_pos]) (by
        intro w hw
        exact (hclosed n T u hu w hw.1).1.trans
          (mul_le_mul_of_nonneg_right (by linarith only [hHs]) (Real.exp_pos _).le)) (by
        intro w hw
        have hh := (le_abs_self _).trans_lt (hclosed n T u hu w hw.1).2
        linarith only [hh, hcLk])
    have hηq : ηL ≤ B.innerRate + cL := (min_le_right τ (2 * cL)).trans hqc.le
    have he : Real.exp (-(B.innerRate + cL) * ((v : ℝ) - a)) * Real.exp (-τ * a) ≤
        Real.exp (-ηL * v) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith only [mul_nonneg (sub_nonneg.2 hηq) (sub_nonneg.2 huv),
        mul_nonneg (sub_nonneg.2 (min_le_left τ (2 * cL))) a.property.1]
    have he2 : Real.exp (-(2 * cL) * (v : ℝ)) ≤ Real.exp (-ηL * v) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right τ (2 * cL))) v.property.1)
    have hh : |(X n T).2.1 u v 0| ≤
        Real.exp (-(B.innerRate + cL) * ((v : ℝ) - a)) * (L * Real.exp (-τ * a)) +
          Q * Hs ^ 2 * Real.exp (-(2 * cL) * v) := by
      apply hb.trans
      convert add_le_add (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le) le_rfl using 1
      dsimp only [Q]
      rw [show B.innerRate + cL - 2 * cL = B.innerRate - cL by ring]
      ring
    calc
      _ ≤ _ := hh
      _ = L * (Real.exp (-(B.innerRate + cL) * ((v : ℝ) - a)) * Real.exp (-τ * a)) +
          Q * Hs ^ 2 * Real.exp (-(2 * cL) * v) := by ring
      _ ≤ L * Real.exp (-ηL * v) + Q * Hs ^ 2 * Real.exp (-ηL * v) :=
        add_le_add (mul_le_mul_of_nonneg_left he hL.le)
          (mul_le_mul_of_nonneg_left he2 (mul_nonneg hQ₀ (sq_nonneg _)))
      _ = _ := by dsimp only [Ldec]; ring
  let ν (n : ℕ) (T : Ici (0 : ℝ)) := radialNuField T.property B.charge B.cosmological
    (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose.choose
  have hga (n : ℕ) (T : Ici (0 : ℝ)) := (hX n T).choose.interior_gauge hU.le T.property hUR hc
    (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
    (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
    (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
    hrd hp (hfU n)
  have hnuPower (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc 0 U) (hu : 0 < (u : ℝ))
      (v : Icc 0 (T : ℝ)) (huv : (1 + β) * arrival n u ≤ v) :
      |ν n T u v| ≤ 2 * N * (u : ℝ) ^ (dL - 1) := by
    rw [abs_of_neg (hga n T u v).2.2.1]
    have hh := ((hX n T).choose_spec.2.1 u hu v huv).2.2
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hu (u.property.2.trans (hUU.trans _hU1))
        (by dsimp only [dL, dN]; linarith only [hdn] : dL - 1 ≤ -1 + dN)) (by positivity))
  have hlapse (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc 0 U) (hu : 0 < (u : ℝ))
      (v : Icc 0 (T : ℝ)) (huv : (1 + β) * arrival n u ≤ v) :
      Real.exp ((X n T).1 u v 2) ≤ Odec * (u : ℝ) ^ (dL / 2 - 1) * Real.exp (-ηO * v) := by
    have hgm : (1 + β) * arrival n u ∈ Icc 0 (T : ℝ) :=
      ⟨(mul_pos hα (hpos n u (hdom ⟨hu, u.property.2⟩))).le, huv.trans v.property.2⟩
    let a : Icc 0 (T : ℝ) := ⟨(1 + β) * arrival n u, hgm⟩
    have he : ηO / (B.outerRate / (1 + β)) = dL / 2 := by
      dsimp only [ηO]; field_simp [B.outerRate_pos.ne', hα.ne']
    have hh := (hX n T).choose.late_lapse_bound u hu a v huv
      (div_pos B.outerRate_pos hα) (N := 8 * N) (d := dL) (by positivity) hηO.le hηOq (by
        have heq : B.outerRate / (1 + β) * (a : ℝ) = B.outerRate * arrival n u := by
          dsimp only [a]; field_simp [hα.ne']
        simpa only [heq] using (hscale n u (hdom ⟨hu, u.property.2⟩)).2) (by
        have hg := hga n T u a
        have homega := (div_le_iff_of_neg
          (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hg.2.2.1)).1 hg.2.2.2.2
        have hn := hnuPower n T u hu a le_rfl
        rw [abs_of_neg hg.2.2.1] at hn
        nlinarith only [homega, hn]) (by
        intro w hw
        have hh := (le_abs_self _).trans_lt (hclosed n T u hu w hw.1).2
        linarith only [hh, hcLk])
    simpa only [he, show dL - 1 - dL / 2 = dL / 2 - 1 by ring] using hh
  have hfuture (n : ℕ) (T : Ici (0 : ℝ)) :
      ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 (T : ℝ), 0 < t → (1 + β) * arrival n t ≤ v →
        |(X n T).2.2 t v 1| ≤ 2 * C * |f n t| + G * t ^ (dL + sL - 1) := by
    have hscalar (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 (T : ℝ)) (huv : (1 + β) * arrival n u ≤ v) :
        |(X n T).2.1 u v 1| ≤ Hs * Real.exp (-cL * v) :=
      ((hclosed n T u hu v huv).1).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hHs]) (Real.exp_pos _).le)
    filter_upwards [(hX n T).choose_spec.2.2.2.2.1 cL Hs hcL hHs.le hscalar] with t ht
    intro v ht0 htv
    convert (ht v ht0 htv).2 dL hdL hdn hgap using 1
    dsimp only [G, K, dL, sL]; ring_nf
  have hconformalDecay (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc 0 U) (hu : 0 < (u : ℝ))
      (v : Icc 0 (T : ℝ)) (huv : (1 + β) * arrival n u ≤ v) :
      |(X n T).2.1 u v 2 + 2 * B.innerRate| ≤ Edec * Real.exp (-ηE * v) := by
    let γ := fun t => (1 + β) * arrival n t
    have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (u : ℝ) :=
      (show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and
        ((eventually_lt_nhds hu).filter_mono nhdsWithin_le_nhds)
    obtain ⟨z₀, hz₀, hzV⟩ := (hnear.and (((hal n).const_mul_atTop hα).eventually
      (eventually_gt_atTop (v : ℝ)))).exists
    have hsub : Icc z₀ (u : ℝ) ⊆ Ioc 0 U :=
      fun _ ht => ⟨hz₀.1.trans_le ht.1, ht.2.trans u.property.2⟩
    obtain ⟨z, hz, hzt⟩ := intermediate_value_Icc' hz₀.2.le
      ((((hac n).mono hdom).const_mul (1 + β)).mono hsub) ⟨huv, hzV.le⟩
    let z' : Icc 0 U := ⟨z, (hsub hz).1.le, (hsub hz).2⟩
    have hz0 := (hsub hz).1
    have hlate (t : ℝ) (ht : t ∈ Icc z u) : γ t ≤ v :=
      (mul_le_mul_of_nonneg_left ((haa n).antitoneOn (hdom (hsub hz))
        (hdom ⟨hz0.trans_le ht.1, ht.2.trans u.property.2⟩) ht.1) hα.le).trans_eq hzt
    have hbound := (hX n T).choose.late_conformal_source_bound hU.le T.property hUR hp hpq (hfU n)
      (O := Odec * Real.exp (-ηO * v)) (N := 2 * N) (L := Ldec * Real.exp (-ηL * v))
      (H := Hs / 2 * Real.exp (-cL * v)) (P := P) (C := 2 * C) (G := G) (d := dL / 2) (s := dL + sL)
      hρ (by positivity) (by positivity) (by positivity) (by positivity) hP (by positivity) hG
      (by positivity) (add_pos hdL hsL) z' u hz0 hz.2 v (by
        intro w hw
        have hw0 : 0 < (w : ℝ) := hz0.trans_le hw.1
        have hlatew := hlate w hw
        refine ⟨(hX n T).choose_spec.1 w v, ?_, ?_, hlateLambda n T w hw0 v hlatew,
          (hclosed n T w hw0 v hlatew).1, ?_⟩
        · exact (hnuPower n T w hw0 v hlatew).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hw0 (w.property.2.trans (hUU.trans _hU1))
              (by linarith only [hdL] : dL / 2 - 1 ≤ dL - 1)) (by positivity))
        · exact (hlapse n T w hw0 v hlatew).trans_eq (by ring)
        · apply hpot _ ⟨(hX n T).choose_spec.1 w v, ?_⟩
          have hh := ((hX n T).choose_spec.2.1 w hw0 v hlatew).2.1
          linarith only [hh, hΔr, B.inner_pos]) (by
        filter_upwards [hfuture n T] with t ht
        intro htm
        exact ht v (hz0.trans_le htm.1) (hlate t htm))
    have hrate (b : ℝ) (hb : ηE ≤ b) : Real.exp (-b * (v : ℝ)) ≤ Real.exp (-ηE * v) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hb) v.property.1)
    have heO := hrate ηO ((min_le_right _ _).trans (min_le_left _ _))
    have heL := hrate ηL ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hec := hrate cL ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hgdec : ((Odec * Real.exp (-ηO * v)) * P +
        2 * (Ldec * Real.exp (-ηL * v)) * (2 * N) / (3 * B.inner / 4) ^ 2) ≤
        (Odec * P + 2 * Ldec * (2 * N) / (3 * B.inner / 4) ^ 2) * Real.exp (-ηE * v) := by
      calc
        _ = (Odec * P) * Real.exp (-ηO * v) +
            (2 * Ldec * (2 * N) / (3 * B.inner / 4) ^ 2) * Real.exp (-ηL * v) := by ring
        _ ≤ (Odec * P) * Real.exp (-ηE * v) +
            (2 * Ldec * (2 * N) / (3 * B.inner / 4) ^ 2) * Real.exp (-ηE * v) :=
          add_le_add (mul_le_mul_of_nonneg_left heO (by positivity))
            (mul_le_mul_of_nonneg_left heL (by positivity))
        _ = _ := by ring
    have hpw (b : ℝ) (hb : 0 ≤ b) : U ^ b ≤ Ws ^ b := Real.rpow_le_rpow hU.le hUWs hb
    have hgeo := div_le_div_of_nonneg_right
      (mul_le_mul hgdec (hpw (dL / 2) (by positivity))
        (Real.rpow_nonneg hU.le (dL / 2)) (by positivity)) (show 0 ≤ dL / 2 by positivity)
    have hnorm := (scalar_prefix_norm_le hUδ (hf n)).trans (hfn n)
    have hsnorm := add_le_add (mul_le_mul
      (mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * C by positivity))
        (hpw (1 / q) (one_div_nonneg.2 hpq.symm.pos.le))
        (Real.rpow_nonneg hU.le (1 / q)) (by positivity))
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hpw (dL + sL) (add_pos hdL hsL).le) hG) (add_pos hdL hsL).le)
    have hsc1 : 2 * (Hs / 2 * Real.exp (-cL * v)) ≤ Hs * Real.exp (-ηE * v) := by
      calc
        _ = Hs * Real.exp (-cL * v) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hec hHs.le
    have hscdec := mul_le_mul hsc1 hsnorm (by positivity) (by positivity)
    have hsource := hbound.trans (add_le_add hgeo hscdec)
    have hg := ((hX n T).choose_spec.2.2.1 z' hz0 (hzt.le.trans v.property.2)).2.1
    simp only [z', hzt, projIcc_of_mem T.property v.property] at hg
    have hgamma := hg.trans (mul_le_mul_of_nonneg_left (hrate τ (min_le_left _ _)) hL.le)
    have hh := (abs_add_le ((X n T).2.1 u v 2 - (X n T).2.1 z' v 2)
      ((X n T).2.1 z' v 2 + 2 * B.innerRate)).trans (add_le_add hsource hgamma)
    rw [← add_assoc, sub_add_cancel] at hh
    exact hh.trans_eq (by dsimp only [Edec, Egeom, Escalar]; ring)
  have hconformalTail (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc 0 U) (hu : 0 < (u : ℝ))
      (a b : Icc 0 (T : ℝ)) (hua : (1 + β) * arrival n u ≤ a) (hab : a ≤ b) :
      |(X n T).1 u b 2 - (X n T).1 u a 2 + 2 * B.innerRate * ((b : ℝ) - a)| ≤
        Edec / ηE * Real.exp (-ηE * a) := by
    have hh := ((hX n T).choose.conformal_remainder_bound u a b hab hEdec.le hηE
      (K := fun _ => -B.innerRate) (k := B.innerRate) (J := 0) continuous_const (by
        intro w hw
        simpa only [mul_neg, sub_neg_eq_add] using hconformalDecay n T u hu w (hua.trans hw.1)) (by simp)).1
    simpa only [mul_zero, add_zero] using hh
  have hcornerAll : ∀ n (T : Ici (0 : ℝ)) (u : Icc 0 U), 0 < (u : ℝ) →
    ∀ v : Icc 0 (T : ℝ), (1 + β) * arrival n u ≤ v →
      let a := projIcc 0 (T : ℝ) T.property (arrival n u)
      |(X n T).1 u v 2 - (X n T).1 u a 2 + 2 * B.innerRate * ((v : ℝ) - arrival n u)| ≤ Rmatch ∧
      Real.exp (-Rmatch) * (Real.exp ((X n T).1 u a 2) *
        Real.exp (-2 * B.innerRate * ((v : ℝ) - arrival n u))) ≤ Real.exp ((X n T).1 u v 2) ∧
      Real.exp ((X n T).1 u v 2) ≤ Real.exp Rmatch * (Real.exp ((X n T).1 u a 2) *
        Real.exp (-2 * B.innerRate * ((v : ℝ) - arrival n u))) ∧
      Olo ≤ (u : ℝ) * Real.exp ((X n T).1 u a 2) ∧
      (u : ℝ) * Real.exp ((X n T).1 u a 2) ≤ Ohi ∧
      Olo * (u : ℝ) ≤ -(X n T).2.1 u a 0 / Real.exp ((X n T).1 u a 2) ∧
      -(X n T).2.1 u a 0 / Real.exp ((X n T).1 u a 2) ≤ Ohi * (u : ℝ) ∧
      (Real.exp (-Rmatch) * Olo * j ^ (2 * B.innerRate / B.outerRate)) *
        ((u : ℝ) ^ (-1 - 2 * B.innerRate / B.outerRate) * Real.exp (-2 * B.innerRate * v)) ≤
          Real.exp ((X n T).1 u v 2) ∧
      Real.exp ((X n T).1 u v 2) ≤ (Real.exp Rmatch * Ohi * D ^ (2 * B.innerRate / B.outerRate)) *
        ((u : ℝ) ^ (-1 - 2 * B.innerRate / B.outerRate) * Real.exp (-2 * B.innerRate * v)) := by
    intro n T u hu v huv
    have hG : 0 ≤ (1 + β) * arrival n u := mul_nonneg hα.le (hpos n u (hdom ⟨hu, u.property.2⟩)).le
    have hgm : (1 + β) * arrival n u ∈ Icc 0 (T : ℝ) := ⟨hG, huv.trans v.property.2⟩
    let b : Icc 0 (T : ℝ) := ⟨(1 + β) * arrival n u, hgm⟩
    let a := projIcc 0 (T : ℝ) T.property (arrival n u)
    have hearly := ((hX n T).choose_spec.2.2.1 u hu hgm.2).2.2.2
    simp only [projIcc_of_mem T.property hgm] at hearly
    have hlate := hconformalTail n T u hu b v le_rfl huv
    have hexp : Real.exp (-ηE * (b : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hηE]) b.property.1)
    have hlate' := hlate.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (div_nonneg hEdec.le hηE.le))
    have hrem : |(X n T).1 u v 2 - (X n T).1 u a 2 +
        2 * B.innerRate * ((v : ℝ) - arrival n u)| ≤ Rmatch := by
      calc
        _ = |((X n T).1 u b 2 - (X n T).1 u a 2 +
              2 * B.innerRate * ((b : ℝ) - arrival n u)) +
            ((X n T).1 u v 2 - (X n T).1 u b 2 + 2 * B.innerRate * ((v : ℝ) - b))| := by congr 1; ring
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add hearly hlate')
    have ham : arrival n u ∈ Icc 0 (T : ℝ) := by
      refine ⟨(hpos n u (hdom ⟨hu, u.property.2⟩)).le, ?_⟩
      have hh : arrival n u ≤ (1 + β) * arrival n u := by
        nlinarith only [mul_nonneg hβ.le (hpos n u (hdom ⟨hu, u.property.2⟩)).le]
      exact hh.trans (huv.trans v.property.2)
    have ha : (a : ℝ) = arrival n u := by simp only [a, projIcc_of_mem T.property ham]
    have hm := hmatching n U T hU T.property hUR (hfU n) (hX n T).choose hUU u hu a ha
    have hcorner := corner_lapse_bounds hu B.outerRate_pos B.innerRate_pos.le hj hOhi.le
      (hscale n u (hdom ⟨hu, u.property.2⟩)) ⟨hm.1, hm.2.1⟩ hrem
    refine ⟨hrem, ?_, ?_, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hcorner⟩
    · rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith only [(abs_le.1 hrem).1]
    · rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith only [(abs_le.1 hrem).2]
  have hentry (ε : ℝ) (hε : 0 < ε) (n : ℕ) (u : Icc ε U) :
      (1 + β) * arrival n u ≤ max 0 (((1 + β) / B.outerRate) * Real.log (D / ε)) := by
    have hu : 0 < (u : ℝ) := hε.trans_le u.property.1
    have he : Real.exp (B.outerRate * arrival n u) ≤ D / ε := by
      apply (le_div_iff₀ hε).2
      calc
        _ = ε * Real.exp (B.outerRate * arrival n u) := mul_comm _ _
        _ ≤ (u : ℝ) * Real.exp (B.outerRate * arrival n u) :=
          mul_le_mul_of_nonneg_right u.property.1 (Real.exp_pos _).le
        _ ≤ _ := (hscale n u (hdom ⟨hu, u.property.2⟩)).2
    have hh := mul_le_mul_of_nonneg_left ((Real.le_log_iff_exp_le (div_pos hD hε)).2 he)
      (div_nonneg hα.le B.outerRate_pos.le)
    have hid : (1 + β) / B.outerRate * (B.outerRate * arrival n u) = (1 + β) * arrival n u := by
      field_simp [B.outerRate_pos.ne']
    rw [hid] at hh
    exact hh.trans (le_max_right _ _)
  have hboundary (ε : ℝ) (hε : 0 < ε) (_hεU : ε ≤ U) :
      ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∃ Z : ℕ → C(Icc ε U, WaveVector),
        (∀ n, Tendsto (renormalizedWaveRow hε.le B.innerRate (X n)) atTop (𝓝 (Z n))) ∧
        (∀ n t, T₀ ≤ t →
          ‖renormalizedWaveRow hε.le B.innerRate (X n) t - Z n‖ ≤
            (Ldec / ηL + (Hs / 2) / cL + Edec / ηE) *
              Real.exp (-(min ηL (min cL ηE)) * t)) ∧
        (∀ n u, 3 * B.inner / 4 ≤ Z n u 0) ∧
        (∀ n (u : Icc ε U), 0 < Real.exp (Z n u 2) ∧
          Tendsto (fun t => Real.exp (2 * B.innerRate * t) *
            Real.exp ((X n ⟨max 0 t, le_max_left (0 : ℝ) t⟩).1
              ⟨u, hε.le.trans u.property.1, u.property.2⟩
              ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ 2)) atTop (𝓝 (Real.exp (Z n u 2)))) ∧
        ∃ Alo Ahi : ℝ, 0 < Alo ∧ 0 < Ahi ∧
          (∀ n u, Alo ≤ waveAmplitude (Z n) u ∧ waveAmplitude (Z n) u ≤ Ahi) ∧
          (∀ n t, T₀ ≤ t → ∀ u,
            Alo ≤ waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t) u ∧
              waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t) u ≤ Ahi) ∧
          (∀ n, Tendsto (fun t => waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t))
            atTop (𝓝 (waveAmplitude (Z n)))) ∧
          (∀ n t, T₀ ≤ t →
            ‖waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t) - waveAmplitude (Z n)‖ ≤
              Ahi * (Ldec / ηL + (Hs / 2) / cL + Edec / ηE) *
                Real.exp (-(min ηL (min cL ηE)) * t)) ∧
          (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            Tendsto Z atTop (𝓝 (Z 0)) ∧
            TendstoUniformlyOn (fun n => renormalizedWaveRow hε.le B.innerRate (X n))
              (renormalizedWaveRow hε.le B.innerRate (X 0)) atTop (Ici 0) ∧
            Tendsto (fun n => waveAmplitude (Z n)) atTop (𝓝 (waveAmplitude (Z 0))) ∧
            TendstoUniformlyOn (fun n t => waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t))
              (fun t => waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X 0) t)) atTop (Ici 0)) := by
    let ηT := min ηL (min cL ηE)
    let Ctail := Ldec / ηL + (Hs / 2) / cL + Edec / ηE
    have hηT : 0 < ηT := lt_min hηL (lt_min hcL hηE)
    have hCt : 0 ≤ Ctail := by dsimp only [Ctail]; positivity
    have hterm₀ : 0 ≤ Ldec / ηL := by positivity
    have hterm₁ : 0 ≤ (Hs / 2) / cL := by positivity
    have hterm₂ : 0 ≤ Edec / ηE := by positivity
    let T₀ := max 0 (((1 + β) / B.outerRate) * Real.log (D / ε))
    have hT₀ : 0 ≤ T₀ := le_max_left _ _
    have hlimits (n : ℕ) := exists_renormalized_wave_limit (k := B.innerRate) hε.le hT₀ hCt hηT (X n) (hcompat n) (by
      intro T u a b ha hab i
      let w : Icc 0 U := ⟨u, hε.le.trans u.property.1, u.property.2⟩
      have hw : 0 < (w : ℝ) := hε.trans_le u.property.1
      have hentered : (1 + β) * arrival n w ≤ a := (hentry ε hε n u).trans ha
      have henv (C r : ℝ) (hCbound : C ≤ Ctail) (hr : ηT ≤ r) :
          C * Real.exp (-r * a) ≤ Ctail * Real.exp (-ηT * a) :=
        mul_le_mul hCbound (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg hr) a.property.1))
          (Real.exp_pos _).le hCt
      fin_cases i
      · change |(X n T).1 w b 0 - (X n T).1 w a 0 + 0| ≤ Ctail * Real.exp (-ηT * a)
        have hh := (hX n T).choose.longitudinal_tail_bound w 0 a b hab hLdec.le hηL
          (fun v hv => hlateLambda n T w hw v (hentered.trans hv.1))
        simpa only [add_zero] using
          hh.trans (henv (Ldec / ηL) ηL (by dsimp only [Ctail]; linarith only [hterm₁, hterm₂]) (min_le_left _ _))
      · change |(X n T).1 w b 1 - (X n T).1 w a 1 + 0| ≤ Ctail * Real.exp (-ηT * a)
        have hh := (hX n T).choose.longitudinal_tail_bound w 1 a b hab (by positivity : 0 ≤ Hs / 2) hcL
          (fun v hv => (hclosed n T w hw v (hentered.trans hv.1)).1)
        simpa only [add_zero] using
          hh.trans (henv ((Hs / 2) / cL) cL (by dsimp only [Ctail]; linarith only [hterm₀, hterm₂])
            ((min_le_right _ _).trans (min_le_left _ _)))
      · change |(X n T).1 w b 2 - (X n T).1 w a 2 + 2 * B.innerRate * ((b : ℝ) - a)| ≤
          Ctail * Real.exp (-ηT * a)
        have hh := hconformalTail n T w hw a b hentered hab
        exact hh.trans (henv (Edec / ηE) ηE (by dsimp only [Ctail]; linarith only [hterm₀, hterm₁])
            ((min_le_right _ _).trans (min_le_right _ _))))
    choose Z hZ hZtail hZamp using hlimits
    have hradius : ∀ n u, 3 * B.inner / 4 ≤ Z n u 0 := by
      intro n u
      have hz := ((continuous_apply 0).comp (continuous_eval_const u)).tendsto (Z n) |>.comp (hZ n)
      apply ge_of_tendsto' hz
      intro t
      change 3 * B.inner / 4 ≤ (X n ⟨max 0 t, le_max_left (0 : ℝ) t⟩).1
        ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩ 0 + 0
      simpa only [add_zero] using
        (hX n ⟨max 0 t, le_max_left (0 : ℝ) t⟩).choose_spec.1
          ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩
    let σA := -1 - 2 * B.innerRate / B.outerRate
    let Alo := (Real.exp (-Rmatch) * Olo * j ^ (2 * B.innerRate / B.outerRate)) * U ^ σA
    let Ahi := (Real.exp Rmatch * Ohi * D ^ (2 * B.innerRate / B.outerRate)) * ε ^ σA
    have hAlo : 0 < Alo := by dsimp only [Alo]; positivity
    have hAhi : 0 < Ahi := by dsimp only [Ahi]; positivity
    have hσA : σA ≤ 0 := by
      have hh := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) B.innerRate_pos.le) B.outerRate_pos.le
      dsimp only [σA]
      linarith only [hh]
    have hampBounds (n : ℕ) (t : ℝ) (ht : T₀ ≤ t) (u : Icc ε U) :
        Alo ≤ waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t) u ∧
          waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t) u ≤ Ahi := by
      let T : Ici (0 : ℝ) := ⟨max 0 t, le_max_left (0 : ℝ) t⟩
      have ht0 := hT₀.trans ht
      let v : Icc 0 (T : ℝ) := ⟨t, ht0, le_max_right 0 t⟩
      let w : Icc 0 U := ⟨u, hε.le.trans u.property.1, u.property.2⟩
      have hw : 0 < (w : ℝ) := hε.trans_le u.property.1
      have hh := (hcornerAll n T w hw v ((hentry ε hε n u).trans ht)).2.2.2.2.2.2.2
      have hlo := mul_le_mul_of_nonneg_left hh.1 (Real.exp_pos (2 * B.innerRate * t)).le
      have hhi := mul_le_mul_of_nonneg_left hh.2 (Real.exp_pos (2 * B.innerRate * t)).le
      have hcancel (d : ℝ) : Real.exp (2 * B.innerRate * t) *
          (d * ((u : ℝ) ^ σA * Real.exp (-2 * B.innerRate * t))) = d * (u : ℝ) ^ σA := by
        calc
          _ = (d * (u : ℝ) ^ σA) * (Real.exp (2 * B.innerRate * t) * Real.exp (-2 * B.innerRate * t)) := by ring
          _ = _ := by
            rw [← Real.exp_add, show 2 * B.innerRate * t + -2 * B.innerRate * t = 0 by ring, Real.exp_zero, mul_one]
      rw [hcancel] at hlo hhi
      rw [waveAmplitude_renormalizedWaveRow_apply hε.le (X n) (hcompat n) T ht0 (le_max_right 0 t) u]
      refine ⟨?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hw u.property.2 hσA) (by positivity)).trans hlo
      · exact hhi.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hε u.property.1 hσA) (by positivity))
    have hampLimit (n : ℕ) :
        Tendsto (fun t => waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t))
          atTop (𝓝 (waveAmplitude (Z n))) :=
      waveAmplitude.continuous.tendsto (Z n) |>.comp (hZ n)
    have hampLimitBounds (n : ℕ) (u : Icc ε U) :
        Alo ≤ waveAmplitude (Z n) u ∧ waveAmplitude (Z n) u ≤ Ahi := by
      have hz := (continuous_eval_const u).tendsto (waveAmplitude (Z n)) |>.comp (hampLimit n)
      exact ⟨ge_of_tendsto hz ((eventually_ge_atTop T₀).mono (fun t ht => (hampBounds n t ht u).1)),
        le_of_tendsto hz ((eventually_ge_atTop T₀).mono (fun t ht => (hampBounds n t ht u).2))⟩
    have hampTail (n : ℕ) (t : ℝ) (ht : T₀ ≤ t) :
        ‖waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t) - waveAmplitude (Z n)‖ ≤
          (Ahi * Ctail) * Real.exp (-ηT * t) := by
      have hh := (waveAmplitude_norm_sub_le hAhi (fun u => (hampBounds n t ht u).2)
        (fun u => (hampLimitBounds n u).2)).trans (mul_le_mul_of_nonneg_left (hZtail n t ht) hAhi.le)
      simpa only [mul_assoc] using hh
    refine ⟨T₀, hT₀, Z, hZ, hZtail, hradius, hZamp, Alo, Ahi, hAlo, hAhi,
      hampLimitBounds, hampBounds, hampLimit, hampTail, ?_⟩
    intro hzero hlim
    have hdecay (C : ℝ) : Tendsto (fun t : ℝ => C * Real.exp (-ηT * t)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, id_eq, mul_zero] using
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hηT))).const_mul C
    have hseq := uniform_convergence_of_common_tail (hdecay Ctail)
      (fun n t ht => by simpa only [dist_eq_norm, ContinuousMap.id_apply] using hZtail n t ht)
      (fun t ht => by simpa only [dist_eq_norm, ContinuousMap.id_apply] using hZtail 0 t ht)
      (fun T hT => renormalizedWaveRow_tendstoUniformlyOn hε.le X (X 0) hcompat (hcompat 0)
        (ContinuousMap.id _) ⟨T, hT⟩ (hfinite hzero hlim ⟨T, hT⟩))
    have haseq := uniform_convergence_of_common_tail (hdecay (Ahi * Ctail))
      (fun n t ht => by simpa only [dist_eq_norm] using hampTail n t ht)
      (fun t ht => by simpa only [dist_eq_norm] using hampTail 0 t ht)
      (fun T hT => renormalizedWaveRow_tendstoUniformlyOn hε.le X (X 0) hcompat (hcompat 0)
        waveAmplitude ⟨T, hT⟩ (hfinite hzero hlim ⟨T, hT⟩))
    exact ⟨hseq.1, hseq.2, haseq.1, haseq.2⟩
  let W (n : ℕ) (T : Ici (0 : ℝ)) := radialProductField T.property B.charge B.cosmological
    (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n T).1 (hX n T).choose.choose
  have hfieldCompat (n : ℕ) (S T : Ici (0 : ℝ)) (hST : S ≤ T) (u : Icc 0 U) (v : Icc 0 (S : ℝ)) :
      (X n S).1 u v = (X n T).1 u ⟨v, v.property.1, v.property.2.trans hST⟩ := by
    have hh := congrArg (fun x : WaveState U (S : ℝ) => x.1 u v) (hcompat n S T hST)
    change (X n T).1 ⟨0 + (u : ℝ), by simpa using u.property.1, by simpa using u.property.2⟩
      ⟨0 + (v : ℝ), by simpa using v.property.1, by simpa using v.property.2.trans hST⟩ = (X n S).1 u v at hh
    simpa only [zero_add] using hh.symm
  have hνcompat (n : ℕ) (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v :
      ν n S u v = ν n T u ⟨v, v.property.1, v.property.2.trans hST⟩ :=
    radialNuField_prefix_eq S.property T.property hST B.charge B.cosmological
      _ _ _ (hX n T).choose.choose (hX n S).choose.choose (hfieldCompat n S T hST) u v
  have hWcompat (n : ℕ) (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v :
      W n S u v = W n T u ⟨v, v.property.1, v.property.2.trans hST⟩ := by
    change (X n S).1 u v 0 * ν n S u v =
      (X n T).1 u ⟨v, v.property.1, v.property.2.trans hST⟩ 0 *
        ν n T u ⟨v, v.property.1, v.property.2.trans hST⟩
    rw [hfieldCompat n S T hST, hνcompat n S T hST]
  obtain ⟨Pr, hPr, hPrbound⟩ := radialPotential_bounded B.charge B.cosmological (R := 3 * B.inner / 2) hρ
  have hradial : ∀ ε (hε : 0 < ε), ε ≤ U →
      ∃ T₀ Cw Cν : ℝ, 0 ≤ T₀ ∧ 0 ≤ Cw ∧ 0 ≤ Cν ∧
        ∃ Zw Zν : ℕ → C(Icc ε U, ℝ),
          (∀ n, Tendsto (scalarBoundaryRow hε.le (W n)) atTop (𝓝 (Zw n))) ∧
          (∀ n t, T₀ ≤ t → ‖scalarBoundaryRow hε.le (W n) t - Zw n‖ ≤ Cw * Real.exp (-(2 * B.innerRate) * t)) ∧
          (∀ n, Tendsto (scalarBoundaryRow hε.le (ν n)) atTop (𝓝 (Zν n))) ∧
          (∀ n t, T₀ ≤ t → ‖scalarBoundaryRow hε.le (ν n) t - Zν n‖ ≤
            Cν * Real.exp (-(min (2 * B.innerRate) ηL) * t)) ∧
          (∀ n u, Zν n u ≤ 0) ∧
          (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            Tendsto Zw atTop (𝓝 (Zw 0)) ∧
            TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (W n))
              (scalarBoundaryRow hε.le (W 0)) atTop (Ici 0) ∧
            Tendsto Zν atTop (𝓝 (Zν 0)) ∧
            TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (ν n))
              (scalarBoundaryRow hε.le (ν 0)) atTop (Ici 0)) ∧
          (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            MassCoefficientControl (fun n => massCoefficientRow hε.le B.innerRate (X n) (ν n))) := by
    intro ε hε hεU
    let T₀ := max 0 (((1 + β) / B.outerRate) * Real.log (D / ε))
    have hT₀ : 0 ≤ T₀ := le_max_left _ _
    let Oε := (Real.exp Rmatch * Ohi * D ^ (2 * B.innerRate / B.outerRate)) *
      ε ^ (-1 - 2 * B.innerRate / B.outerRate)
    let Nε := 2 * N * ε ^ (-1 : ℝ)
    let Fε := (3 * B.inner / 2) * Pr * Oε
    let Cw := Fε / (2 * B.innerRate)
    let Cν := (Cw + (Ldec / ηL) * Nε) / (3 * B.inner / 4)
    have hOε : 0 ≤ Oε := by dsimp only [Oε]; positivity
    have hNε : 0 ≤ Nε := by dsimp only [Nε]; positivity
    have hFε : 0 ≤ Fε := by dsimp only [Fε]; positivity [B.inner_pos]
    have hCw : 0 ≤ Cw := div_nonneg hFε (by positivity [B.innerRate_pos])
    have hCν : 0 ≤ Cν := by dsimp only [Cν]; positivity
    have h2k : 0 < 2 * B.innerRate := by positivity [B.innerRate_pos]
    have hntail (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc ε U) (v : Icc 0 (T : ℝ)) (hv : T₀ ≤ v) :
        |ν n T ⟨u, hε.le.trans u.property.1, u.property.2⟩ v| ≤ Nε := by
      let w : Icc 0 U := ⟨u, hε.le.trans u.property.1, u.property.2⟩
      have hw : 0 < (w : ℝ) := hε.trans_le u.property.1
      have hpow : (w : ℝ) ^ (dL - 1) ≤ ε ^ (-1 : ℝ) :=
        (Real.rpow_le_rpow_of_exponent_ge hw (w.property.2.trans (hUU.trans _hU1))
          (by linarith only [hdL] : (-1 : ℝ) ≤ dL - 1)).trans
          (Real.rpow_le_rpow_of_nonpos hε u.property.1 (by norm_num))
      exact (hnuPower n T w hw v ((hentry ε hε n u).trans hv)).trans
        (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hflux (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc ε U) (v : Icc 0 (T : ℝ)) (hv : T₀ ≤ v) :
        |radialFluxField B.charge B.cosmological (X n T).1 (hX n T).choose.choose
          ⟨u, hε.le.trans u.property.1, u.property.2⟩ v| ≤ Fε * Real.exp (-(2 * B.innerRate) * v) := by
      let w : Icc 0 U := ⟨u, hε.le.trans u.property.1, u.property.2⟩
      have hw : 0 < (w : ℝ) := hε.trans_le u.property.1
      have hentered := (hentry ε hε n u).trans hv
      have hrlo := (hX n T).choose_spec.1 w v
      have hrp := hρ.trans_le hrlo
      have hrhi : (X n T).1 w v 0 ≤ 3 * B.inner / 2 := by
        have hh := ((hX n T).choose_spec.2.1 w hw v hentered).2.1
        linarith only [hh, hΔr, B.inner_pos]
      have ho := (hcornerAll n T w hw v hentered).2.2.2.2.2.2.2.2
      have hpw := Real.rpow_le_rpow_of_nonpos hε u.property.1
        (by have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) B.innerRate_pos.le) B.outerRate_pos.le
            linarith : -1 - 2 * B.innerRate / B.outerRate ≤ 0)
      have ho' : Real.exp ((X n T).1 w v 2) ≤ Oε * Real.exp (-(2 * B.innerRate) * v) := by
        apply ho.trans
        simpa only [Oε, neg_mul, mul_assoc] using
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpw (Real.exp_pos _).le)
            (by positivity : 0 ≤ Real.exp Rmatch * Ohi * D ^ (2 * B.innerRate / B.outerRate))
      rw [radialFluxField_apply, abs_mul, abs_mul, abs_of_pos hrp, abs_of_pos (Real.exp_pos _)]
      have hp := mul_le_mul hrhi (hPrbound _ ⟨hrlo, hrhi⟩) (abs_nonneg _) (by positivity [B.inner_pos])
      have hh := mul_le_mul hp ho' (Real.exp_pos _).le (mul_nonneg (by positivity [B.inner_pos]) hPr)
      calc
        _ = ((X n T).1 w v 0 * |radialPotential ((X n T).1 w v 0) B.charge B.cosmological|) *
            Real.exp ((X n T).1 w v 2) := by ring
        _ ≤ ((3 * B.inner / 2) * Pr) * (Oε * Real.exp (-(2 * B.innerRate) * v)) := hh
        _ = _ := by dsimp only [Fε]; ring
    have hWtail (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc ε U) (a b : Icc 0 (T : ℝ))
        (ha : T₀ ≤ a) (hab : a ≤ b) :
        |W n T ⟨u, hε.le.trans u.property.1, u.property.2⟩ b -
          W n T ⟨u, hε.le.trans u.property.1, u.property.2⟩ a| ≤ Cw * Real.exp (-(2 * B.innerRate) * a) :=
      radialProductField_tail_bound _ _ _ _ a b hab hFε h2k (fun t ht => hflux n T u t (ha.trans ht.1))
    have hνtail (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc ε U) (a b : Icc 0 (T : ℝ))
        (ha : T₀ ≤ a) (hab : a ≤ b) :
        |ν n T ⟨u, hε.le.trans u.property.1, u.property.2⟩ b -
          ν n T ⟨u, hε.le.trans u.property.1, u.property.2⟩ a| ≤
            Cν * Real.exp (-(min (2 * B.innerRate) ηL) * a) := by
      let w : Icc 0 U := ⟨u, hε.le.trans u.property.1, u.property.2⟩
      have hrlo := (hX n T).choose_spec.1 w b
      have hrp := hρ.trans_le hrlo
      have hr := (hX n T).choose.longitudinal_tail_bound w 0 a b hab hLdec.le hηL
        (fun t ht => hlateLambda n T w (hε.trans_le u.property.1) t ((hentry ε hε n u).trans (ha.trans ht.1)))
      have hprod := mul_le_mul hr (hntail n T u a ha) (abs_nonneg _) (by positivity : 0 ≤ Ldec / ηL * Real.exp (-ηL * a))
      rw [← abs_mul] at hprod
      have hnum := (abs_sub (W n T w b - W n T w a)
        (((X n T).1 w b 0 - (X n T).1 w a 0) * ν n T w a)).trans
          (add_le_add (hWtail n T u a b ha hab) hprod)
      have hid : ν n T w b - ν n T w a =
          ((W n T w b - W n T w a) - ((X n T).1 w b 0 - (X n T).1 w a 0) * ν n T w a) /
            (X n T).1 w b 0 := by
        change _ = (((X n T).1 w b 0 * ν n T w b - (X n T).1 w a 0 * ν n T w a) -
          ((X n T).1 w b 0 - (X n T).1 w a 0) * ν n T w a) / (X n T).1 w b 0
        field_simp [hrp.ne']
        ring
      change |ν n T w b - ν n T w a| ≤ _
      rw [hid, abs_div, abs_of_pos hrp]
      apply (div_le_div_of_nonneg_left (abs_nonneg _) hρ hrlo).trans
      apply (div_le_div_of_nonneg_right hnum hρ.le).trans
      have he₂ := Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left (2 * B.innerRate) ηL)) a.property.1)
      have heL := Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right (2 * B.innerRate) ηL)) a.property.1)
      have hh := add_le_add (mul_le_mul_of_nonneg_left he₂ hCw)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heL (div_nonneg hLdec.le hηL.le)) hNε)
      have hdiv := div_le_div_of_nonneg_right hh hρ.le
      convert hdiv using 1
      simp only [Cν]
      ring
    choose Zw hw hwerr using fun n => exists_scalar_boundary_limit hε.le hT₀ hCw h2k
      (W n) (hWcompat n) (hWtail n)
    choose Zν hn hnerr using fun n => exists_scalar_boundary_limit hε.le hT₀ hCν (lt_min h2k hηL)
      (ν n) (hνcompat n) (hνtail n)
    have hsign (n : ℕ) (u : Icc ε U) : Zν n u ≤ 0 := by
      apply le_of_tendsto ((continuous_eval_const u).tendsto (Zν n) |>.comp (hn n))
      apply Eventually.of_forall
      intro t
      exact (hga n ⟨max 0 t, le_max_left (0 : ℝ) t⟩
        ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩).2.2.1.le
    suffices hseq : f 0 = 0 →
        Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
          Tendsto Zw atTop (𝓝 (Zw 0)) ∧
          TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (W n))
            (scalarBoundaryRow hε.le (W 0)) atTop (Ici 0) ∧
          Tendsto Zν atTop (𝓝 (Zν 0)) ∧
          TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (ν n))
            (scalarBoundaryRow hε.le (ν 0)) atTop (Ici 0) by
      refine ⟨T₀, Cw, Cν, hT₀, hCw, hCν, Zw, Zν, hw, hwerr, hn, hnerr, hsign, hseq, ?_⟩
      intro hzero hlim
      obtain ⟨Ta, hTa, Z, hZ, hZtail, _hR, _hZA, Alo, Ahi, hAlo, _hAhi,
        hAlim, hArow, _hAlimT, _hAtail, hAseq⟩ := hboundary ε hε hεU
      let ηZ := min ηL (min cL ηE)
      let ηN := min (2 * B.innerRate) ηL
      let Cz := Ldec / ηL + (Hs / 2) / cL + Edec / ηE
      let Tc := max T₀ Ta
      let ηc := min ηN ηZ
      let Kc := 2 / Alo
      let Cc := Kc * (Cν + Nε * Cz)
      let Mc := Kc * Nε
      let Q := fun n => waveMassCoefficient (Zν n, Z n)
      have hηZ : 0 < ηZ := lt_min hηL (lt_min hcL hηE)
      have hηN : 0 < ηN := lt_min h2k hηL
      have hηc : 0 < ηc := lt_min hηN hηZ
      have hCz : 0 ≤ Cz := by dsimp only [Cz]; positivity
      have hKc : 0 < Kc := div_pos (by norm_num) hAlo
      have hMc : 0 ≤ Mc := mul_nonneg hKc.le hNε
      have hCc : 0 ≤ Cc := mul_nonneg hKc.le (add_nonneg hCν (mul_nonneg hNε hCz))
      have hNr (n : ℕ) (t : ℝ) (ht : T₀ ≤ t) : ‖scalarBoundaryRow hε.le (ν n) t‖ ≤ Nε := by
        apply (ContinuousMap.norm_le _ hNε).2
        intro u
        change |ν n ⟨max 0 t, le_max_left (0 : ℝ) t⟩
          ⟨u, hε.le.trans u.property.1, u.property.2⟩ ⟨max 0 t, le_max_left (0 : ℝ) t, le_rfl⟩| ≤ Nε
        exact hntail n _ u _ (ht.trans (le_max_right _ _))
      have hNl (n : ℕ) : ‖Zν n‖ ≤ Nε :=
        le_of_tendsto (hn n).norm ((eventually_ge_atTop T₀).mono (fun t ht => hNr n t ht))
      have hQt (n : ℕ) : Tendsto (massCoefficientRow hε.le B.innerRate (X n) (ν n)) atTop (𝓝 (Q n)) :=
        waveMassCoefficient.continuous.tendsto (Zν n, Z n) |>.comp ((hn n).prodMk_nhds (hZ n))
      refine ⟨Tc, Mc, Cc, ηc, hT₀.trans (le_max_left _ _), hMc, hCc, hηc, Q, hQt, ?_, ?_, ?_, ?_⟩
      · intro n t ht
        have htN : T₀ ≤ t := (le_max_left _ _).trans ht
        have htZ : Ta ≤ t := (le_max_right _ _).trans ht
        have hgeom := fun u => (hArow n t htZ u).1
        have hzeroC : waveMassCoefficient (0, renormalizedWaveRow hε.le B.innerRate (X n) t) = 0 := by
          ext u
          simp only [waveMassCoefficient, ContinuousMap.coe_mk, ContinuousMap.zero_apply, zero_mul, smul_zero]
        have hbound := waveMassCoefficient_norm_sub_le (N := scalarBoundaryRow hε.le (ν n) t)
          (M := 0) (L := 0) hAlo (by simp) hgeom hgeom
        simp only [hzeroC, sub_zero, sub_self, norm_zero, mul_zero, add_zero] at hbound
        refine ⟨hbound.trans (mul_le_mul_of_nonneg_left (hNr n t htN) hKc.le), ?_⟩
        have hb := waveMassCoefficient_norm_sub_le (N := scalarBoundaryRow hε.le (ν n) t)
          hAlo (hNl n) hgeom (fun u => (hAlim n u).1)
        have heN := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
          (neg_le_neg (min_le_left ηN ηZ)) (hT₀.trans htN))
        have heZ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
          (neg_le_neg (min_le_right ηN ηZ)) (hT₀.trans htN))
        have hnb := (hnerr n t htN).trans (mul_le_mul_of_nonneg_left heN hCν)
        have hzb := (hZtail n t htZ).trans (mul_le_mul_of_nonneg_left heZ hCz)
        apply hb.trans
        have hh := mul_le_mul_of_nonneg_left
          (add_le_add hnb (mul_le_mul_of_nonneg_left hzb hNε)) hKc.le
        convert hh using 1
        dsimp only [Cc, Kc, ηc, Cz, ηN, ηZ]
        ring
      · intro n u
        change 0 ≤ -2 * (Zν n u * Real.exp (-Z n u 2))
        exact mul_nonneg_of_nonpos_of_nonpos (by norm_num)
          (mul_nonpos_of_nonpos_of_nonneg (hsign n u) (Real.exp_pos _).le)
      · exact waveMassCoefficient.continuous.tendsto (Zν 0, Z 0) |>.comp
          (((hseq hzero hlim).2.2.1).prodMk_nhds (hAseq hzero hlim).1)
      · apply Metric.tendstoUniformlyOn_iff.2
        intro e he
        let K := Kc * (1 + Nε) + 1
        have hK : 0 < K := by dsimp only [K]; positivity
        let d := e / K
        have hd : 0 < d := div_pos he hK
        filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hseq hzero hlim).2.2.2 d hd,
          Metric.tendstoUniformlyOn_iff.1 (hAseq hzero hlim).2.1 d hd] with n hnn hzn
        intro t ht
        have htN : T₀ ≤ t := (le_max_left _ _).trans ht
        have htZ : Ta ≤ t := (le_max_right _ _).trans ht
        have hnt := hnn t (hT₀.trans htN)
        have hzt := hzn t (hT₀.trans htN)
        rw [dist_comm, dist_eq_norm] at hnt hzt ⊢
        have hb := waveMassCoefficient_norm_sub_le (N := scalarBoundaryRow hε.le (ν n) t) hAlo (hNr 0 t htN)
          (fun u => (hArow n t htZ u).1) (fun u => (hArow 0 t htZ u).1)
        apply lt_of_le_of_lt hb
        calc
          _ ≤ Kc * (d + Nε * d) := mul_le_mul_of_nonneg_left
            (add_le_add hnt.le (mul_le_mul_of_nonneg_left hzt.le hNε)) hKc.le
          _ < K * d := by dsimp only [K]; nlinarith only [hd]
          _ = e := mul_div_cancel₀ e hK.ne'
    intro hzero hlim
    have hRfinite (T : Ici (0 : ℝ)) :
        Tendsto (fun n => ν n T) atTop (𝓝 (ν 0 T)) ∧
          Tendsto (fun n => W n T) atTop (𝓝 (W 0 T)) :=
      IsWaveIntegral.radial_tendsto (fun n => (hX n T).choose) (hX 0 T).choose
        (fun n => (hX n T).choose.choose) (hX 0 T).choose.choose (hfinite hzero hlim T).fst_nhds
    have hdecay (C η : ℝ) (hη : 0 < η) : Tendsto (fun t : ℝ => C * Real.exp (-η * t)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, id_eq, mul_zero] using
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hη))).const_mul C
    have hwseq := uniform_convergence_of_common_tail (hdecay Cw _ h2k)
      (fun n t ht => by simpa only [dist_eq_norm] using hwerr n t ht)
      (fun t ht => by simpa only [dist_eq_norm] using hwerr 0 t ht)
      (fun T hT => scalarBoundaryRow_tendstoUniformlyOn hε.le W (W 0) hWcompat (hWcompat 0)
        ⟨T, hT⟩ (hRfinite ⟨T, hT⟩).2)
    have hnseq := uniform_convergence_of_common_tail (hdecay Cν _ (lt_min h2k hηL))
      (fun n t ht => by simpa only [dist_eq_norm] using hnerr n t ht)
      (fun t ht => by simpa only [dist_eq_norm] using hnerr 0 t ht)
      (fun T hT => scalarBoundaryRow_tendstoUniformlyOn hε.le ν (ν 0) hνcompat (hνcompat 0)
        ⟨T, hT⟩ (hRfinite ⟨T, hT⟩).1)
    exact ⟨hwseq.1, hwseq.2, hnseq.1, hnseq.2⟩
  let ζ := fun n (T : Ici (0 : ℝ)) => scalarTransportCorrection T.property (ν n T) (X n T).2.1
  have hζcompat (n : ℕ) (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v :
      ζ n S u v = ζ n T u ⟨v, v.property.1, v.property.2.trans hST⟩ :=
    scalarTransportCorrection_prefix_eq S.property T.property hST _ _ _ _
      (hνcompat n S T hST) (fun u v => (hvel n S T hST u v).symm) u v
  have hcorrection : ∀ ε (hε : 0 < ε), ε ≤ U →
      ∃ T₀ Cζ : ℝ, 0 ≤ T₀ ∧ 0 ≤ Cζ ∧ ∃ Zζ : ℕ → C(Icc ε U, ℝ),
        (∀ n, Tendsto (scalarBoundaryRow hε.le (ζ n)) atTop (𝓝 (Zζ n))) ∧
        (∀ n t, T₀ ≤ t → ‖scalarBoundaryRow hε.le (ζ n) t - Zζ n‖ ≤
          Cζ * Real.exp (-cL * t)) ∧
        (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
          Tendsto Zζ atTop (𝓝 (Zζ 0)) ∧
          TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (ζ n))
            (scalarBoundaryRow hε.le (ζ 0)) atTop (Ici 0)) := by
    intro ε hε _hεU
    let T₀ := max 0 (((1 + β) / B.outerRate) * Real.log (D / ε))
    let Nε := 2 * N * ε ^ (-1 : ℝ)
    let Cζ := (Nε * (Hs / 2)) / cL
    have hNε : 0 ≤ Nε := by dsimp only [Nε]; positivity
    have hsource : 0 ≤ Nε * (Hs / 2) := mul_nonneg hNε (by positivity)
    have hCζ : 0 ≤ Cζ := div_nonneg hsource hcL.le
    have htail (n : ℕ) (T : Ici (0 : ℝ)) (u : Icc ε U) (a b : Icc 0 (T : ℝ))
        (ha : T₀ ≤ a) (hab : a ≤ b) :
        |ζ n T ⟨u, hε.le.trans u.property.1, u.property.2⟩ b -
          ζ n T ⟨u, hε.le.trans u.property.1, u.property.2⟩ a| ≤ Cζ * Real.exp (-cL * a) := by
      let w : Icc 0 U := ⟨u, hε.le.trans u.property.1, u.property.2⟩
      have hw : 0 < (w : ℝ) := hε.trans_le u.property.1
      apply scalarTransportCorrection_tail_bound T.property (ν n T) (X n T).2.1 w a b hab hsource hcL
      intro v hv
      have hentered := (hentry ε hε n u).trans (ha.trans hv.1)
      have hpow : (w : ℝ) ^ (dL - 1) ≤ ε ^ (-1 : ℝ) :=
        (Real.rpow_le_rpow_of_exponent_ge hw (w.property.2.trans (hUU.trans _hU1))
          (by linarith only [hdL] : (-1 : ℝ) ≤ dL - 1)).trans
          (Real.rpow_le_rpow_of_nonpos hε u.property.1 (by norm_num))
      have hn := (hnuPower n T w hw v hentered).trans
        (mul_le_mul_of_nonneg_left hpow (by positivity))
      rw [abs_mul]
      exact (mul_le_mul hn (hclosed n T w hw v hentered).1 (abs_nonneg _) hNε).trans_eq
        (mul_assoc _ _ _).symm
    choose Zζ hz hzerr using fun n => exists_scalar_boundary_limit hε.le (le_max_left _ _)
      hCζ hcL (ζ n) (hζcompat n) (htail n)
    refine ⟨T₀, Cζ, le_max_left _ _, hCζ, Zζ, hz, hzerr, ?_⟩
    intro hzero hlim
    have hζfinite (T : Ici (0 : ℝ)) : Tendsto (fun n => ζ n T) atTop (𝓝 (ζ 0 T)) := by
      have hn := (IsWaveIntegral.radial_tendsto (fun n => (hX n T).choose) (hX 0 T).choose
        (fun n => (hX n T).choose.choose) (hX 0 T).choose.choose (hfinite hzero hlim T).fst_nhds).1
      let Q : WaveRectangle U (T : ℝ) →L[ℝ] C(Icc 0 U, C(Icc 0 (T : ℝ), ℝ)) :=
        ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U)
          (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 (T : ℝ)) (ContinuousLinearMap.proj (1 : Fin 3)))
      let P := ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 U) (continuousPrimitiveL (E := ℝ) T.property)
      have hw := (Q.continuous.tendsto (X 0 T).2.1).comp (hfinite hzero hlim T).snd_nhds.fst_nhds
      exact (P.continuous.tendsto _).comp (hn.neg.mul hw)
    have hdecay : Tendsto (fun t : ℝ => Cζ * Real.exp (-cL * t)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, id_eq, mul_zero] using
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hcL))).const_mul Cζ
    exact uniform_convergence_of_common_tail hdecay
      (fun n t ht => by simpa only [dist_eq_norm] using hzerr n t ht)
      (fun t ht => by simpa only [dist_eq_norm] using hzerr 0 t ht)
      (fun T hT => scalarBoundaryRow_tendstoUniformlyOn hε.le ζ (ζ 0) hζcompat (hζcompat 0)
        ⟨T, hT⟩ (hζfinite ⟨T, hT⟩))
  have hconstraint (hzero : f 0 = 0) (ε : ℝ) (hε : 0 < ε) (hεU : ε ≤ U) :
      TransverseBoundaryGeometry hε.le hεU B.innerRate (X 0) (ν 0) := by
    obtain ⟨_, _, Z, hZ, _, hR, _⟩ := hboundary ε hε hεU
    obtain ⟨_, _, _, _, _, _, _, Nh, _, _, hNlimit, _, hNsign, _, _⟩ := hradial ε hε hεU
    obtain ⟨_, _, _, _, Sh, hSlimit, _, _⟩ := hcorrection ε hε hεU
    have hdata := incomingWave_constraint_data hU.le hUR hp (hfU 0) (horizonPhi h r 0)
    have hinzero : ∀ᵐ u ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR hp (hfU 0) u 1 = 0 := by
      filter_upwards [incomingWaveVelocity_ae hUR hp (hfU 0)] with u hu
      rw [hu]
      change f 0 u = 0
      rw [hzero]
      rfl
    refine ⟨Z 0, Nh 0, Sh 0, hZ 0, hNlimit 0, hSlimit 0,
      (fun u => ⟨hρ.trans_le (hR 0 u), hNsign 0 u⟩), ?_⟩
    exact zero_scalar_boundary_constraint hU.le hε.le hεU _ _ _ (X 0)
      (fun T => (hX 0 T).choose) (fun T => (hX 0 T).choose.choose) rfl hdata.1 hdata.2 hinzero
      (Z 0) (Nh 0) (Sh 0) (hZ 0) (hNlimit 0) (hSlimit 0) (fun u => (hρ.trans_le (hR 0 u)).ne')
  have hreference (hzero : f 0 = 0) (T : Ici (0 : ℝ)) :
      (∀ u v, 0 < (X 0 T).1 u v 0 * (X 0 T).2.1 u v 1) ∧
      (∀ u (v : Icc 0 (T : ℝ)), 0 < (v : ℝ) → 0 < ζ 0 T u v) ∧
      ∀ u, Monotone (ζ 0 T u) := by
    have hx0 : IsWaveIntegral hU.le T.property B.charge B.cosmological
        (incomingWaveCurve hU.le hUR hp (f := fun _ : ℝ => (0 : ℝ)) MemLp.zero (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological T hc
          (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
          (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'))
        (incomingWaveVelocity hUR hp (f := fun _ : ℝ => (0 : ℝ)) MemLp.zero) (X 0 T) := by
      simpa only [hzero] using (hX 0 T).choose
    have hh := hSign U T hU.le T.property hUR p hp MemLp.zero (X 0 T) hx0 hUWsign
    simpa only [ζ, ν, hzero] using hh
  have hstrict (hzero : f 0 = 0) (ε : ℝ) (hε : 0 < ε) (hεU : ε ≤ U)
      (Nh : C(Icc ε U, ℝ)) (hNh : Tendsto (scalarBoundaryRow hε.le (ν 0)) atTop (𝓝 Nh)) :
      ∀ u, Nh u < 0 := by
    have hd : 0 < ε / 2 := half_pos hε
    have hdε : ε / 2 < ε := half_lt_self hε
    obtain ⟨Zd, Nd, Sd, _hZd, hNd, hSd, hsign, hcon⟩ :=
      hconstraint hzero (ε / 2) hd (hdε.le.trans hεU)
    have hSdpos := scalarBoundaryRow_pos_of_monotone hd.le (ζ 0) (hζcompat 0)
      (fun T u => (hreference hzero T).2.2 u)
      (fun u => (hreference hzero ⟨1, (show (0 : ℝ) ≤ 1 from zero_le_one)⟩).2.1 u
        ⟨1, zero_le_one, le_rfl⟩ zero_lt_one) Sd hSd
    intro u
    let ud : Icc (ε / 2) U := ⟨u, hdε.le.trans u.property.1, u.property.2⟩
    have hneg := hcon.strict_negative (fun w => (hsign w).1) (fun w => (hsign w).2)
      hSdpos ud (hdε.trans_le u.property.1)
    have hlim := ((continuous_eval_const u).tendsto Nh).comp hNh
    have hlimd := ((continuous_eval_const ud).tendsto Nd).comp hNd
    have he : Nh u = Nd ud := tendsto_nhds_unique hlim hlimd
    rwa [he]
  refine ⟨arrival, X, (fun n => ⟨(hac n).mono hdom, (haa n).mono hdom, hal n,
    fun u hu => hpos n u (hdom hu)⟩), (fun n u hu => hscale n u (hdom hu)),
    fun n T => (hX n T).choose, fun n T => (hX n T).choose_spec.1, ?_, hauxFamily, ?_, ?_, ?_, hclosed, hlateLambda, ?_,
    hlapse, hconformalDecay, hconformalTail, hcornerAll, hboundary,
    ⟨fun n T => (hX n T).choose.choose, hnuPower, hradial, hcorrection, hconstraint⟩, hcompat, hfinite⟩
  · intro n T u hu v
    exact ⟨fun hv => (hmatching n U T hU T.property hUR (hfU n) (hX n T).choose hUU u hu v hv).2.2.2.2,
      fun hv => hpre n hU.le T.property hUR (hfU n) (hX n T).choose u (hdom ⟨hu, u.property.2⟩)
        u le_rfl v hv⟩
  · intro ℓ Bn hlog hBn hBnBudget
    have hfRad (n : ℕ) : MemLp (logarithmicIncoming (1 - 1 / p.toReal) (ℓ n) (Bn n)) p
        (volume.restrict (Icc 0 δr)) := by
      simpa only [hlog n] using (hf n).mono_measure
        (Measure.restrict_mono (Icc_subset_Icc le_rfl hδrδ) le_rfl)
    have hradProfiles (n : ℕ) := henergy (ℓ n) (Bn n) (hBn n) (hfRad n)
      (by simpa only [hlog n] using (scalar_prefix_norm_le hδrδ (hf n)).trans (hfn n))
      (by
        filter_upwards [ae_mono
          (Measure.restrict_mono (Icc_subset_Icc le_rfl hδrδ) le_rfl)
          (hpoint n)] with t ht
        simpa only [hlog n] using ht)
    choose g hgc hga hgl hdc hgstart hgp hradPhysical using hradProfiles
    have hradData :
      ∀ n (V : Ici (0 : ℝ)),
        ∃ (w : C(Icc 0 (V : ℝ), ℝ)) (hw0 : ∀ v, 0 ≤ w v),
          (∀ v, w v = g n (max Tr (v : ℝ))) ∧ Antitone w ∧
          (∀ v : Icc 0 (V : ℝ), Tr ≤ v → g n v ≤ U →
            (X n V).1 (projIcc 0 U hU.le (g n v)) v 0 = Yr) ∧
          RadiationGammaCharts hU.le V.property (X n V) (g n) Tr (1 + β) ηr Cr Yr ∧
          (∀ t : ℝ, Tr ≤ t → g n t ≤ U → t ≤ V → arrival n (g n t) < t) ∧
          (∀ t : ℝ, Tr ≤ t → g n t ≤ U → (1 + β) * t ≤ V →
            let u := projIcc 0 U hU.le (g n t)
            let a := projIcc 0 (V : ℝ) V.property t
            Drlo * g n t ≤ -(X n V).2.1 u a 0 / Real.exp ((X n V).1 u a 2) ∧
            -(X n V).2.1 u a 0 / Real.exp ((X n V).1 u a 2) ≤ Drhi * g n t ∧
            (∫ v in t..(1 + β) * t, intervalExtension V.property ((X n V).1 u) v 0 *
              (intervalExtension V.property ((X n V).2.1 u) v 1) ^ 2 /
                (-intervalExtension V.property ((X n V).2.1 u) v 0)) ≤ 1 / 16 ∧
            ∀ hr : ∀ q v, (X n V).1 q v 0 ≠ 0,
              let ν' := radialNuField V.property B.charge B.cosmological
                (incomingWaveCurve hU.le hUR hp (hfU n) (horizonPhi h r 0)) (X n V).1 hr
              ∀ a' b' : Icc 0 (V : ℝ), t ≤ a' → a' ≤ b' → (b' : ℝ) ≤ (1 + β) * t →
                B.inner / 2 ≤ (X n V).1 u b' 0 ∧
                |ν' u b'| ≤ (2 * Real.exp 2) * (-ν' u a') * Real.exp (-2 * B.innerRate * ((b' : ℝ) - a')) ∧
                |(X n V).2.1 u b' 0| ≤ (Real.exp (2 + 1 / 16) * (-(X n V).2.1 u a' 0)) *
                  Real.exp (-2 * B.innerRate * ((b' : ℝ) - a'))) ∧
          ((∀ t : ℝ, Tr ≤ t → g n t ≤ U → ∀ v : Icc 0 (V : ℝ), (1 + β) * t ≤ v →
            let u := projIcc 0 U hU.le (g n t)
            (∫ w in t..(v : ℝ), intervalExtension V.property ((X n V).1 u) w 0 *
              (intervalExtension V.property ((X n V).2.1 u) w 1) ^ 2 /
                (-intervalExtension V.property ((X n V).2.1 u) w 0)) ≤ 1 / 4) →
            let S := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 (V : ℝ)) U)
              (fun _ => hU.le) 0 B.innerRate 0 (X n V)
            ((∫ t in (0 : ℝ)..(V : ℝ), (S (projIcc 0 (V : ℝ) V.property t)) ^ 2) ≤
              Er₀ + Er₁ * ∫ t, Bn n t ^ 2) ∧
            let W : C(Icc 0 (V : ℝ), ℝ) :=
              ⟨fun v => w (projIcc 0 (V : ℝ) V.property ((v : ℝ) / (1 + β))), by fun_prop⟩
            (∫ t in (0 : ℝ)..(V : ℝ),
              (Real.exp (ξrad * t) * ‖lateRadiationDifferenceRows hU.le W B.innerRate (X n V)
                (projIcc 0 (V : ℝ) V.property t)‖) ^ 2) ≤ Ed) ∧
          let W : C(Icc 0 (V : ℝ), ℝ) :=
            ⟨fun v => w (projIcc 0 (V : ℝ) V.property ((v : ℝ) / (1 + β))), by fun_prop⟩
          let hW0 := fun v : Icc 0 (V : ℝ) => hw0 (projIcc 0 (V : ℝ) V.property ((v : ℝ) / (1 + β)))
          let M := movingSpatialRadiationEnvelope W hW0 0 B.innerRate 0 (X n V)
          let Z := fun t v : ℝ => g n t * Real.exp (B.innerRate * t) *
            (intervalExtension V.property (intervalExtension hU.le (X n V).1 (g n t)) v 0 *
              derivWithin (fun u => intervalExtension V.property (intervalExtension hU.le (X n V).1 u) v 1)
                (Icc 0 U) (g n t))
          (∫ t in (0 : ℝ)..(V : ℝ), (M (projIcc 0 (V : ℝ) V.property t)) ^ 2) ≤
            E₀ + E₁ * ∫ t, Bn n t ^ 2 ∧
          ∀ a b : ℝ, Tr ≤ a → a ≤ b → (1 + β) * b ≤ V → g n a ≤ U →
            (∫ t in a..b, (Z t ((1 + β) * t)) ^ 2) ≤
              2 * (F₀ + F₁ * ∫ t, Bn n t ^ 2) +
                2 * ((2 * Real.exp 1) * Dr / (B.inner / 2) / (3 * B.innerRate)) ^ 2 *
                  (E₀ + E₁ * ∫ t, Bn n t ^ 2) := by
      intro n V
      have hfLogU : MemLp (logarithmicIncoming (1 - 1 / p.toReal) (ℓ n) (Bn n)) p
          (volume.restrict (Icc 0 U)) := by simpa only [hlog n] using hfU n
      have hxLog : IsWaveIntegral hU.le V.property B.charge B.cosmological
          (incomingWaveCurve hU.le hUR hp hfLogU (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc
            (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
            (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'))
          (incomingWaveVelocity hUR hp hfLogU) (X n V) := by
        simpa only [hlog n] using (hX n V).choose
      obtain ⟨w, hw0, hw, hwa, hlevel, hoptical, hME, _htrace, _hpointGamma, hGE⟩ :=
        hradPhysical n U V hU V.property hUR hUUr hfLogU (X n V) hxLog
      have hcharts := exists_radiation_gamma_chart hU.le V.property hTr.le
        (by linarith only [hβ] : 1 ≤ 1 + β) hηr hCr (hgc n) (hga n) (hgl n) (hdc n)
        (hUUr.trans_lt (hgstart n))
        (fun t ht => ⟨(hgp n t ht).1, (hgp n t ht).2.2.1,
          (hgp n t ht).2.2.2.1, (hgp n t ht).2.2.2.2.2⟩) (X n V) hlevel
      have horder (t : ℝ) (hTt : Tr ≤ t) (hgtU : g n t ≤ U) (htV : t ≤ V) :
          arrival n (g n t) < t := by
        have hgt := (hgp n t hTt).1
        let u : Icc 0 U := ⟨g n t, hgt.le, hgtU⟩
        let v : Icc 0 (V : ℝ) := ⟨t, hTr.le.trans hTt, htV⟩
        have hrad := hlevel v hTt hgtU
        change (X n V).1 (projIcc 0 U hU.le (g n t)) v 0 = Yr at hrad
        rw [show projIcc 0 U hU.le (g n t) = u from projIcc_of_mem hU.le u.property] at hrad
        by_contra hn
        have hbefore := hpre n hU.le V.property hUR (hfU n) (hX n V).choose (g n t)
          (hdom ⟨hgt, hgtU⟩) u le_rfl v (not_lt.1 hn)
        rw [hrad] at hbefore
        exact (not_le_of_gt hYrY) hbefore
      refine ⟨w, hw0, hw, hwa, hlevel, hcharts, horder,
        fun t hTt hgtU hγV => by simpa only [hlog n] using hoptical t hTt hgtU hβ hγV, ?_, hME, hGE⟩
      intro hflux
      let W : C(Icc 0 (V : ℝ), ℝ) :=
        ⟨fun v => w (projIcc 0 (V : ℝ) V.property ((v : ℝ) / (1 + β))), by fun_prop⟩
      have hW0 (v : Icc 0 (V : ℝ)) : 0 ≤ W v := hw0 _
      have hW (v : Icc 0 (V : ℝ)) : W v = g n (max Tr ((v : ℝ) / (1 + β))) := by
        have hvdiv : (v : ℝ) / (1 + β) ∈ Icc 0 (V : ℝ) :=
          ⟨div_nonneg v.property.1 hα.le,
            (div_le_self v.property.1 (by linarith only [hβ])).trans v.property.2⟩
        simp only [W, ContinuousMap.coe_mk, projIcc_of_mem V.property hvdiv, hw]
      have hfc : ContinuousOn (logarithmicIncoming (1 - 1 / p.toReal) (ℓ n) (Bn n)) (Ioi 0) := by
        apply ContinuousOn.mul
        · exact continuousOn_const.mul (continuousOn_id.rpow_const (fun u hu => Or.inl hu.ne'))
        · exact (Bn n).continuous.comp_continuousOn
            (continuousOn_const.sub (continuousOn_id.log (fun u hu => hu.ne')))
      have hderiv (t : ℝ) (ht : t ∈ Ici Tr) : DifferentiableAt ℝ (g n) t ∧ deriv (g n) t < 0 := by
        have hh := (mul_pos hηr (hgp n t ht).1).trans_le
          ((le_div_iff₀ (hgp n t ht).1).1 (hgp n t ht).2.2.2.1)
        exact ⟨(hgp n t ht).2.2.1, neg_pos.1 hh⟩
      obtain ⟨ar, _harc, _harl, har, _harleft⟩ := exists_arrival_inverse_closed
        (hgc n) (hga n) (hgl n) (fun t ht => (hgp n t ht).1) hderiv
      let entry : Icc 0 U → Icc 0 (V : ℝ) := fun u => projIcc 0 (V : ℝ) V.property (ar u)
      have hentered (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 (V : ℝ))
          (hTv : Tr < (v : ℝ) / (1 + β)) (hgu : g n ((v : ℝ) / (1 + β)) ≤ u) :
          Tr < ar u ∧ g n (ar u) = u ∧ (1 + β) * ar u ≤ v ∧ arrival n u < ar u := by
        have huT := u.property.2.trans_lt (hUUr.trans_lt (hgstart n))
        have ht := har u ⟨hu, huT⟩
        have htime : ar u ≤ (v : ℝ) / (1 + β) := by
          by_contra hn
          have hh := (hga n) hTv.le ht.1.le (not_le.1 hn)
          rw [ht.2.1] at hh
          exact (not_lt_of_ge hgu) hh
        have hγ : (1 + β) * ar u ≤ v := by
          simpa only [mul_comm] using (le_div_iff₀ hα).1 htime
        have htγ : ar u ≤ (1 + β) * ar u := by
          nlinarith only [mul_nonneg hβ.le (hTr.le.trans ht.1.le)]
        refine ⟨ht.1, ht.2.1, hγ, ?_⟩
        have hh := horder (ar u) ht.1.le (by rw [ht.2.1]; exact u.property.2)
          (htγ.trans (hγ.trans v.property.2))
        simpa only [ht.2.1] using hh
      have hEntry (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 (V : ℝ))
          (hTv : Tr < (v : ℝ) / (1 + β)) (hgu : g n ((v : ℝ) / (1 + β)) ≤ u) :
          entry u ≤ v ∧ (X n V).2.1 u (entry u) 0 < 0 ∧
            -(X n V).2.1 u (entry u) 0 / Real.exp ((X n V).1 u (entry u) 2) ≤ Drhi * (u : ℝ) := by
        obtain ⟨ht, hgt, hγ, _hold⟩ := hentered u hu v hTv hgu
        have htγ : ar u ≤ (1 + β) * ar u := by
          nlinarith only [mul_nonneg hβ.le (hTr.le.trans ht.le)]
        have htV : ar u ∈ Icc 0 (V : ℝ) := ⟨hTr.le.trans ht.le, htγ.trans (hγ.trans v.property.2)⟩
        have hm := hoptical (ar u) ht.le (by rw [hgt]; exact u.property.2) hβ (hγ.trans v.property.2)
        dsimp only at hm
        rw [hgt, projIcc_of_mem hU.le u.property] at hm
        have hDpos : 0 < -(X n V).2.1 u (entry u) 0 / Real.exp ((X n V).1 u (entry u) 2) :=
          (mul_pos hDrlo hu).trans_le hm.1
        have hneg : (X n V).2.1 u (entry u) 0 < 0 := neg_pos.1
          ((div_pos_iff.mp hDpos).resolve_right (by intro hn; exact (Real.exp_pos _).not_gt hn.2)).1
        exact ⟨by dsimp only [entry]; rw [projIcc_of_mem V.property htV]; exact htγ.trans hγ,
          hneg, hm.2.1⟩
      have hOld (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 (V : ℝ))
          (hTv : Tr < (v : ℝ) / (1 + β)) (hgu : g n ((v : ℝ) / (1 + β)) ≤ u) :
          (1 + β) * arrival n u ≤ v := by
        have hh := hentered u hu v hTv hgu
        exact (mul_le_mul_of_nonneg_left hh.2.2.2.le hα.le).trans hh.2.2.1
      have hoptflux (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 (V : ℝ))
          (hTv : Tr < (v : ℝ) / (1 + β)) (hgu : g n ((v : ℝ) / (1 + β)) ≤ u) :
          (∫ t in (entry u : ℝ)..v, intervalExtension V.property ((X n V).1 u) t 0 *
            (intervalExtension V.property ((X n V).2.1 u) t 1) ^ 2 /
              (-intervalExtension V.property ((X n V).2.1 u) t 0)) ≤ 1 / 4 := by
        obtain ⟨ht, hgt, hγ, _hold⟩ := hentered u hu v hTv hgu
        have htγ : ar u ≤ (1 + β) * ar u := by
          nlinarith only [mul_nonneg hβ.le (hTr.le.trans ht.le)]
        have htV : ar u ∈ Icc 0 (V : ℝ) := ⟨hTr.le.trans ht.le, htγ.trans (hγ.trans v.property.2)⟩
        have hh := hflux (ar u) ht.le (by rw [hgt]; exact u.property.2) v hγ
        simpa only [hgt, projIcc_of_mem hU.le u.property, entry, projIcc_of_mem V.property htV] using hh
      have hI0 : 0 ≤ ∫ t, Bn n t ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
      have hEg : 0 ≤ 2 * (F₀ + F₁ * ∫ t, Bn n t ^ 2) +
          2 * Ggamma ^ 2 * (E₀ + E₁ * ∫ t, Bn n t ^ 2) := by positivity
      have hh := hxLog.full_radiation_energy_of_optical_flux
        (Cd := Drhi) (Co := CoRad) (Jmax := 1 / 4) (N := 2 * N) (ρ := 3 * B.inner / 4)
        hU V.property hUR hc (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
        (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
        (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
        hrd hp hfLogU hfc B.outerRate_pos B.innerRate_pos hβ.le hβ8 hjr hCr hDrhi.le hCoRad
        (by positivity) hρ hTr.le hEg (g n) (hgc n) (hga n) (hUUr.trans_lt (hgstart n))
        (fun t ht => (hgp n t ht).1) (fun t ht => (hgp n t ht).2.2.2.2.1)
        hcharts W hW0 hW (hX n V).choose_spec.1 entry hEntry
        (fun u hu v hTv hgu => by simpa only [CoRad, neg_mul] using
          (hcornerAll n V u hu v (hOld u hu v hTv hgu)).2.2.2.2.2.2.2.2)
        hoptflux (fun u hu v hTv hgu => by
          simpa only [ν, dL, hlog n] using hnuPower n V u hu v (hOld u hu v hTv hgu))
        (hsmallRad U hU.le hUWr) hME hGE
      refine ⟨hh.1.trans_eq (by dsimp only [Er₀, Er₁, Brad, crad, Lrad, Ggamma]; ring), ?_⟩
      have hEeB : E₀ + E₁ * ∫ t, Bn n t ^ 2 ≤ EeBudget :=
        add_le_add_right (mul_le_mul_of_nonneg_left (hBnBudget n) hE₁) E₀
      have hEgB : 2 * (F₀ + F₁ * ∫ t, Bn n t ^ 2) +
          2 * Ggamma ^ 2 * (E₀ + E₁ * ∫ t, Bn n t ^ 2) ≤ EgBudget :=
        add_le_add (mul_le_mul_of_nonneg_left
          (add_le_add_right (mul_le_mul_of_nonneg_left (hBnBudget n) hF₁) F₀) (by norm_num))
          (mul_le_mul_of_nonneg_left hEeB (by positivity))
      exact (hh.2 ξrad hξradk le_rfl (by change ξrad ≤ 3 * ξrad; linarith only [hξrad])).trans
        (add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hEgB hα.le) (by positivity))
          (mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left hEeB (by norm_num))
            (mul_le_mul_of_nonneg_left hEgB hBrad)) (by positivity)))
    have hrestart (n : ℕ) (V : Ici (0 : ℝ)) (t : ℝ) (ht : Tr ≤ t) (hgt : g n t ≤ U)
        (a' b' : Icc 0 (V : ℝ)) (hta : t ≤ a') (hab : a' ≤ b') (hbg : (b' : ℝ) ≤ (1 + β) * t) :
        let u := projIcc 0 U hU.le (g n t)
        B.inner / 2 ≤ (X n V).1 u b' 0 ∧
        |ν n V u b'| ≤ (2 * Real.exp 2) * (-ν n V u a') * Real.exp (-2 * B.innerRate * ((b' : ℝ) - a')) ∧
        |(X n V).2.1 u b' 0| ≤ (Real.exp (2 + 1 / 16) * (-(X n V).2.1 u a' 0)) *
          Real.exp (-2 * B.innerRate * ((b' : ℝ) - a')) := by
      -- The full early interval may extend beyond the observed prefix.
      let S : Ici (0 : ℝ) := ⟨max (V : ℝ) ((1 + β) * t), by
        change 0 ≤ max (V : ℝ) ((1 + β) * t)
        exact V.property.trans (le_max_left _ _)⟩
      have hVS : V ≤ S := by
        change (V : ℝ) ≤ max (V : ℝ) ((1 + β) * t)
        exact le_max_left _ _
      have hγS : (1 + β) * t ≤ S := by
        change (1 + β) * t ≤ max (V : ℝ) ((1 + β) * t)
        exact le_max_right _ _
      obtain ⟨_, _, _, _, _, _, _, hoptical, _⟩ := hradData n S
      have hh := (hoptical t ht hgt hγS).2.2.2 (hX n S).choose.choose
        ⟨a', a'.property.1, a'.property.2.trans hVS⟩ ⟨b', b'.property.1, b'.property.2.trans hVS⟩ hta hab hbg
      change B.inner / 2 ≤ (X n S).1 _ _ 0 ∧
        |ν n S _ _| ≤ (2 * Real.exp 2) * (-ν n S _ _) * Real.exp (-2 * B.innerRate * ((b' : ℝ) - a')) ∧
        |(X n S).2.1 _ _ 0| ≤ (Real.exp (2 + 1 / 16) * (-(X n S).2.1 _ _ 0)) *
          Real.exp (-2 * B.innerRate * ((b' : ℝ) - a')) at hh
      simpa only [← hfieldCompat n V S hVS, ← hνcompat n V S hVS, ← hvel n V S hVS] using hh
    have hauxCharts (Y' : Ioo B.inner Yr) (n : ℕ) (V : Ici (0 : ℝ)) :
        AuxiliaryRadiationCharts B hU.le (X n V) (ν n V) (g n) Tr β Y' Laux (Saux Y') := by
      have hgp' (t : ℝ) (ht : t ∈ Ici Tr) : 0 < g n t ∧ DifferentiableAt ℝ (g n) t ∧
          deriv (g n) t < 0 ∧ g n t * Real.exp (B.outerRate * t) ≤ Dr := by
        have hh := hgp n t ht
        have hn := (mul_pos hηr hh.1).trans_le ((le_div_iff₀ hh.1).1 hh.2.2.2.1)
        exact ⟨hh.1, hh.2.2.1, neg_pos.1 hn, hh.2.1⟩
      have hlevel (T : Ici (0 : ℝ)) (t : ℝ) (ht : Tr ≤ t) (hgt : g n t ≤ U) (htT : t ≤ T) :
          (X n T).1 (projIcc 0 U hU.le (g n t)) (projIcc 0 (T : ℝ) T.property t) 0 = Yr := by
        obtain ⟨_, _, _, _, hlevel, _⟩ := hradData n T
        have hmem : t ∈ Icc 0 (T : ℝ) := ⟨hTr.le.trans ht, htT⟩
        simpa only [projIcc_of_mem T.property hmem] using hlevel ⟨t, hmem⟩ ht hgt
      have hh := hchartSolve Y' p hp (f n)
        ((hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hδqδ) le_rfl))
        ((scalar_prefix_norm_le hδqδ (hf n)).trans (hfn n)) hUR (hfU n) (X n)
        (fun T => (hX n T).choose) (g n) (hgc n) (hga n) (hgl n) (hUUr.trans_lt (hgstart n)) hgp' hlevel
      intro b hb
      obtain ⟨hw, z, hz, hzw, hrow⟩ := hh V b hb
      refine ⟨hw, z, hz, hzw, ?_⟩
      intro u hzu huw
      obtain ⟨Q, hQz, hQd, hQp⟩ := hrow u hzu huw
      refine ⟨Q, hQz, hQd, ?_⟩
      intro t ht
      obtain ⟨hr, hn, hnl, hnh, hl, hL, a, ha, hba, hga, haτ, hτb, hτγ⟩ := hQp t ht
      refine ⟨hr, hn, hnl, hnh, hl, hL.trans (mul_le_mul_of_nonneg_right
        (le_max_right La Lq) (sub_pos.2 Y'.property.1).le), ⟨a, ha, hba, hga, haτ, hτb, hτγ⟩, ?_⟩
      intro a' b' hτa hab hbb
      have htu : t ∈ Icc 0 U := ⟨hz.le.trans ht.1, ht.2.trans u.property.2⟩
      have hbg : (b' : ℝ) ≤ (1 + β) * a := (show (b' : ℝ) ≤ b from hbb).trans
        (by simpa only [mul_comm] using (div_le_iff₀ hα).1 hba)
      simpa only [hga] using hrestart n V a ha.le (hga.trans_le htu.2) a' b'
        (haτ.le.trans hτa) hab hbg
    suffices hrest : _ by
      refine ⟨g, fun n => ⟨hgc n, hga n, hgl n, hdc n, hUUr.trans_lt (hgstart n), hgp n⟩,
        fun Y' n V _hr => hauxCharts Y' n V, ?_, hrest⟩
      intro m Q hP₀ hPQ hQi hQlim hfront hsupport hflim
      suffices hmatching : _ by
        refine ⟨hmatching, ?_⟩
        let cν := Real.exp (∫ t in Ioi 0,
          2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
        let Ch := r 0 / (B.event * cν ^ B.criticalExponent)
        let Ptime := fun n t => Bn n (B.outerRate * t + ℓ n)
        have hprofile (n : ℕ) := timeChange_l2_halfline (l := 0) B.outerRate_pos
          (show ContinuousOn (fun t => B.outerRate * t + ℓ n) (Ici 0) by fun_prop)
          (fun t _ => show HasDerivAt (fun t => B.outerRate * t + ℓ n) B.outerRate t from by
            simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul B.outerRate).add_const (ℓ n))
          (fun _ _ => le_rfl) (Bn n).continuous (hBn n)
        suffices hgamma : RadiationGammaTransmissionTail B hU.le X g Ptime β (B.transmission hm * Ch) by
          refine ⟨hgamma, ?_⟩
          intro ε hε hεU
          have hzero : f 0 = 0 := by
            rw [hlog 0, hP₀]
            funext u
            simp only [logarithmicIncoming, BoundedContinuousFunction.coe_zero, Pi.zero_apply, mul_zero]
          have hvanish : ∀ S : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) S, Ptime n t = 0 := by
            intro S
            filter_upwards [(tendsto_atTop.1 hfront) (B.outerRate * S)] with n hn
            intro t ht
            apply hsupport n
            have hh := mul_le_mul_of_nonneg_left ht.2 B.outerRate_pos.le
            linarith only [hn, hh]
          have hcomp := radiation_comparison B hU.le hε hβ.le hξrad X g Ptime hcompat
            (fun n => (hrest.2.1 n).2.1)
            (fun n => ⟨(Bn n).continuous.comp (by fun_prop), (hprofile n).1⟩)
            (fun n t ht => (hgp n t ht).2.1) (fun n => hrest.2.2.1 n) hgamma (hfinite hzero hflim) hvanish
          refine ⟨hcomp, (fun n V => (hX n V).choose.choose), ?_⟩
          obtain ⟨_, _, _, _, _, _, _, Zν, _, _, hNlimit, _, hNsign, _, hcoef⟩ := hradial ε hε hεU
          have hdensity := radiation_mass_density hε.le X ν Ptime hcompat hνcompat (hcoef hzero hflim)
            (fun n => (hrest.2.1 n).2.1)
            (fun n => (hrest.2.1 n).2.2.trans
              (add_le_add_right (mul_le_mul_of_nonneg_left (hBnBudget n) hEr₁) Er₀))
            (fun n => (hprofile n).1)
            (fun n => (hprofile n).2.trans (div_le_div_of_nonneg_right (hBnBudget n) B.outerRate_pos.le))
            hcomp.2 hvanish
          refine ⟨hdensity, ?_⟩
          have hNfinite (V : Ici (0 : ℝ)) : Tendsto (fun n => ν n V) atTop (𝓝 (ν 0 V)) :=
            (IsWaveIntegral.radial_tendsto (fun n => (hX n V).choose) (hX 0 V).choose
              (fun n => (hX n V).choose.choose) (hX 0 V).choose.choose (hfinite hzero hflim V).fst_nhds).1
          obtain ⟨hmflux, hmfinite⟩ := mass_rows (k := B.innerRate) hε.le X ν
            (fun n V => (hX n V).choose.choose) hcompat hνcompat
            (fun n V u v => (hX n V).choose.outgoing_mass_integral hU.le V.property hUR hc
              (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
              (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
              (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
              hrd hp (hfU n) u v) (hfinite hzero hflim) hNfinite
          have hresponse : RadiationMassResponse hε.le B.innerRate (B.transmission hm * Ch)
              B.charge B.cosmological X ν (fun n V => (hX n V).choose.choose) Ptime :=
            mass_cumulative_limit hdensity hmflux hmfinite
          refine ⟨hresponse, ?_⟩
          obtain ⟨_, _, Z, hZ, _, hR, _⟩ := hboundary ε hε hεU
          have hCh : 0 < Ch := div_pos (hU.le.trans_lt hUR)
            (mul_pos B.event_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _))
          exact radiation_mass_profile hε.le B.outerRate_pos
            (mul_pos (B.transmission_pos hm) hCh).ne' X ν
            (fun n V => (hX n V).choose.choose) ℓ m (fun n => Bn n) (Z 0) (Zν 0)
            hresponse (hZ 0) (hNlimit 0) (fun u => hρ.trans_le (hR 0 u))
            (hstrict hzero ε hε hεU (Zν 0) (hNlimit 0))
            hBn hfront hsupport
        apply radiation_gamma_transmission_tail B hm hU.le hYr.1 hβ.le X g Ptime
          (fun n => ⟨(hrest.2.1 n).1, (hrest.2.1 n).2.1⟩) hgc (fun n => (hprofile n).1)
          (fun n => (hprofile n).2.trans (div_le_div_of_nonneg_right (hBnBudget n) B.outerRate_pos.le))
        intro Y'
        let lY := Tmatch Y'
        have hlY : 0 ≤ lY := (hτmatch Y' ⟨U, hU⟩).le
        obtain ⟨gY, θ, ζ, hreg, htrace, hsource, hlimit, htail⟩ := hmatching Y' lY le_rfl
        refine ⟨lY, Saux Y', gY, θ, hlY, (fun n => (hreg n).2.2.2.1), ?_, ?_, ?_, ?_, htail⟩
        · intro n t ht
          let V : Ici (0 : ℝ) := ⟨t, hlY.trans ht⟩
          have htV : t ∈ Icc 0 (V : ℝ) := ⟨hlY.trans ht, le_rfl⟩
          have hh := htrace n t ht V htV
          rw [radiationRow_eq (X n) (hcompat n) V (t := t) le_rfl]
          simp only [spatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
            projIcc_of_mem V.property htV, zero_mul, sub_zero, hh.2.1]
          exact hh.2.2.1
        · intro n t hstart hS
          have ht : 0 ≤ t := (hSaux Y').le.trans hS
          have hlt : lY ≤ t := ((le_max_left _ _).trans hstart).trans
            (div_le_self ht (by linarith only [hβ]))
          let V : Ici (0 : ℝ) := ⟨t, ht⟩
          let lV : Icc 0 (V : ℝ) := ⟨lY, hlY, hlt⟩
          let tV : Icc 0 (V : ℝ) := ⟨t, ht, le_rfl⟩
          obtain ⟨z, w, hzw, _⟩ := (hsource n).2.2.2.1 V lV le_rfl tV hstart hS
          obtain ⟨hz, hw, horder⟩ := hzw tV le_rfl
          simpa only [hz, hw] using horder
        · intro n
          simpa only [Ptime, Ch, cν, add_zero] using ((hlimit 0).1 n).1
        · apply squeeze_zero (fun n => integral_nonneg (fun t => sq_nonneg _)) _ (hlimit 0).2
          intro n
          have hiθ := (memLp_two_iff_integrable_sq ((hlimit 0).1 n).1.1).1 ((hlimit 0).1 n).1
          have hiζ := (memLp_two_iff_integrable_sq ((hlimit 0).1 n).2.1).1 ((hlimit 0).1 n).2
          simpa only [Ptime, Ch, cν, add_zero, Pi.add_apply] using integral_mono hiθ (hiθ.add hiζ)
            (fun t => le_add_of_nonneg_right (sq_nonneg _))
      intro Y' lY hlY
      have heq (n : ℕ) : f n = logarithmicIncoming B.criticalExponent (ℓ n) (Bn n) := by
        rw [hbeq]
        exact hlog n
      have hfM (n : ℕ) : MemLp (logarithmicIncoming B.criticalExponent (ℓ n) (Bn n)) p
          (volume.restrict (Icc 0 δm)) := by
        simpa only [← heq n] using (hf n).mono_measure
          (Measure.restrict_mono (Icc_subset_Icc le_rfl hδmδ) le_rfl)
      have hfMU (n : ℕ) : MemLp (logarithmicIncoming B.criticalExponent (ℓ n) (Bn n)) p
          (volume.restrict (Icc 0 U)) := by simpa only [← heq n] using hfU n
      have hflimM : Tendsto (fun n => (eLpNorm (logarithmicIncoming B.criticalExponent (ℓ n) (Bn n)) p
          (volume.restrict (Icc 0 δm))).toReal) atTop (𝓝 0) := by
        simpa only [← heq] using squeeze_zero (fun n => ENNReal.toReal_nonneg)
          (fun n => scalar_prefix_norm_le hδmδ (hf n)) hflim
      obtain ⟨gY, θ, ζ, hreg, htrace, hsource, hlimit⟩ := hmatchSolve Y' p hp ℓ m Bn Q
        (by rw [mul_comm, ← hcrit]) hP₀ hBn hBnBudget hPQ hQi hQlim hfront hsupport hfM
        (fun n => by simpa only [← heq n] using (scalar_prefix_norm_le hδmδ (hf n)).trans (hfn n))
        hflimM U hU hUR (hUU.trans _hU1) hUδm hfMU X
        (fun n V => by simpa only [heq n] using (hX n V).choose)
        (3 * B.inner / 4) hρ (fun n V => (hX n V).choose_spec.1) lY hlY
      suffices hsourceFull : _ by
        refine ⟨gY, θ, ζ, hreg, ?_, hsourceFull, hlimit, ?_⟩
        · intro n t ht V htV
          have hh := htrace n t ht V htV
          refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
          intro hr
          simpa only [← heq n] using hh.2.2.2
        · let cν := Real.exp (∫ t in Ioi 0,
            2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
          let Ch := r 0 / (B.event * cν ^ B.criticalExponent)
          let cζ := extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - Y') * Ch
          let H := fun n t => cζ * Bn n (B.outerRate * t + ℓ n)
          have hprofile (n : ℕ) := timeChange_l2_halfline (l := lY) B.outerRate_pos
            (show ContinuousOn (fun t => B.outerRate * t + ℓ n) (Ici lY) by fun_prop)
            (fun t _ => show HasDerivAt (fun t => B.outerRate * t + ℓ n) B.outerRate t from by
              simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul B.outerRate).add_const (ℓ n))
            (fun _ _ => le_rfl) (Bn n).continuous (hBn n)
          have hH (n : ℕ) : MemLp (H n) 2 (volume.restrict (Ici lY)) := (hprofile n).1.const_mul cζ
          have hHE (n : ℕ) : (∫ t in Ici lY, H n t ^ 2) ≤ cζ ^ 2 * (Ebudget / B.outerRate) := by
            simp only [H, mul_pow, integral_const_mul]
            exact mul_le_mul_of_nonneg_left ((hprofile n).2.trans
              (div_le_div_of_nonneg_right (hBnBudget n) B.outerRate_pos.le)) (sq_nonneg cζ)
          have hlim : Tendsto (fun n => ∫ t in Ici lY, (ζ n t - ζ 0 t - H n t) ^ 2)
              atTop (𝓝 0) := by
            apply squeeze_zero (fun n => integral_nonneg (fun t => sq_nonneg _)) _ (hlimit 0).2
            intro n
            have hiθ := (memLp_two_iff_integrable_sq ((hlimit 0).1 n).1.1).1 ((hlimit 0).1 n).1
            have hiζ := (memLp_two_iff_integrable_sq ((hlimit 0).1 n).2.1).1 ((hlimit 0).1 n).2
            simpa only [H, cζ, Ch, cν, add_zero, Pi.add_apply] using integral_mono hiζ (hiθ.add hiζ)
              (fun t => le_add_of_nonneg_left (sq_nonneg _))
          exact auxiliary_radiation_tail B hU.le ((hτmatch Y' ⟨U, hU⟩).le.trans hlY)
            X gY g ζ H (fun n => (hreg n).2.2.2.2) hH hHE hlim
            (fun n => (hrest.2.1 n).2.1)
            (fun n => (hrest.2.1 n).2.2.trans
              (add_le_add_right (mul_le_mul_of_nonneg_left (hBnBudget n) hEr₁) Er₀))
            (fun n l' b₀ hll' hstart hS => (hsourceFull n).2.2.2.2 l' b₀ hll' hstart hS)
      intro n
      have hFE (V : Ici (0 : ℝ)) (l' : Icc 0 (V : ℝ)) (hll' : lY ≤ l')
          (b₀ : Icc 0 (V : ℝ)) (hstart : max (l' : ℝ) Tr ≤ (b₀ : ℝ) / (1 + β)) (hS : Saux Y' ≤ b₀) :=
        (hsource n).2.2.2 V l' hll' Tr β Laux (Saux Y') (g n) hβ.le hLaux.le (hgc n)
          (by simpa only [ν, heq n] using hauxCharts Y' n V) b₀ hstart hS
      refine ⟨(hsource n).1, (hsource n).2.1, ?_, hFE, ?_⟩
      · intro V hr
        simpa only [← heq n] using (hsource n).2.2.1 V
      · intro l' b₀ hll' hstart hS
        have hl0 : 0 ≤ l' := ((hτmatch Y' ⟨U, hU⟩).le.trans hlY).trans hll'
        have hb0 : 0 ≤ b₀ := (hSaux Y').le.trans hS
        have hlb : l' ≤ b₀ := ((le_max_left _ _).trans hstart).trans
          (div_le_self hb0 (by linarith only [hβ]))
        apply auxiliary_radiation_halfline B hU.le hβ.le hl0 hstart (X n) (hcompat n)
          (hrest.2.1 n).2.1 (gY n) (g n) _
          ((hreg n).1.mono (Ici_subset_Ici.2 hll')) (hgc n)
          ((hsource n).2.1.mono_measure (Measure.restrict_mono (Ici_subset_Ici.2 hll') le_rfl))
        intro V hV
        have hlV : l' ∈ Icc 0 (V : ℝ) := ⟨hl0, hlb.trans hV⟩
        apply hFE V (projIcc 0 (V : ℝ) V.property l')
          (by simpa only [projIcc_of_mem V.property hlV] using hll') _
          (by simpa only [projIcc_of_mem V.property hlV] using hstart) hS
    suffices hradFinite : _ by
      refine ⟨hradFinite, ?_, ?_, (fun n V => (hX n V).choose.choose), ?_⟩
      · intro n
        have hh := radiationRow_energy (k := B.innerRate) (X n) (hcompat n) hU.le (by
          intro V
          obtain ⟨_, _, _, _, _, _, _, _, _, hE, _⟩ := hradFinite n V
          exact hE)
        exact ⟨continuous_radiationRow (X n) (hcompat n), hh⟩
      · intro n
        apply late_radiation_halfline hU.le hξrad.le (X n) (hcompat n) (g n) (hgc n)
        intro V
        obtain ⟨w, _hw0, hw, _hwa, _hlevel, _hcharts, _horder, _hoptical, _hflux,
          _henergy, hweighted, _rest⟩ := hradFinite n V
        let W : C(Icc 0 (V : ℝ), ℝ) :=
          ⟨fun v => w (projIcc 0 (V : ℝ) V.property ((v : ℝ) / (1 + β))), by fun_prop⟩
        refine ⟨W, ?_, hweighted⟩
        intro v
        have hvdiv : (v : ℝ) / (1 + β) ∈ Icc 0 (V : ℝ) :=
          ⟨div_nonneg v.property.1 hα.le,
            (div_le_self v.property.1 (by linarith only [hβ])).trans v.property.2⟩
        simp only [W, ContinuousMap.coe_mk, projIcc_of_mem V.property hvdiv, hw]
      · let m (n : ℕ) (V : Ici (0 : ℝ)) :=
          massField B.charge B.cosmological (X n V).1 (X n V).2.1 (ν n V) (hX n V).choose.choose
        have hmcompat (n : ℕ) (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v :
            m n S u v = m n T u ⟨v, v.property.1, v.property.2.trans hST⟩ := by
          simp only [m, massField_apply, hfieldCompat n S T hST, hνcompat n S T hST, hvel n S T hST]
        have hmmono (n : ℕ) (V : Ici (0 : ℝ)) (u : Icc 0 U) : Monotone (m n V u) :=
          (hX n V).choose.mass_monotone hU.le V.property hUR hc
            (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
            (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
            (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
            hrd hp (hfU n) u
        intro n V u v
        change |m n V u v| ≤ Mbound
        apply abs_le.2
        constructor
        · have hi := hInitialMass hU.le (hUU.trans _hU1) hUR hp (hfU n)
            ((scalar_prefix_norm_le hUδ (hf n)).trans (hfn n)) (hX n ⟨0, by simp⟩).choose
            (hX n ⟨0, by simp⟩).choose_spec.1 u
          change |m n ⟨0, by simp⟩ u ⟨0, le_rfl, le_rfl⟩| ≤ Minit at hi
          have hlo := (abs_le.1 hi).1
          rw [hmcompat n ⟨0, by simp⟩ V V.property u ⟨0, le_rfl, le_rfl⟩] at hlo
          exact (neg_le_neg (le_max_left _ _)).trans (hlo.trans (hmmono n V u v.property.1))
        · by_cases hu0 : (u : ℝ) = 0
          · have hu : u = ⟨0, le_rfl, hU.le⟩ := Subtype.ext hu0
            have hm := (hX n V).choose.horizon_mass_trace hU.le V.property hUR hc
              (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
              (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
              (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
              hrd hp (hfU n) v
            change m n V ⟨0, le_rfl, hU.le⟩ v = horizonMass B.mass h v at hm
            rw [hu, hm]
            have hh := (horizonMass_bounds (B.innerRate_pos.trans hks) hH hb B.mass v).1
            exact (by linarith only [hh] : horizonMass B.mass h v ≤ B.mass).trans
              ((le_abs_self _).trans ((le_max_left _ _).trans (le_max_right _ _)))
          have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm hu0)
          obtain ⟨T, hT⟩ := eventually_atTop.1 ((hgl n).eventually_lt_const hu)
          obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' (le_max_right T Tr)
            ((hgc n).mono (fun _ hw => hw.1))
            (show (u : ℝ) ∈ Icc (g n (max T Tr)) (g n Tr) from
              ⟨(hT _ (le_max_left _ _)).le, u.property.2.trans (hUUr.trans_lt (hgstart n)).le⟩)
          have ht0 : 0 ≤ t := hTr.le.trans ht.1
          have htγ : t ≤ (1 + β) * t := by nlinarith only [mul_nonneg hβ.le ht0]
          let S : Ici (0 : ℝ) := ⟨max (V : ℝ) ((1 + β) * t), by
            change 0 ≤ max (V : ℝ) ((1 + β) * t)
            exact V.property.trans (le_max_left _ _)⟩
          have hVS : V ≤ S := by
            change (V : ℝ) ≤ max (V : ℝ) ((1 + β) * t)
            exact le_max_left _ _
          have hγS : (1 + β) * t ≤ S := by
            change (1 + β) * t ≤ max (V : ℝ) ((1 + β) * t)
            exact le_max_right _ _
          have htS : t ∈ Icc 0 (S : ℝ) := ⟨ht0, htγ.trans hγS⟩
          let a : Icc 0 (S : ℝ) := ⟨t, htS⟩
          let b : Icc 0 (S : ℝ) := ⟨S, S.property, le_rfl⟩
          have hgtU : g n t ≤ U := by rw [hgt]; exact u.property.2
          obtain ⟨_, _, _, _, _, _, horder, hmatching, hflux, _⟩ := hradFinite n S
          have hold : (1 + β) * arrival n u ≤ b := by
            have hh := horder t ht.1 hgtU htS.2
            rw [hgt] at hh
            exact (mul_le_mul_of_nonneg_left hh.le hα.le).trans hγS
          have hm := hmatching t ht.1 hgtU hγS
          have hJ := hflux t ht.1 hgtU b hγS
          simp only [hgt, projIcc_of_mem hU.le u.property, projIcc_of_mem S.property htS] at hm hJ
          have hDa : 0 < -(X n S).2.1 u a 0 / Real.exp ((X n S).1 u a 2) :=
            (mul_pos hDrlo hu).trans_le hm.1
          have hlam : (X n S).2.1 u a 0 < 0 :=
            neg_pos.1 ((div_pos_iff_of_pos_right (Real.exp_pos _)).1 hDa)
          obtain ⟨_, _, _, _, _, htransport⟩ := (hX n S).choose.trapped_q_transport
            hU.le S.property hUR hc (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
            (fun z => ((sub_pos.2 hdHR).trans_le (hrb z)).ne')
            (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
            hrd hp (hfU n) u a b htS.2 hlam
          let Db := -(X n S).2.1 u b 0 / Real.exp ((X n S).1 u b 2)
          have hDb : Db = (-(X n S).2.1 u a 0 / Real.exp ((X n S).1 u a 2)) *
              Real.exp (∫ z in t..(b : ℝ), intervalExtension S.property ((X n S).1 u) z 0 *
                (intervalExtension S.property ((X n S).2.1 u) z 1) ^ 2 /
                  (-intervalExtension S.property ((X n S).2.1 u) z 0)) := by
            dsimp only [Db]
            rw [htransport, Real.exp_add, Real.exp_sub]
            field_simp
            ring
          have hDb0 : 0 ≤ Db := by rw [hDb]; positivity
          have hDbhi : Db ≤ Drhi * (u : ℝ) * Real.exp (1 / 8) := by
            rw [hDb]
            exact mul_le_mul hm.2.1 (Real.exp_le_exp.2 hJ) (Real.exp_pos _).le (by positivity)
          have hν := (neg_le_abs (ν n S u b)).trans (hnuPower n S u hu b hold)
          have hp : (u : ℝ) ^ (dL - 1) * u = (u : ℝ) ^ dL := by
            calc
              _ = (u : ℝ) ^ ((dL - 1) + 1) := by rw [Real.rpow_add hu, Real.rpow_one]
              _ = _ := by rw [sub_add_cancel]
          have hprod : (-ν n S u b) * Db ≤ Qmass := calc
            _ ≤ (2 * N * (u : ℝ) ^ (dL - 1)) * (Drhi * u * Real.exp (1 / 8)) :=
              mul_le_mul hν hDbhi hDb0 (by positivity)
            _ = Qmass * (u : ℝ) ^ dL := by rw [← hp]; dsimp only [Qmass]; ring
            _ ≤ Qmass := mul_le_of_le_one_right hQmass
              (Real.rpow_le_one hu.le (u.property.2.trans (hUU.trans _hU1)) hdL.le)
          have hrhi : (X n S).1 u b 0 ≤ 3 * B.inner / 2 := by
            have hh := ((hX n S).choose_spec.2.1 u hu b hold).2.1
            linarith only [hh, hΔr, B.inner_pos]
          have hmLate : m n S u b ≤ Mlate := renormalizedMass_le_of_optical hρ
            ((hX n S).choose_spec.1 u b) hrhi B.cosmological_pos.le hQmass hprod
          have hmEarlier := hmmono n S u (show (⟨v, v.property.1, v.property.2.trans hVS⟩ : Icc 0 (S : ℝ)) ≤ b from
            v.property.2.trans hVS)
          rw [← hmcompat n V S hVS u v] at hmEarlier
          exact hmEarlier.trans (hmLate.trans ((le_max_right _ _).trans (le_max_right _ _)))
    intro n V
    obtain ⟨w, hw0, hw, hwa, hlevel, hcharts, horder, hoptical, hconditional, hME, hGE⟩ := hradData n V
    let Dval (S : Ici (0 : ℝ)) (t v : ℝ) :=
      -(X n S).2.1 (projIcc 0 U hU.le (g n t)) (projIcc 0 (S : ℝ) S.property v) 0 /
        Real.exp ((X n S).1 (projIcc 0 U hU.le (g n t)) (projIcc 0 (S : ℝ) S.property v) 2)
    let Jval (S : Ici (0 : ℝ)) (t v : ℝ) :=
      ∫ z in t..v, intervalExtension S.property ((X n S).1 (projIcc 0 U hU.le (g n t))) z 0 *
        (intervalExtension S.property ((X n S).2.1 (projIcc 0 U hU.le (g n t))) z 1) ^ 2 /
          (-intervalExtension S.property ((X n S).2.1 (projIcc 0 U hU.le (g n t))) z 0)
    have htγ (t : ℝ) (ht : Tr ≤ t) : t ≤ (1 + β) * t := by
      nlinarith only [mul_nonneg hβ.le (hTr.le.trans ht)]
    have htransport (S : Ici (0 : ℝ)) (t : ℝ) (ht : Tr ≤ t) (hgt : g n t ≤ U)
        (v : Icc 0 (S : ℝ)) (hγv : (1 + β) * t ≤ v) :
        0 < Dval S t t ∧ Dval S t v = Dval S t t * Real.exp (Jval S t v) := by
      obtain ⟨_, _, _, _, _, _, _, hm, _⟩ := hradData n S
      have hm' := (hm t ht hgt (hγv.trans v.property.2)).1
      have htS : t ∈ Icc 0 (S : ℝ) := ⟨hTr.le.trans ht, (htγ t ht).trans (hγv.trans v.property.2)⟩
      have hD0 : 0 < Dval S t t := (mul_pos hDrlo (hgp n t ht).1).trans_le hm'
      have hlam : (X n S).2.1 (projIcc 0 U hU.le (g n t)) (projIcc 0 (S : ℝ) S.property t) 0 < 0 :=
        neg_pos.1 ((div_pos_iff_of_pos_right (Real.exp_pos _)).1 hD0)
      have hab : projIcc 0 (S : ℝ) S.property t ≤ v := by
        rw [projIcc_of_mem S.property htS]; exact (htγ t ht).trans hγv
      obtain ⟨_, _, _, _, _, htrans⟩ := (hX n S).choose.trapped_q_transport
        hU.le S.property hUR hc (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
        (fun z => ((sub_pos.2 hdHR).trans_le (hrb z)).ne')
        (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
        hrd hp (hfU n) (projIcc 0 U hU.le (g n t)) (projIcc 0 (S : ℝ) S.property t) v hab hlam
      refine ⟨hD0, ?_⟩
      dsimp only [Dval, Jval]
      rw [projIcc_of_mem S.property v.property, htrans, Real.exp_add, Real.exp_sub]
      simp only [projIcc_of_mem S.property htS]
      field_simp
    have hDcompat (S : Ici (0 : ℝ)) (hSV : S ≤ V) (t v : ℝ) (hv : v ∈ Icc 0 (S : ℝ)) :
        Dval S t v = Dval V t v := by
      dsimp only [Dval]
      rw [projIcc_of_mem S.property hv, projIcc_of_mem V.property ⟨hv.1, hv.2.trans hSV⟩,
        hfieldCompat n S V hSV _ ⟨v, hv⟩, ← hvel n S V hSV _ ⟨v, hv⟩]
    have hJcompat (S : Ici (0 : ℝ)) (hSV : S ≤ V) (t : ℝ) (ht : Tr ≤ t) (hgt : g n t ≤ U)
        (v : Icc 0 (S : ℝ)) (hγv : (1 + β) * t ≤ v) : Jval S t v = Jval V t v := by
      have htS : t ∈ Icc 0 (S : ℝ) := ⟨hTr.le.trans ht, (htγ t ht).trans (hγv.trans v.property.2)⟩
      have hs := htransport S t ht hgt v hγv
      have hv := htransport V t ht hgt ⟨v, v.property.1, v.property.2.trans hSV⟩ hγv
      apply Real.exp_injective
      apply mul_left_cancel₀ hs.1.ne'
      calc
        _ = Dval S t v := hs.2.symm
        _ = Dval V t v := hDcompat S hSV t v v.property
        _ = Dval V t t * Real.exp (Jval V t v) := hv.2
        _ = _ := by rw [← hDcompat S hSV t t htS]
    have himprove (S : Ici (0 : ℝ))
        (hflux : ∀ t : ℝ, Tr ≤ t → g n t ≤ U → ∀ v : Icc 0 (S : ℝ),
          (1 + β) * t ≤ v → Jval S t v ≤ 1 / 4) :
        ∀ t : ℝ, Tr ≤ t → g n t ≤ U → ∀ v : Icc 0 (S : ℝ),
          (1 + β) * t ≤ v → Jval S t v ≤ 1 / 8 := by
      obtain ⟨_, _, _, _, _, _, horderS, hm, henergyS, _⟩ := hradData n S
      have hES := (henergyS hflux).1.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hBnBudget n) hEr₁))
      intro t ht hgt v hγv
      let u := projIcc 0 U hU.le (g n t)
      have huval : (u : ℝ) = g n t := by simp only [u, projIcc_of_mem hU.le ⟨(hgp n t ht).1.le, hgt⟩]
      have hu : 0 < (u : ℝ) := by rw [huval]; exact (hgp n t ht).1
      have htS : t ∈ Icc 0 (S : ℝ) := ⟨hTr.le.trans ht, (htγ t ht).trans (hγv.trans v.property.2)⟩
      have hγS : (1 + β) * t ∈ Icc 0 (S : ℝ) :=
        ⟨mul_nonneg hα.le htS.1, hγv.trans v.property.2⟩
      have hm' := hm t ht hgt hγS.2
      let Env := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 (S : ℝ)) U)
        (fun _ => hU.le) 0 B.innerRate 0 (X n S)
      have hEnv (z : Icc 0 (S : ℝ)) : Real.exp (B.innerRate * z) *
          |(X n S).1 u z 0 * (X n S).2.1 u z 1| ≤ Env z := by
        simpa only [zero_mul, sub_zero] using
          (movingSpatialRadiationEnvelope_le_iff (a := 0) (σ := 0) hU.le
            (ContinuousMap.const (Icc 0 (S : ℝ)) U) (fun _ => hU.le) (X n S) z).1 le_rfl u u.property.2
      have hopt := (hX n S).choose.optical_flux_of_radiation_energy
        (k := B.innerRate) (σ := 2 * B.innerRate / B.outerRate) hU.le S.property hUR hc
        (horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb) hrc
        (fun z => ((sub_pos.2 hdHR).trans_le (hrb z)).ne')
        (horizonPhi_integrable (B.innerRate_pos.trans hks) hH (sub_pos.2 hdHR) hc hrc hb hrb)
        hrd hp (hfU n) hDrlo hCoLow hρ u hu ⟨t, htS⟩ ⟨(1 + β) * t, hγS⟩ v
        (htγ t ht) hγv (by simpa only [u, huval, projIcc_of_mem S.property htS] using hm'.1)
        (fun z _ _ => (hX n S).choose_spec.1 u z) (by
          intro z hγz _hzv
          have hOld : (1 + β) * arrival n u ≤ z := by
            rw [huval]
            exact (mul_le_mul_of_nonneg_left (horderS t ht hgt htS.2).le hα.le).trans hγz
          simpa only [CoLow, neg_mul] using
            (hcornerAll n S u hu z hOld).2.2.2.2.2.2.2.1)
        Env (fun z _ _ => hEnv z) hES hm'.2.2.1
      have hlogsmall : Real.log (1 + Fflux (g n t)) ≤ 1 / 16 :=
        (Real.log_le_iff_le_exp (by dsimp only [Fflux]; positivity [(hgp n t ht).1])).2
          (by linarith only [hsmallFlux (g n t) (hgp n t ht).1.le hgt])
      have hJ : Jval S t v ≤ 1 / 16 + Real.log (1 + Fflux (g n t)) := by
        simpa only [Jval, u, Fflux, huval] using hopt.2
      linarith only [hJ, hlogsmall]
    let K := {t : Icc Tr ((V : ℝ) / (1 + β)) // g n t ≤ U}
    have hgcI : Continuous (fun t : Icc Tr ((V : ℝ) / (1 + β)) => g n t) :=
      ((hgc n).mono (fun _ ht => ht.1)).domRestrict
    have : CompactSpace K := isCompact_iff_compactSpace.1 (isClosed_le hgcI continuous_const).isCompact
    let time : K → ℝ := fun t => t.1
    have htime : Continuous time := continuous_subtype_val.comp continuous_subtype_val
    have hgK : Continuous (fun t : K => g n (time t)) := hgcI.comp continuous_subtype_val
    let F : ℝ × K → ℝ := fun z => Dval V (time z.2) z.1 - Real.exp (1 / 4) * Dval V (time z.2) (time z.2)
    have hDc : Continuous (fun z : ℝ × K => Dval V (time z.2) z.1) := by
      have hpt : Continuous (fun z : ℝ × K =>
          (projIcc 0 U hU.le (g n (time z.2)), projIcc 0 (V : ℝ) V.property z.1)) :=
        (((continuous_projIcc (h := hU.le)).comp hgK).comp continuous_snd).prodMk
          ((continuous_projIcc (h := V.property)).comp continuous_fst)
      exact (((continuous_apply (0 : Fin 3)).comp (X n V).2.1.uncurry.continuous).comp hpt).neg.div
        (Real.continuous_exp.comp (((continuous_apply (2 : Fin 3)).comp (X n V).1.uncurry.continuous).comp hpt))
        (fun _ => Real.exp_ne_zero _)
    have hFc : Continuous F := hDc.sub
      (((hDc.comp (htime.prodMk continuous_id)).comp continuous_snd).const_mul _)
    have hgamma0 (q : K) : 0 ≤ (1 + β) * time q := mul_nonneg hα.le (hTr.le.trans q.1.property.1)
    have hbarrier (q : K) (v : Icc 0 (V : ℝ)) (hγv : (1 + β) * time q ≤ v) :
        F (v, q) ≤ 0 ↔ Jval V (time q) v ≤ 1 / 4 := by
      have hh := htransport V (time q) q.1.property.1 q.property v hγv
      dsimp only [F]
      rw [hh.2, mul_comm (Real.exp (1 / 4)), sub_nonpos, mul_le_mul_iff_right₀ hh.1, Real.exp_le_exp]
    have hstrict (q : K) (v : Icc 0 (V : ℝ)) (hγv : (1 + β) * time q ≤ v)
        (hJ : Jval V (time q) v ≤ 1 / 8) : F (v, q) < 0 := by
      have hh := htransport V (time q) q.1.property.1 q.property v hγv
      have he := mul_lt_mul_of_pos_left
        (Real.exp_lt_exp.2 (hJ.trans_lt (by norm_num : (1 / 8 : ℝ) < 1 / 4))) hh.1
      dsimp only [F]
      rw [hh.2]
      nlinarith only [he]
    have hboot := continuous_entered_bootstrap hFc (htime.const_mul (1 + β)) hgamma0 (by
      intro q hqV
      let v : Icc 0 (V : ℝ) := ⟨(1 + β) * time q, hgamma0 q, hqV⟩
      apply hstrict q v le_rfl
      exact ((hoptical (time q) q.1.property.1 q.property hqV).2.2.1).trans (by norm_num)) (by
      intro z hz hpre q hqz
      let S : Ici (0 : ℝ) := ⟨z, hz.1⟩
      have hpref : ∀ t : ℝ, Tr ≤ t → g n t ≤ U → ∀ v : Icc 0 (S : ℝ),
          (1 + β) * t ≤ v → Jval S t v ≤ 1 / 4 := by
        intro t ht hgt v hγv
        have htV : t ≤ (V : ℝ) / (1 + β) :=
          (le_div_iff₀ hα).2 (by simpa only [mul_comm] using hγv.trans (v.property.2.trans hz.2))
        let q' : K := ⟨⟨t, ht, htV⟩, hgt⟩
        rw [hJcompat S hz.2 t ht hgt v hγv]
        exact (hbarrier q' ⟨v, v.property.1, v.property.2.trans hz.2⟩ hγv).1
          (hpre v ⟨v.property.1, v.property.2⟩ q' hγv)
      have hJ := himprove S hpref (time q) q.1.property.1 q.property ⟨z, hz.1, le_rfl⟩ hqz
      rw [hJcompat S hz.2 (time q) q.1.property.1 q.property ⟨z, hz.1, le_rfl⟩ hqz] at hJ
      exact hstrict q ⟨z, hz⟩ hqz hJ)
    have hflux : ∀ t : ℝ, Tr ≤ t → g n t ≤ U → ∀ v : Icc 0 (V : ℝ),
        (1 + β) * t ≤ v → Jval V t v ≤ 1 / 4 := by
      intro t ht hgt v hγv
      have htV : t ≤ (V : ℝ) / (1 + β) :=
        (le_div_iff₀ hα).2 (by simpa only [mul_comm] using hγv.trans v.property.2)
      let q : K := ⟨⟨t, ht, htV⟩, hgt⟩
      exact (hbarrier q v hγv).1 (hboot v v.property q hγv).le
    exact ⟨w, hw0, hw, hwa, hlevel, hcharts, horder, hoptical,
      himprove V hflux, (hconditional hflux).1, (hconditional hflux).2, hME, hGE⟩
  · intro n T q hq hqT
    have hh := ((hX n T).choose_spec.2.2.1 q hq hqT).2
    exact ⟨hh.1, hh.2.1⟩
  · intro n T
    have hscalar (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 (T : ℝ)) (huv : (1 + β) * arrival n u ≤ v) :
        |(X n T).2.1 u v 1| ≤ Hs * Real.exp (-cL * v) :=
      ((hclosed n T u hu v huv).1).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hHs]) (Real.exp_pos _).le)
    filter_upwards [(hX n T).choose_spec.2.2.2.2.1 cL Hs hcL hHs.le hscalar] with u hu
    intro v hu0 huv
    exact (hu v hu0 huv).2 dL hdL hdn hgap
  · intro n T u hu a b hua hab
    exact (hX n T).choose.longitudinal_tail_bound u 0 a b hab hLdec.le hηL
      (fun w hw => hlateLambda n T u hu w (hua.trans hw.1))

end CauchyHorizon.Background
