import CauchyHorizon
import Tests.PhaseEnergy
import Tests.Packets
import Tests.PacketMass
import Tests.OuterTransverseMatching
import Tests.OuterRadiusMatching
import Tests.OuterModeMatching
import Tests.BandToEvent
import Tests.RadiusTransport
import Tests.BandTransportDecay
import Tests.TransportEnergy
import Tests.ScalarSecond
import Tests.ScalarCoordinates
import Tests.BandEnergy
import Tests.BandGrowth
import Tests.SourceNorm
import Tests.BandPropagation
import Tests.MatchedBand
import Tests.BandOverlap
import Tests.MatchedHalfline
import Tests.ZeroReference
import Tests.BottomConvergence
import Tests.BottomLimit
import Tests.TransverseDifference
import Tests.NestedRadiusSections
import Tests.RadiationComparison
import Tests.GeneralRadialConstraint
import Tests.WeakWave
import Tests.CoordinateMetric
import Tests.CoordinateRicci
import Tests.CoordinateMaxwell
import Tests.ScalarDivergence
import Tests.SphericalGeometry
import Tests.SphericalChart
import Tests.ConnectionChange
import Tests.SphericalEinstein
import Tests.MetricTransition
import Tests.SphericalConnection
import Tests.SphericalMatter
import Tests.LocalWeakExtension
import Tests.NullRicciSources
import Tests.CompactifiedGeometry
import Tests.FirstCrossing
import Tests.PacketQuantiles
import Tests.FinitePackets
import Tests.PacketPair
import Tests.InitialGeometry
import Tests.LateData
import Tests.FirstOrder
import Tests.OpticalIdentities
import Tests.PacketBump
import Tests.PacketNorm
import Tests.ContinuousWave
import Tests.WeakExtensionGeometry
import Tests.CausalHorizon
import Tests.CharacteristicCausality
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter MeasureTheory Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace CauchyHorizon.Tests

example : 0 < 1 - 1 / (4 : ℝ) ∧ 1 - 1 / (4 : ℝ) < 1 ∧
    0 < 1 - 2 / (4 : ℝ) := critical_range (by norm_num)

example (initial rate origin : ℝ) :
    Tendsto (fun t => Real.exp (rate * (t - origin)) *
      Real.exp (logarithmicProfile initial rate origin (fun _ => 0) t))
      atTop (𝓝 (Real.exp initial)) := by
  simpa using exact_rate_of_integrable_error (origin := origin) (integrableOn_zero) initial rate

example {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : Lp ℝ 2 μ) :
    l2Square (f - f) = 0 := by
  change (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (f - f) (f - f) = 0
  simp

-- This instance checks the same mixed space L2(time; C(I)) used by the paper.
example {I : Type*} [TopologicalSpace I] [CompactSpace I]
    {f g : ℕ → Lp C(I, ℝ) 2 (volume : Measure ℝ)} {M : ℝ}
    (hbound : ∀ n, ‖f n‖ + ‖g n‖ ≤ M)
    (hclose : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ s : Set ℝ,
      ‖(∫ t in s, f n t ^ 2) - ∫ t in s, g n t ^ 2‖ < ε :=
  square_cumulative_convergence_uniform hbound hclose

-- Each endpoint is singular; neither coefficient is continuous on the closed interval.
example : ∃! p, IsVolterraPair (a := 0) (b := 1) (by norm_num)
    (fun t => (1 - t) ^ (-1 / 2 : ℝ)) (fun t => t ^ (-3 / 4 : ℝ)) 0 1 p := by
  apply exists_unique_volterraPair
  · simpa using (intervalIntegral.intervalIntegrable_rpow'
      (a := (1 : ℝ)) (b := (0 : ℝ)) (by norm_num : (-1 : ℝ) < -1 / 2)).comp_sub_left 1
  · exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  · exact (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (by change 1 - x ≠ 0; linarith [hx.2]))
  · exact continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')

example {p : C(Icc (0 : ℝ) 1, ℝ) × C(Icc (0 : ℝ) 1, ℝ)}
    (hp : IsVolterraPair (by norm_num) (fun _ => 1) (fun _ => 1) 0 1 p) :
    0 < p.1 ⟨1, by norm_num⟩ ∧ 0 < p.2 ⟨1, by norm_num⟩ := by
  have hp0 := volterraPair_nonneg (by norm_num) intervalIntegrable_const intervalIntegrable_const
    continuousOn_const continuousOn_const (by norm_num) (by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) hp
  exact volterraPair_strict_positive (by norm_num) intervalIntegrable_const (by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    hp hp0 _ (by norm_num)

-- A concrete charged de Sitter background satisfies the paper's critical range.
noncomputable def sampleBackground : Background where
  mass := 462 / 481
  charge := Real.sqrt (468 / 481)
  cosmological := 75 / 481
  inner := 1
  event := 6 / 5
  cosmologicalRadius := 3
  charge_ne := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 468 / 481)).ne'
  cosmological_pos := by norm_num
  inner_pos := by norm_num
  inner_lt_event := by norm_num
  event_lt_cosmological := by norm_num
  root_inner := by
    rw [horizonFunction, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 468 / 481)]
    norm_num
  root_event := by
    rw [horizonFunction, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 468 / 481)]
    norm_num
  root_cosmological := by
    rw [horizonFunction, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 468 / 481)]
    norm_num

example : sampleBackground.outerRate = 40 / 481 ∧ sampleBackground.innerRate = 31 / 481 := by
  norm_num [Background.outerRate, Background.innerRate, Background.negativeRoot, sampleBackground]

theorem sample_critical_exponent : sampleBackground.criticalExponent = 31 / 40 := by
  norm_num [Background.criticalExponent, Background.outerRate, Background.innerRate,
    Background.negativeRoot, sampleBackground]

example : sampleBackground.criticalExponent = 1 - 1 / (40 / 9 : ℝ) ∧ 4 ≤ (40 / 9 : ℝ) := by
  rw [sample_critical_exponent]
  norm_num

example : 0 < sampleBackground.transmission (by rw [sample_critical_exponent]; norm_num) :=
  sampleBackground.transmission_pos _

-- The norm bound is attained by a constant source, on the entire time axis.
example (t : ℝ) : terminalGreen (by norm_num : (0 : ℝ) < 2)
    (BoundedContinuousFunction.const ℝ 1) t = 1 / 2 := terminalGreen_const _ _ _

-- The actual endpoint p = 4, with no continuity assumption on f.
example {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 1))) :
    MemLp (fun u => -(2 - u) * f u ^ 2) 2 (volume.restrict (Icc (0 : ℝ) 1)) ∧
      (∀ᵐ u, u ∈ Icc (0 : ℝ) 1 →
        deriv (deriv (incomingRadius 2)) u - deriv (incomingLogOmega 2 f) u *
          deriv (incomingRadius 2) u =
            -incomingRadius 2 u * (deriv (incomingPhi 0 f) u) ^ 2) := by
  have hi := incoming_integrable_sources (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) < 2) (le_refl 4) hf
  exact ⟨(incoming_memLp_sources (by norm_num) (le_refl 4) hf).2,
    incoming_constraint (by norm_num) hi.1 hi.2⟩

-- Continuous radiative data have the exact quadratic mass flux without differentiating h.
example (t : ℝ) : HasDerivAt (horizonMass 1 (fun w => Real.exp (-w)))
    (Real.exp (-t) ^ 2 / 2) t := by
  apply horizonMass_hasDerivAt (by fun_prop)
  intro w
  apply horizon_mass_integrable (s := 1) (H := 1) (by norm_num) (by norm_num) (by fun_prop)
  intro v
  simp only [Real.norm_of_nonneg (Real.exp_pos _).le, neg_one_mul, one_mul, le_refl]

example : HasDerivWithinAt (terminalWeight 2) (-2) (Ici (0 : ℝ)) 0 := by
  simpa [terminalWeight] using terminalWeight_hasDerivWithinAt 2 (le_refl (0 : ℝ))

noncomputable def nonsmoothTail (v : ℝ) : ℝ := Real.exp (-v) * (1 + min |v - 1| 1)

-- The tail is continuous but has a corner at v = 1; the nonlinear radius still exists.
example : ∃ T : ℝ, 0 ≤ T ∧ ∃ r : ℝ → ℝ, Continuous r ∧ 0 < r 0 ∧
    (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass sampleBackground.mass (fun w => nonsmoothTail (w + T)) t)
        sampleBackground.charge sampleBackground.cosmological) (Ici 0) t) ∧
    Tendsto r atTop (nhds sampleBackground.event) := by
  have hc : ContinuousOn nonsmoothTail (Ici 0) := by unfold nonsmoothTail; fun_prop
  have hb (v : ℝ) (_hv : v ∈ Ici (0 : ℝ)) : ‖nonsmoothTail v‖ ≤ 2 * Real.exp (-(1 : ℝ) * v) := by
    have hmin : 0 ≤ min |v - 1| 1 := le_min (abs_nonneg _) (by norm_num)
    have hmax := min_le_right |v - 1| (1 : ℝ)
    unfold nonsmoothTail
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (by linarith : 0 ≤ 1 + min |v - 1| 1), neg_one_mul]
    nlinarith [Real.exp_pos (-v)]
  obtain ⟨T, δ, hT, _hδ, hδR, r, hrc, hrb, hrd, _hrdec, hrend⟩ :=
    sampleBackground.exists_late_tail_horizon (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 2) hc hb
  exact ⟨T, hT, r, hrc, (sub_pos.2 hδR).trans_le (hrb 0), hrd, hrend⟩

-- A constant coefficient checks the sign and normalization of the exact amplitude.
example (a : ℝ) : Tendsto (fun t => Real.exp (-a * t) * (-horizonNu (fun _ => a / 2) t))
    atTop (nhds 1) := by
  have he : (fun _ : ℝ => 2 * (a / 2) - a) = fun _ => 0 := by funext; ring
  have hi : IntegrableOn (fun _ : ℝ => 2 * (a / 2) - a) (Ioi 0) := by
    rw [he]
    exact integrable_zero _ _ _
  have hh := horizonNu_exact_amplitude (K := fun _ => a / 2) continuous_const hi
  simpa only [he, integral_zero, Real.exp_zero] using hh

-- The late construction gives positive radial flux for the original, unextended tail.
example : ∃ T : ℝ, 0 ≤ T ∧ ∃ r : ℝ → ℝ, Continuous r ∧
    (∀ t ∈ Ici (0 : ℝ), 0 < horizonFunction (r t)
      (horizonMass sampleBackground.mass (fun w => Real.exp (-(w + T))) t)
      sampleBackground.charge sampleBackground.cosmological) := by
  have hc : ContinuousOn (fun w : ℝ => Real.exp (-w)) (Ici 0) := by fun_prop
  have hb (w : ℝ) (_hw : w ∈ Ici (0 : ℝ)) :
      ‖Real.exp (-w)‖ ≤ 1 * Real.exp (-(1 : ℝ) * w) := by
    simp only [Real.norm_of_nonneg (Real.exp_pos _).le, neg_one_mul, one_mul, le_refl]
  obtain ⟨T, δ, hT, _hδ, _hδR, g, r, _hgc, hgeq, hrc, _hrb, _hrd, _hrdec, _hrend, hest⟩ :=
    sampleBackground.exists_late_outgoing_data (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 1) hc hb (fun w _ => Real.exp_pos _)
  refine ⟨T, hT, r, hrc, ?_⟩
  intro t ht
  have hm := horizonMass_congr_future hgeq ht sampleBackground.mass
  have hp := hest.2.2.2.2.1 t ht
  simpa only [hm] using hp

-- Nonzero charge and cosmological constant check all three source components.
example : waveSource 2 3 ![2, 0, 0] ![1, 2, 3] ![4, 5, 6] = ![-1 / 2, -13 / 2, -145 / 8] := by
  ext i
  fin_cases i <;> dsimp [waveSource, radialPotential, conformalPotential] <;> norm_num

-- The transverse derivative is an arbitrary L2 equivalence class of continuous sections.
example {μ : Measure (Icc (0 : ℝ) 1)} [IsFiniteMeasure μ]
    (u : Lp C(Icc (0 : ℝ) 1, WaveVector) 2 μ) :
    ∀ᵐ x ∂μ, ∀ y : Icc (0 : ℝ) 1,
      waveMixedSource 0 0 (ContinuousMap.const _ ![1, 0, 0]) (ContinuousMap.const _ ![1, 0, 0])
        (fun _ => by norm_num) u x y 0 = -1 / 4 - u x y 0 := by
  have h := waveMixedSource_ae 0 0 (ContinuousMap.const _ ![1, 0, 0])
    (ContinuousMap.const _ ![1, 0, 0]) (fun _ => by norm_num) u
  filter_upwards [h] with x hx
  intro y
  rw [hx y]
  dsimp [waveSource, radialPotential]
  norm_num

-- The horizontal integral gains sqrt(length), with values in the actual C_v space.
example (f : Lp C(Icc (0 : ℝ) 1, WaveVector) 2 (volume.restrict (Icc (0 : ℝ) 4))) :
    ‖horizontalPrimitive (by norm_num : (0 : ℝ) ≤ 4) f‖ ≤ 2 * ‖f‖ := by
  have h := horizontalPrimitive_norm_le (by norm_num : (0 : ℝ) ≤ 4) f
  have hsqrt : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  simpa only [sub_zero, hsqrt] using h

-- A shifted interval checks the primitive's base point and its orientation.
example : continuousPrimitive (by norm_num : (-1 : ℝ) ≤ 2)
    (ContinuousMap.const _ (3 : ℝ)) ⟨2, by norm_num⟩ = 9 := by
  change (∫ t in (-1 : ℝ)..2, (3 : ℝ)) = 9
  norm_num

-- Both primitives act on the same real restricted measure, without a subtype measure.
example (f : Lp C(Icc (0 : ℝ) 3, WaveVector) 2 (volume.restrict (Icc (0 : ℝ) 4))) :
    ‖verticalPrimitive (by norm_num : (0 : ℝ) ≤ 3) f‖ ≤ 3 * ‖f‖ := by
  simpa only [sub_zero] using verticalPrimitive_norm_le (by norm_num : (0 : ℝ) ≤ 3) f

-- The rough incoming trace is preserved for arbitrary L2 data, not only smooth data.
example (uIn : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (u : WaveTransverse 1 2) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      (waveIteration (by norm_num) (by norm_num) 2 3
        (ContinuousMap.const _ ![1, 0, 0]) (ContinuousMap.const _ ![1, 0, 0]) uIn
        (ContinuousMap.const _ (ContinuousMap.const _ ![1, 0, 0]), 0, u)
        (fun _ _ => by norm_num)).2.2 t ⟨0, by norm_num⟩ = uIn t :=
  waveIteration_incoming_derivative _ _ _ _ _ _ _ _ _

-- One coefficient works for every square size and all rough data with the same L2 bound.
example {lo hi : WaveVector × WaveVector} (hr : 0 < lo.1 0) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (d : ℝ) (hd : 0 ≤ d), d ≤ 1 →
      ∀ (zIn vOut : C(Icc 0 d, WaveVector))
        (uIn : Lp WaveVector 2 (volume.restrict (Icc 0 d))) (x y : WaveState d d)
        (hx : waveRange lo hi x) (hy : waveRange lo hi y), ‖x.2.2‖ ≤ 4 →
      ‖waveIteration hd hd 2 3 zIn vOut uIn x (waveRange_radius hr hx) -
        waveIteration hd hd 2 3 zIn vOut uIn y (waveRange_radius hr hy)‖ ≤
        B * (Real.sqrt d + d) * ‖x - y‖ := by
  obtain ⟨B, hB, h⟩ := waveIteration_local_bound (hi := hi) hr 2 3 4
  exact ⟨B, hB, fun _ hd hd1 => h hd hd hd1⟩

-- The two characteristic primitives commute for arbitrary rough transverse sources.
example (f : WaveTransverse 2 3) :
    longitudinalIntegral (by norm_num : (0 : ℝ) ≤ 3)
      (horizontalPrimitive (by norm_num : (0 : ℝ) ≤ 2) f) =
    horizontalPrimitive (by norm_num : (0 : ℝ) ≤ 2)
      (verticalPrimitive (by norm_num : (0 : ℝ) ≤ 3) f) :=
  (horizontalPrimitive_compLp (by norm_num) (continuousPrimitiveL (E := WaveVector) (by norm_num)) f).symm

-- The continuous longitudinal sections have an L2 transverse derivative as a Banach-valued curve.
example (f : WaveTransverse 2 3) :
    ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 2),
      HasDerivWithinAt (intervalExtension (by norm_num : (0 : ℝ) ≤ 2)
        (horizontalPrimitive (by norm_num : (0 : ℝ) ≤ 2) f)) (f u) (Icc 0 2) u :=
  horizontalPrimitive_ae_hasDerivWithinAt _ _

-- Constant characteristic data still have a nonzero nonlinear source; a positive local size exists.
example : ∃ d : ℝ, ∃ hd : 0 < d, ∃ x : WaveState d d,
    IsWaveIntegral hd.le hd.le 0 0 (ContinuousMap.const _ ![1, 0, 0]) 0 0 x ∧
      (∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) d),
        HasDerivWithinAt (intervalExtension hd.le x.1) (x.2.2 u) (Icc 0 d) u) := by
  obtain ⟨δ, _hδ, _hδr, d, hd, _hd1, h⟩ := exists_local_wave_integral 0 0 1 1 0
    (by norm_num) (by norm_num) (by norm_num)
  have hz : ‖(ContinuousMap.const (Icc (0 : ℝ) d) ![1, 0, 0] : C(Icc 0 d, WaveVector))‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ (by norm_num)).2
    intro u
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro i
    fin_cases i <;> norm_num
  obtain ⟨x, hx, _hunique⟩ := h hd.le hd.le le_rfl le_rfl (ContinuousMap.const _ ![1, 0, 0]) 0 0
    (fun _ => by norm_num) hz (by simp) (by simp)
  have hzero : horizontalPrimitive hd.le (0 : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) d))) = 0 := by
    simpa using horizontalPrimitive_sub hd.le (0 : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) d))) 0
  exact ⟨d, hd, x, hx.2, hx.2.horizontal_derivative (by rw [hzero, add_zero])⟩

-- The mixed derivative uses the actual source at almost every u, simultaneously for every v.
example {U V : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 zIn vOut uIn x) :
    ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      HasDerivWithinAt (fun t => intervalExtension hU x.2.1 t v)
        (waveSource 2 3 (x.1 (projIcc 0 U hU u) v) (x.2.2 u v)
          (x.2.1 (projIcc 0 U hU u) v)) (Icc 0 U) u := hx.wave_equation

-- A nonzero scalar input checks the radius, scalar integral and quadratic conformal sign.
example : incomingWaveCurve (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
    (le_refl (4 : ℝ≥0∞)) (memLp_const (2 : ℝ)) 7 ⟨1, by norm_num⟩ =
      ![1, 9, Real.log 4 - 6] := by
  rw [incomingWaveCurve_apply]
  ext i
  fin_cases i
  · norm_num [incomingRadius]
  · norm_num [incomingPhi]
  · dsimp [incomingLogOmega]
    have he : (fun u : ℝ => (2 - u) * (2 : ℝ) ^ 2) = fun u => 8 - 4 * u := by funext; ring
    have hg : IntervalIntegrable (fun u : ℝ => 4 * u) volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    rw [he, intervalIntegral.integral_sub intervalIntegrable_const hg]
    rw [intervalIntegral.integral_const_mul (4 : ℝ) (fun u : ℝ => u)]
    norm_num

-- The physical incoming gauge r=R-u has a local solution even at the exact L4 endpoint.
example : ∃ d : ℝ, ∃ hd : 0 < d, ∃ hdR : d < 2, ∃ x : WaveState d d,
    IsWaveIntegral hd.le hd.le 0 0
      (incomingWaveCurve hd.le hdR (le_refl (4 : ℝ≥0∞)) (memLp_const (0 : ℝ)) 0) 0
      (incomingWaveVelocity hdR (le_refl (4 : ℝ≥0∞)) (memLp_const (0 : ℝ))) x := by
  obtain ⟨δ, _hδ, d, hd, hdR, hd1, hsolve⟩ := exists_local_incoming_wave 0 0 2 0 1
    (by norm_num) (by norm_num) (0 : C(ℝ, WaveVector))
  let hf : MemLp (fun _ : ℝ => (0 : ℝ)) 4 (volume.restrict (Icc 0 d)) := memLp_const 0
  let c : C(Icc 0 d, WaveVector) := ContinuousMap.const _ ![-1, 0, 0]
  have he : incomingWaveVelocity hdR (le_refl 4) hf = intervalToLp hd.le 2 c := by
    apply Lp.ext
    filter_upwards [incomingWaveVelocity_ae hdR (le_refl 4) hf, intervalToLp_ae hd.le 2 c] with u hu hc
    rw [hu, hc]
    ext i
    fin_cases i <;> simp [incomingVelocity, c]
  have hc : ‖c‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ (by norm_num)).2
    intro u
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro i
    fin_cases i <;> norm_num [c]
  have hn : ‖incomingWaveVelocity hdR (le_refl 4) hf‖ ≤ 1 := by
    rw [he]
    have hb := intervalToL2_norm_le hd.le c
    rw [sub_zero] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg d)).trans (by simpa using Real.sqrt_le_one.2 hd1))
  obtain ⟨x, hx, _hunique⟩ := hsolve hd.le hd.le hdR le_rfl le_rfl (le_refl 4) hf hn
  exact ⟨d, hd, hdR, x, hx.2⟩

-- A stationary radius has nonzero logarithmic lapse velocity in the chosen horizon gauge.
example : horizonWaveCurve (by norm_num : (0 : ℝ) ≤ 2) 1 0 0
    (h := fun _ => 0) (r := fun _ => 2) continuous_const
    (fun _ => by simp) continuous_const (fun _ => by norm_num) ⟨2, by norm_num⟩ =
      ![2, 0, Real.log 4 + 1] := by
  rw [horizonWaveCurve_apply (hφ := fun _ => by simp) (hrd := ?_)]
  · ext i
    fin_cases i <;> norm_num [horizonVector, horizonPhi, horizonLogOmega, horizonK, horizonMass]
  · intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)

-- The stability estimate gives uniqueness for all local fixed points in the stated range.
example {lo hi : WaveVector × WaveVector} (hr : 0 < lo.1 0) (e Λ M : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ 1 →
      B * (Real.sqrt U + V) ≤ 1 / 2 →
      ∀ (z : C(Icc 0 U, WaveVector)) (v : C(Icc 0 V, WaveVector))
        (u : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x y : WaveState U V),
        IsWaveIntegral hU hV e Λ z v u x → IsWaveIntegral hU hV e Λ z v u y →
        waveRange lo hi x → waveRange lo hi y → ‖x.2.2‖ ≤ M → x = y := by
  obtain ⟨B, hB, h⟩ := local_wave_stability (hi := hi) hr e Λ M
  refine ⟨B, hB, ?_⟩
  intro U V hU hV hU1 hsize z v u x y hx hy hxr hyr hxu
  have hd := h hU hV hU1 hsize z z v v u u x y hx hy hxr hyr hxu
  simp only [sub_self, norm_zero, add_zero, mul_zero] at hd
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hd (norm_nonneg (x - y))))

-- The scalar budget controls the complete, genuinely nonzero incoming velocity.
example : ‖incomingWaveVelocity (by norm_num : (1 : ℝ) < 2)
    (le_refl (4 : ℝ≥0∞)) (memLp_const (2 : ℝ))‖ ≤ 11 := by
  have hb : (eLpNorm (fun _ : ℝ => (2 : ℝ)) 4 (volume.restrict (Icc (0 : ℝ) 1))).toReal ≤ 2 := by
    rw [eLpNorm_const' (2 : ℝ) (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
    norm_num
  have h := incomingWaveVelocity_norm_le (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    (by norm_num : (1 : ℝ) < 2) (le_refl (4 : ℝ≥0∞)) (memLp_const (2 : ℝ)) hb
  norm_num at h ⊢
  exact h

-- The finite-measure inclusion also covers the infinite scalar exponent.
example {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc (0 : ℝ) 1)))
    (hb : (eLpNorm f ∞ (volume.restrict (Icc (0 : ℝ) 1))).toReal ≤ 2) :
    ‖incomingWaveVelocity (by norm_num : (1 : ℝ) < 2) (by simp : (4 : ℝ≥0∞) ≤ ∞) hf‖ ≤ 11 := by
  have h := incomingWaveVelocity_norm_le (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    (by norm_num : (1 : ℝ) < 2) (by simp : (4 : ℝ≥0∞) ≤ ∞) hf hb
  norm_num at h ⊢
  exact h

section L4
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

-- Strong L4 convergence of arbitrary rough scalar data gives strong vector L2 convergence.
example {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 4 (volume.restrict (Icc (0 : ℝ) 1)))
    (hg : MemLp g 4 (volume.restrict (Icc (0 : ℝ) 1)))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (nhds (hg.toLp g))) :
    Tendsto (fun n => incomingWaveVelocity (by norm_num : (1 : ℝ) < 2) le_rfl (hf n)) atTop
      (nhds (incomingWaveVelocity (by norm_num : (1 : ℝ) < 2) le_rfl hg)) :=
  incomingWaveVelocity_tendsto (by norm_num) (by norm_num) hf hg hlim
end L4

-- The radial flux has the exact neutral, zero-cosmological-constant coefficient -1/4.
example (u : Icc (0 : ℝ) 1) (v : Icc (0 : ℝ) 2) :
    radialFluxField 0 0 (ContinuousMap.const _ (ContinuousMap.const _ ![2, 7, 0]))
      (fun _ _ => by norm_num) u v = -(1 / 4 : ℝ) := by
  change 2 * (Real.exp 0 * radialPotential 2 0 0) = -(1 / 4 : ℝ)
  norm_num [radialPotential]

-- Actual rough incoming data give one continuous representative for all longitudinal times.
example {U V R : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 (incomingWaveCurve hU hUR le_rfl hf 7) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) :
    (∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      x.2.2 u v 0 = radialNuField hV 2 3 (incomingWaveCurve hU hUR le_rfl hf 7)
        x.1 hx.choose (projIcc 0 U hU u) v) ∧
    (∀ u : Icc 0 U, radialNuField hV 2 3 (incomingWaveCurve hU hUR le_rfl hf 7)
      x.1 hx.choose u ⟨0, le_rfl, hV⟩ = -1) :=
  ⟨hx.incoming_radialNu_ae hU hV hUR le_rfl hf, hx.radialNu_incoming hx.choose⟩

-- Continuous and L2 primitives agree on the same shifted real interval.
example (f : C(Icc (-1 : ℝ) 2, WaveVector)) :
    horizontalPrimitive (by norm_num : (-1 : ℝ) ≤ 2)
      (intervalToLp (by norm_num : (-1 : ℝ) ≤ 2) 2 f) =
      continuousPrimitive (by norm_num : (-1 : ℝ) ≤ 2) f :=
  horizontalPrimitive_intervalToLp _ f

-- The physical incoming derivative is -1 at every u, including the endpoint.
example {U V R : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 (incomingWaveCurve hU hUR le_rfl hf 7) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) (u : Icc 0 U) :
    HasDerivWithinAt (fun t => intervalExtension hU x.1 t ⟨0, le_rfl, hV⟩ 0) (-1) (Icc 0 U) u := by
  have hd := hx.incoming_radial_hasDerivWithinAt hU hV hUR le_rfl hf ⟨0, le_rfl, hV⟩ u.property
  rwa [hx.radialNu_incoming hx.choose u] at hd

-- Both radial mixed derivatives equal the same continuous nonlinear source everywhere.
example {U V : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 zIn vOut uIn x)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV 2 3 zIn x.1 hx.choose
    let F := radialSourceField 2 3 x.1 x.2.1 N hx.choose
    HasDerivWithinAt (intervalExtension hV (N u)) (F u v) (Icc 0 V) v ∧
      HasDerivWithinAt (fun t => intervalExtension hU x.2.1 t v 0) (F u v) (Icc 0 U) u :=
  ⟨hx.radialNu_hasDerivWithinAt hx.choose u v, hx.lambda_hasDerivWithinAt hx.choose hinu v u.property⟩

-- Local existence supplies a nonvacuous horizon derivative and gauge, not just a trace assumption.
example : ∃ d : ℝ, ∃ hd : 0 < d, ∃ x : WaveState d d,
    HasDerivWithinAt (fun t => intervalExtension hd.le x.1 t ⟨d, hd.le, le_rfl⟩ 0)
      (-Real.exp (d / 2)) (Icc 0 d) 0 ∧
    -Real.exp (x.1 ⟨0, le_rfl, hd.le⟩ ⟨d, hd.le, le_rfl⟩ 2) /
      (4 * (-Real.exp (d / 2))) = 1 := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨d, hd, hdR, _hd1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 0 le_rfl
  let hf : MemLp (fun _ : ℝ => (0 : ℝ)) 4 (volume.restrict (Icc 0 d)) := memLp_const 0
  obtain ⟨x, hx, _htraces⟩ := hsolve hd.le hd.le hdR le_rfl le_rfl (le_refl 4) hf (by simp)
  let v : Icc 0 d := ⟨d, hd.le, le_rfl⟩
  have hν := hx.horizon_radial_trace hd.le hd.le hdR hc hi hrc hr0 hφ hrd (le_refl 4) hf v
  norm_num [horizonNu, horizonK, horizonMass, v] at hν
  have hdν := hx.incoming_radial_hasDerivWithinAt hd.le hd.le hdR (le_refl 4) hf v
    (show (0 : ℝ) ∈ Icc 0 d from ⟨le_rfl, hd.le⟩)
  rw [hν] at hdν
  have hg := (hx.horizon_gauge hd.le hd.le hdR hc hi hrc hr0 hφ hrd (le_refl 4) hf v).2.2
  rw [hν] at hg
  exact ⟨d, hd, x, hdν, hg⟩

-- At the critical input exponent the scalar component improves from the constructed L2 to L4.
example {U V R : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 (incomingWaveCurve hU hUR le_rfl hf 7) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) :
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u)) 4 (volume.restrict (Icc 0 U)) :=
  (hx.incoming_transverse_regularity hU hV hUR le_rfl hf).1

-- A higher input exponent gives the distinct conformal exponent p/2, not merely L2.
example {U V R : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 6 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 (incomingWaveCurve hU hUR (by norm_num) hf 7) vOut
      (incomingWaveVelocity hUR (by norm_num) hf) x) :
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u)) 6 (volume.restrict (Icc 0 U)) ∧
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (2 : Fin 3))) (x.2.2 u)) 3 (volume.restrict (Icc 0 U)) := by
  have hhalf : (6 : ℝ≥0∞) / 2 = 3 := by
    symm
    apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2
    norm_num
  simpa only [hhalf] using hx.incoming_transverse_regularity hU hV hUR (by norm_num) hf

-- Bounded incoming data preserve both bounded transverse components.
example {U V R : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 (incomingWaveCurve hU hUR le_top hf 7) vOut
      (incomingWaveVelocity hUR le_top hf) x) :
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u)) ∞ (volume.restrict (Icc 0 U)) ∧
    MemLp (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
      (ContinuousLinearMap.proj (2 : Fin 3))) (x.2.2 u)) ∞ (volume.restrict (Icc 0 U)) := by
  have hhalf : (∞ : ℝ≥0∞) / 2 = ∞ := ENNReal.top_div_of_ne_top (by norm_num)
  simpa only [hhalf] using hx.incoming_transverse_regularity hU hV hUR le_top hf

-- The longitudinal scalar correction has the sign -nu*phi_v and the correct integration length.
example (u : Icc (0 : ℝ) 1) :
    scalarTransportCorrection (by norm_num : (0 : ℝ) ≤ 2)
      (ContinuousMap.const _ (ContinuousMap.const _ (-2 : ℝ)))
      (ContinuousMap.const _ (ContinuousMap.const _ ![1, 3, 0])) u ⟨2, by norm_num⟩ = 12 := by
  change (∫ w in (0 : ℝ)..2, (-(-2 : ℝ)) * 3) = 12
  norm_num

-- Nonzero initial values and slopes check every term of the absolutely continuous product rule.
example :
    let f := intervalToLp (by norm_num : (0 : ℝ) ≤ 1) 2 (ContinuousMap.const _ (2 : ℝ))
    let g := intervalToLp (by norm_num : (0 : ℝ) ≤ 1) 2 (ContinuousMap.const _ (3 : ℝ))
    (∫ s in (0 : ℝ)..1, f s * (5 + ∫ w in 0..s, g w) + (4 + ∫ w in 0..s, f w) * g s) = 28 := by
  dsimp only
  have hp := l2_primitive_product (by norm_num : (0 : ℝ) ≤ 1)
    (intervalToLp (by norm_num) 2 (ContinuousMap.const _ (2 : ℝ)))
    (intervalToLp (by norm_num) 2 (ContinuousMap.const _ (3 : ℝ))) 4 5 ⟨1, by norm_num⟩
  rw [horizontalPrimitive_intervalToLp, horizontalPrimitive_intervalToLp] at hp
  norm_num [continuousPrimitive, intervalExtension_apply] at hp
  linarith only [hp]

-- The horizontal integral law holds for actual rough data, with no smooth approximation assumed.
example {U V R : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 (incomingWaveCurve hU hUR le_rfl hf 7) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) (u : Icc 0 U) (v : Icc 0 V) :
    x.1 u v 0 * x.2.1 u v 1 = x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1 +
      ∫ s in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU s) v 0 * x.2.2 s v 1 :=
  hx.theta_integral (c := ![R, 7, Real.log 4]) rfl u v

-- Both nonzero charge and cosmological terms contribute to the differentiated flux.
example : radialFluxDifferential 2 3
    (ContinuousMap.const (Icc (0 : ℝ) 1) ![2, 0, Real.log 4])
    (ContinuousMap.const _ ![3, 5, 7]) (fun _ => by norm_num) ⟨1, by norm_num⟩ = 117 := by
  change Real.exp (Real.log 4) *
    (3 * (-(2 : ℝ) ^ 2 / (2 * 2 ^ 3) + 3 * 2 / 2) + 7 * 2 * radialPotential 2 2 3) = 117
  norm_num [radialPotential, Real.exp_log]

-- Absolute continuity is proved in the full C_v norm, also on a degenerate u interval.
example (f : Lp C(Icc (0 : ℝ) 1, ℝ) 2 (volume.restrict (Icc (0 : ℝ) 0))) :
    AbsolutelyContinuousOnInterval
      (fun t => (ContinuousMap.const _ (3 : ℝ)) +
        intervalExtension le_rfl (horizontalPrimitive le_rfl f) t) 0 0 :=
  horizontalPrimitive_absolutelyContinuous le_rfl f _

-- Critical rough data give the actual integral constraint, with no assumed second derivative.
example {U V R : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 (incomingWaveCurve hU hUR le_rfl hf 7) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV 2 3 (incomingWaveCurve hU hUR le_rfl hf 7) x.1 hx.choose
    N u v * Real.exp (-x.1 u v 2) = N ⟨0, le_rfl, hU⟩ v * Real.exp (-x.1 ⟨0, le_rfl, hU⟩ v 2) -
      ∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * Real.exp (-intervalExtension hU x.1 t v 2) *
        (x.2.2 t v 1) ^ 2 := by
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR le_rfl hf 7
  exact (hx.transverse_constraint_integral hx.choose rfl hn hl v).2 u

-- The density is integrable even at the p = infinity endpoint.
example {U V R : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV 2 3 (incomingWaveCurve hU hUR le_top hf 7) vOut
      (incomingWaveVelocity hUR le_top hf) x) (v : Icc 0 V) :
    IntervalIntegrable (fun t => intervalExtension hU x.1 t v 0 *
      Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2) volume 0 U := by
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR le_top hf 7
  exact (hx.transverse_constraint_integral hx.choose rfl hn hl v).1

-- Local existence and horizon normalization imply signs throughout a nonempty rectangle.
example : ∃ d : ℝ, ∃ _hd : 0 < d, ∃ x : WaveState d d, ∃ N : C(Icc 0 d, C(Icc 0 d, ℝ)),
    ∀ u v, 0 < x.1 u v 0 ∧ N u v < 0 ∧
      0 < -Real.exp (x.1 u v 2) / (4 * N u v) ∧ -Real.exp (x.1 u v 2) / (4 * N u v) ≤ 1 := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨d, hd, hdR, _hd1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 0 le_rfl
  let hf : MemLp (fun _ : ℝ => (0 : ℝ)) 4 (volume.restrict (Icc 0 d)) := memLp_const 0
  obtain ⟨x, hx, _htraces⟩ := hsolve hd.le hd.le hdR le_rfl le_rfl (le_refl 4) hf (by simp)
  refine ⟨d, hd, x, radialNuField hd.le 0 0
    (incomingWaveCurve hd.le hdR (le_refl 4) hf (horizonPhi (fun _ => 0) (fun _ => 2) 0))
    x.1 hx.choose, fun u v => ?_⟩
  exact (hx.interior_gauge hd.le hd.le hdR hc hi hrc hr0 hφ hrd (le_refl 4) hf u v).2

-- Nonzero radial, scalar and conformal velocities check every quadratic-flux term.
example : radialFluxVariation ![2, 0, Real.log 4] ![3, 5, 7] = -49 := by
  change (3 : ℝ) ^ 2 + 2 * 3 * 7 - 2 ^ 2 * 5 ^ 2 = -49
  norm_num

section OutgoingConstraints

variable {M e Λ U V : ℝ} {h r : ℝ → ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)

include hφ hrd

-- The actual second radial derivative exists at the bottom endpoint for rough L4 input.
example {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (u : Icc 0 U) :
    HasDerivWithinAt (fun t => intervalExtension hV (x.2.1 u) t 0)
      (x.2.1 u ⟨0, le_rfl, hV⟩ 2 * x.2.1 u ⟨0, le_rfl, hV⟩ 0 -
        x.1 u ⟨0, le_rfl, hV⟩ 0 * (x.2.1 u ⟨0, le_rfl, hV⟩ 1) ^ 2) (Icc 0 V) 0 :=
  hx.outgoing_radial_constraint hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u ⟨le_rfl, hV⟩

-- Bounded incoming data require only continuity, not a derivative, of the horizon radiation.
example {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x)
    (u : Icc 0 U) (v : Icc 0 V) :
    x.2.1 u v 0 * Real.exp (-x.1 u v 2) =
      x.2.1 u ⟨0, le_rfl, hV⟩ 0 * Real.exp (-x.1 u ⟨0, le_rfl, hV⟩ 2) -
        ∫ t in (0 : ℝ)..v, intervalExtension hV (x.1 u) t 0 *
          Real.exp (-intervalExtension hV (x.1 u) t 2) * (intervalExtension hV (x.2.1 u) t 1) ^ 2 :=
  hx.outgoing_integral_constraint hU hV hUR hc hi hrc hr0 hφ hrd le_top hf u v

-- Vanishing transverse scalar flux leaves the horizon normalization unchanged.
example {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (hzero : ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, x.2.2 t v 1 = 0)
    (u : Icc 0 U) (v : Icc 0 V) :
    -Real.exp (x.1 u v 2) /
      (4 * radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose u v) = 1 := by
  rw [(hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf v).2 u]
  have he : (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU (radialNuField hV e Λ
        (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose) t v)) = 0 := by
    rw [intervalIntegral.integral_of_le u.property.1]
    apply integral_eq_zero_of_ae
    have hsub : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
    filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hzero] with t ht
    simp [ht v]
  rw [he]
  norm_num

-- The logarithmic density is integrable at p=infinity without a prescribed radius minimum.
example {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x)
    (v : Icc 0 V) :
    IntervalIntegrable (fun t => intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU (radialNuField hV e Λ
        (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose) t v)) volume 0 U :=
  (hx.horizon_kappa_exponential hU hV hUR hc hi hrc hr0 hφ hrd le_top hf v).1

-- The horizon-anchored identity and absolute estimate also hold at v=0 and p=infinity.
example {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x) :
    let v : Icc 0 V := ⟨0, le_rfl, hV⟩
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
    let R := fun t => intervalExtension hU x.1 t v 0
    let m := fun t => intervalExtension hU (massField e Λ x.1 x.2.1 N hx.choose) t v
    let κ := fun t => -Real.exp (intervalExtension hU x.1 t v 2) / (4 * intervalExtension hU N t v)
    let K := fun t => horizonK (R t) (m t) e Λ
    let S := fun t => κ t / intervalExtension hU N t v * (1 - e ^ 2 / (R t) ^ 2 - Λ * (R t) ^ 2) *
      (x.2.2 t v 1) ^ 2 +
      2 * x.2.2 t v 1 * intervalExtension hU x.2.1 t v 1
    IntervalIntegrable S volume 0 U ∧ ∀ u : Icc 0 U,
      x.2.1 u v 2 - 2 * K u = 2 * K u * (κ u - 1) - ∫ t in (0 : ℝ)..u, S t ∧
      |x.2.1 u v 2 - 2 * K u| ≤ 2 * |K u| * |κ u - 1| + ∫ t in (0 : ℝ)..u, |S t| :=
  hx.horizon_conformal_identity hU hV hUR hc hi hrc hr0 hφ hrd le_top hf ⟨0, le_rfl, hV⟩

end OutgoingConstraints

example {a b : ℝ} (hb : |b| ≤ 3) :
    |-(1 / 2 : ℝ) * a ^ 2 + 2 * a * b| ≤ 2 * a ^ 2 + 9 := by
  have hh := conformal_source_bound (r := 2) (n := 2) (κ := 1) (C := 1)
    (ρ := 2) (G := 2) (H := 3) (a := a) (by norm_num) le_rfl (by norm_num)
    (by norm_num) le_rfl (by norm_num) hb
  norm_num at hh
  simpa only [neg_mul] using hh

section ConformalConstraint

variable {M e Λ U V ρ G : ℝ} {h r : ℝ → ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)

-- Vanishing longitudinal radiation leaves only the constraint energy, including p=infinity.
example {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x)
    (hρ : 0 < ρ) (v : Icc 0 V) (hlo : ∀ u, ρ ≤ x.1 u v 0)
    (hG : ∀ u, |1 - e ^ 2 / (x.1 u v 0) ^ 2 - Λ * (x.1 u v 0) ^ 2| ≤ G)
    (hzero : ∀ u, x.2.1 u v 1 = 0) (u : Icc 0 U) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
    let K := horizonK (x.1 u v 0) (massField e Λ x.1 x.2.1 N hx.choose u v) e Λ
    |x.2.1 u v 2 - 2 * K| ≤ (2 * |K| + G / ρ + 1) *
      ∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 / (-intervalExtension hU N t v) := by
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, zero_mul, add_zero] using
    hx.horizon_conformal_bound hU hV hUR hc hi hrc hr0 hφ hrd le_top hf hρ v hlo hG
      (H := 0) (fun w => by rw [hzero w, abs_zero]) u

-- At u=0 the quantitative estimate recovers the exact horizon identity for rough L4 input.
example {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (hρ : 0 < ρ) (v : Icc 0 V) (hlo : ∀ u, ρ ≤ x.1 u v 0)
    (hG : ∀ u, |1 - e ^ 2 / (x.1 u v 0) ^ 2 - Λ * (x.1 u v 0) ^ 2| ≤ G)
    {H : ℝ} (hH : ∀ u, |x.2.1 u v 1| ≤ H) :
    let o : Icc 0 U := ⟨0, le_rfl, hU⟩
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    x.2.1 o v 2 = 2 * horizonK (x.1 o v 0) (massField e Λ x.1 x.2.1 N hx.choose o v) e Λ := by
  have hh := hx.horizon_conformal_bound hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf hρ v hlo hG hH ⟨0, le_rfl, hU⟩
  have hray : x.1 ⟨0, le_rfl, hU⟩ v 0 = r v :=
    congrArg (fun z : WaveVector => z 0) ((hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf).2 v)
  dsimp only at hh ⊢
  rw [intervalIntegral.integral_same, mul_zero, hray, sub_self, mul_zero, add_zero] at hh
  rw [hray]
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)

end ConformalConstraint

-- A constructed rectangle with nonzero incoming scalar data satisfies the outgoing constraint.
example : ∃ d : ℝ, ∃ hd : 0 < d, ∃ x : WaveState d d,
    x.1 ⟨d, hd.le, le_rfl⟩ ⟨0, le_rfl, hd.le⟩ 1 = d ∧
    ∀ u v : Icc 0 d, x.2.1 u v 0 * Real.exp (-x.1 u v 2) =
      x.2.1 u ⟨0, le_rfl, hd.le⟩ 0 * Real.exp (-x.1 u ⟨0, le_rfl, hd.le⟩ 2) -
        ∫ t in (0 : ℝ)..v, intervalExtension hd.le (x.1 u) t 0 *
          Real.exp (-intervalExtension hd.le (x.1 u) t 2) * (intervalExtension hd.le (x.2.1 u) t 1) ^ 2 := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨d, hd, hdR, _hd1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 1 zero_le_one
  let hf : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d)) := memLp_const 1
  have hnorm : (eLpNorm (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d))).toReal ≤ 1 := by
    by_cases hm : volume.restrict (Icc (0 : ℝ) d) = 0
    · simp [hm]
    · simp [eLpNorm_const (1 : ℝ) (by norm_num : (∞ : ℝ≥0∞) ≠ 0) hm]
  obtain ⟨x, hx, htraces⟩ := hsolve hd.le hd.le hdR le_rfl le_rfl le_top hf hnorm
  refine ⟨d, hd, x, ?_, fun u v => ?_⟩
  · rw [htraces.1 ⟨d, hd.le, le_rfl⟩]
    simp [incomingPhi, horizonPhi]
  · exact hx.outgoing_integral_constraint hd.le hd.le hdR hc hi hrc hr0 hφ hrd le_top hf u v

-- The charged cosmological potential is bounded on a fixed positive radial interval.
example : ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc (1 / 2 : ℝ) 3, |radialPotential r 2 5| ≤ B :=
  radialPotential_bounded 2 5 (by norm_num)

-- Concrete budgets check the factor four, both radial powers, and the logarithmic rate.
example {U V e Λ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hP : ∀ r ∈ Icc (1 : ℝ) 2, |radialPotential r e Λ| ≤ 5)
    (hlo : ∀ u v, 1 ≤ x.1 u v 0) (haxis : ∀ v, x.1 ⟨0, le_rfl, hU⟩ v 0 ≤ 2)
    (hvel : ∀ v, |vOut v 0| ≤ 3)
    (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hx.choose u v < 0)
    (homega : ∀ u v, Real.exp (x.1 u v 2) ≤ -4 * radialNuField hV e Λ zIn x.1 hx.choose u v)
    (u : Icc 0 U) (v : Icc 0 V) :
    |x.2.1 u v 0| ≤ 86 ∧
      Real.exp (-106 * v) ≤ -radialNuField hV e Λ zIn x.1 hx.choose u v ∧
      -radialNuField hV e Λ zIn x.1 hx.choose u v ≤ Real.exp (106 * v) ∧
      Real.exp (x.1 u v 2) ≤ 4 * Real.exp (106 * v) := by
  have hb := hx.finite_radial_flux_bound hx.choose hzin hinu (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 5) hP hlo haxis hvel
    (fun u v => (hnu u v).le) homega
  have hl (a : Icc 0 U) (b : Icc 0 V) : |x.2.1 a b 0| ≤ 86 := by
    have hh := (hb a b).2.2
    norm_num at hh
    exact hh
  have hn := hx.finite_radial_rate_bound hx.choose (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 86) hlo (fun u v => hP _ ⟨hlo u v, (hb u v).1⟩)
    hl hnu homega u v
  norm_num at hn
  exact ⟨hl u v, by simpa only [neg_mul] using hn⟩

-- One set of constants works for every critical L4 datum with the given radius lower bound.
example {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
      {x : WaveState U V},
      IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x →
      (∀ u v, ρ ≤ x.1 u v 0) → ∀ u v, |x.2.1 u v 0| ≤ A := by
  obtain ⟨_R, A, _C, _hR, hA, _hC, hb⟩ := exists_uniform_finite_geometry hU hV hUR hc hi hrc hr0 hφ hrd hρ
  refine ⟨A, hA, ?_⟩
  intro f hf x hx hlo u v
  exact (hb le_rfl hf hx hlo u v).2.2.1

-- Nonzero scalar data supply an actual solution satisfying all finite-state bounds.
example : ∃ d : ℝ, ∃ hd : 0 < d, ∃ x : WaveState d d, ∃ A C B w T : ℝ,
    0 < B ∧ 0 < w ∧ 0 < T ∧ ‖x‖ ≤ T ∧ x.1 ⟨d, hd.le, le_rfl⟩ ⟨0, le_rfl, hd.le⟩ 1 = d ∧
      (∀ u v, |x.2.1 u v 0| ≤ A ∧ w ≤ Real.exp (x.1 u v 2) ∧
        Real.exp (x.1 u v 2) ≤ 4 * Real.exp (C * (v : ℝ))) ∧
      (∀ u : Icc 0 d, ‖waveCoordinateField 1 x.2.1 u‖ ≤ B) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 d), ∀ v : Icc 0 d,
        |x.2.2 u v 1| ≤ B * 2 ∧ |x.2.2 u v 2| ≤ 2 + T * 2 := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨d, hd, hdR, hd1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 1 zero_le_one
  let hf : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d)) := memLp_const 1
  have hnorm : (eLpNorm (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d))).toReal ≤ 1 := by
    by_cases hm : volume.restrict (Icc (0 : ℝ) d) = 0
    · simp [hm]
    · simp [eLpNorm_const (1 : ℝ) (by norm_num : (∞ : ℝ≥0∞) ≠ 0) hm]
  obtain ⟨x, hx, htraces⟩ := hsolve hd.le hd.le hdR le_rfl le_rfl le_top hf hnorm
  have hrcx : Continuous (fun q : Icc 0 d × Icc 0 d => x.1 q.1 q.2 0) := by fun_prop
  obtain ⟨q, _hq, hmin⟩ := isCompact_univ.exists_isMinOn
    ⟨(⟨0, le_rfl, hd.le⟩, ⟨0, le_rfl, hd.le⟩), mem_univ _⟩ hrcx.continuousOn
  have hρ := hx.incoming_radius_pos hd.le hd.le hdR le_top hf q.1 q.2
  have hlo (u v : Icc 0 d) : x.1 q.1 q.2 0 ≤ x.1 u v 0 := hmin (mem_univ (u, v))
  obtain ⟨_R, A, C, _hR, _hA, _hC, hb⟩ :=
    exists_uniform_finite_geometry_on_subrectangles (Vmax := 1) hc hi hrc hr0 hφ hrd hρ
  obtain ⟨B, hB, hscalar⟩ := exists_uniform_finite_scalar_on_subrectangles zero_le_one
    (by norm_num : (0 : ℝ) < 2) hc hi hrc hr0 hφ hrd hρ zero_le_one
  obtain ⟨_k, w, _hk, hw, hkappa⟩ := exists_uniform_finite_kappa_on_subrectangles zero_le_one
    (by norm_num : (0 : ℝ) < 2) hc hi hrc hr0 hφ hrd hρ zero_le_one
  obtain ⟨T, hT, hstate⟩ := exists_uniform_finite_state_on_subrectangles zero_le_one
    (by norm_num : (0 : ℝ) < 2) hc hi hrc hr0 hφ hrd hρ zero_le_one
  have hs := hscalar hd.le hd1 hd.le hd1 hdR le_top hf hnorm hx hlo
  have ht := hstate hd.le hd1 hd.le hd1 hdR le_top hf hnorm hx hlo
  refine ⟨d, hd, x, A, C, B, w, T, hB, hw, hT, ht.1, ?_, (fun u v => ?_), hs.1, ?_⟩
  · rw [htraces.1 ⟨d, hd.le, le_rfl⟩]
    simp [incomingPhi, horizonPhi]
  · exact ⟨(hb hd.le hd.le hd1 hdR le_top hf hx hlo u v).2.2.1,
      (hkappa hd.le hd1 hd.le hd1 hdR le_top hf hnorm hx hlo u v).2,
      (hb hd.le hd.le hd1 hdR le_top hf hx hlo u v).2.2.2.2.2⟩
  · filter_upwards [hs.2.1, ht.2.2] with u hsu htu
    intro v
    exact ⟨by simpa only [show |(1 : ℝ)| + 1 = 2 by norm_num] using hsu v,
      by simpa only [show |(1 : ℝ)| + 1 = 2 by norm_num, one_pow, mul_one] using htu v⟩

-- Zero feedback retains the free bound, including endpoints of the interval.
example {g : ℝ → ℝ} (hg : Continuous g) (hb : ∀ t ∈ Icc (0 : ℝ) 3, g t ≤ 7)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 3) : g u ≤ 7 := by
  have hh := continuous_volterra_bound hg (by norm_num : (0 : ℝ) ≤ 7) (le_refl (0 : ℝ))
    (by simpa only [zero_mul, add_zero] using hb) hu
  simpa using hh

-- The singleton interval needs neither a positive length nor a nonzero measure.
example {g : ℝ → ℝ} (hg : Continuous g) (hb : g 0 ≤ 5) : g 0 ≤ 5 := by
  have hh := continuous_volterra_bound hg (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (0 : ℝ) ≤ 2)
    (U := 0) (by simpa using hb) (u := 0) (by simp)
  simpa using hh

-- The L1 data budget accepts the infinity exponent.
example {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc (0 : ℝ) (1 / 2)))) :
    (∫ t in (0 : ℝ)..(1 / 2 : ℝ), |f t|) ≤
      (eLpNorm f ∞ (volume.restrict (Icc (0 : ℝ) (1 / 2)))).toReal :=
  incoming_integral_abs_le_lp (by norm_num) (by norm_num) le_top hf

-- The explicit scalar constants exercise both transports and the radius division.
example {e Λ : ℝ} {zIn : C(Icc (0 : ℝ) 1, WaveVector)} {vOut : C(Icc (0 : ℝ) 2, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 1))} {x : WaveState 1 2}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive (by norm_num) uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1), uIn u 0 = -1)
    (hlo : ∀ u v, 2 ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ 3)
    (hnu : ∀ u v, |radialNuField (by norm_num) e Λ zIn x.1 hx.choose u v| ≤ 4)
    (hvel : ∀ u v, |x.2.1 u v 0| ≤ 5)
    (hout : ∀ v, |x.1 ⟨0, by norm_num⟩ v 0 * vOut v 1| ≤ 6)
    (hinput : (∫ t in (0 : ℝ)..1, |uIn t 1|) ≤ 7) (u : Icc (0 : ℝ) 1) :
    ‖waveCoordinateField 1 x.2.1 u‖ ≤ (117 / 4 : ℝ) * Real.exp 10 := by
  have hh := (hx.finite_scalar_bound hx.choose hzin hinu (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 5)
    (by norm_num : (0 : ℝ) ≤ 6) (by norm_num : (0 : ℝ) ≤ 7) hlo hin hnu hvel hout hinput).1 u
  norm_num at hh ⊢
  exact hh

-- One constant controls every L4 datum and solution in a fixed norm/radius budget.
example {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ B : ℝ, 0 < B ∧ ∀ {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))),
      (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ 3 →
      ∀ {x : WaveState U V},
      IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x →
      (∀ u v, ρ ≤ x.1 u v 0) →
      (eLpNorm (fun u => (ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 V)
        (ContinuousLinearMap.proj (1 : Fin 3))) (x.2.2 u)) 4 (volume.restrict (Icc 0 U))).toReal ≤ B * 4 := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_finite_scalar hU hU1 hV hUR hc hi hrc hr0 hφ hrd hρ
    (by norm_num : (0 : ℝ) ≤ 3)
  refine ⟨B, hB, ?_⟩
  intro f hf hfn x hx hlo
  simpa only [show (3 : ℝ) + 1 = 4 by norm_num] using (hb le_rfl hf hfn hx hlo).2.2

-- The quadratic data budget preserves both the critical and bounded-data exponents.
example {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 1))) :
    (∫ t in (0 : ℝ)..1, (f t) ^ 2) ≤ (eLpNorm f 4 (volume.restrict (Icc (0 : ℝ) 1))).toReal ^ 2 :=
  incoming_integral_sq_le_lp zero_le_one le_rfl le_rfl hf

example {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc (0 : ℝ) (1 / 2)))) :
    (∫ t in (0 : ℝ)..(1 / 2 : ℝ), (f t) ^ 2) ≤
      (eLpNorm f ∞ (volume.restrict (Icc (0 : ℝ) (1 / 2)))).toReal ^ 2 :=
  incoming_integral_sq_le_lp (by norm_num) (by norm_num) le_top hf

-- Concrete budgets test the reciprocal radial derivative and the conformal factor four.
example {U V e Λ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hinell : ∀ᵐ u ∂volume.restrict (Icc 0 U),
      uIn u 2 = -zIn (projIcc 0 U hU u) 0 * (uIn u 1) ^ 2)
    (hrhi : ∀ u v, x.1 u v 0 ≤ 3)
    (hnlo : ∀ u v, (1 / 2 : ℝ) ≤ -radialNuField hV e Λ zIn x.1 hx.choose u v)
    (haxis : ∀ v, Real.exp (x.1 ⟨0, le_rfl, hU⟩ v 2) =
      -4 * radialNuField hV e Λ zIn x.1 hx.choose ⟨0, le_rfl, hU⟩ v)
    (hscalar : ∀ v, (∫ t in (0 : ℝ)..U, (x.2.2 t v 1) ^ 2) ≤ 2)
    (u : Icc 0 U) (v : Icc 0 V) :
    Real.exp (-12) ≤ -Real.exp (x.1 u v 2) / (4 * radialNuField hV e Λ zIn x.1 hx.choose u v) ∧
      2 * Real.exp (-12) ≤ Real.exp (x.1 u v 2) := by
  have hh := hx.finite_kappa_bound hx.choose hzin hinu hinell (by norm_num : (0 : ℝ) ≤ 3)
    (by norm_num : (0 : ℝ) < 1 / 2) hrhi hnlo haxis hscalar u v
  norm_num at hh ⊢
  exact hh

-- The affine L2 estimate includes a zero-length interval.
example (f g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 0)))
    (hb : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 0), ‖f t‖ ≤ 2 * (‖g t‖ + 1)) :
    ‖f‖ ≤ 2 * ‖g‖ := by
  simpa using l2_norm_le_affine_majorant (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2) f g hb

-- The constant term scales with the square root of the interval length.
example (f g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 4)))
    (hb : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 4), ‖f t‖ ≤ 3 * (‖g t‖ + 1)) :
    ‖f‖ ≤ 3 * (‖g‖ + 2) := by
  have hh := l2_norm_le_affine_majorant (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 3) f g hb
  have hs : Real.sqrt 4 = 2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  simpa only [hs] using hh

-- Scalar values and both conformal derivatives may be arbitrarily large.
example (e Λ : ℝ) : ∃ S : ℝ, 0 ≤ S ∧ ∀ a b c t : ℝ,
    ‖waveSource e Λ ![2, a, 0] ![1, t, b] ![3, 4, c]‖ ≤ S * (|t| + 1) := by
  obtain ⟨S, hS, hb⟩ := exists_waveSource_bound e Λ (ρ := 1) (R := 3) (L := 0) (W := 4) (N := 1)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨S, hS, fun a b c t => ?_⟩
  exact hb ![2, a, 0] ![1, t, b] ![3, 4, c]
    (by norm_num) (by norm_num) (by change |(0 : ℝ)| ≤ 0; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- Three fixed-point identities retain their distinct integration factors.
example {e Λ : ℝ} {zIn : C(Icc (0 : ℝ) 4, WaveVector)} {vOut : C(Icc (0 : ℝ) 2, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 4))} {x : WaveState 4 2}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) e Λ zIn vOut uIn x)
    (hz : ‖zIn‖ ≤ 5) (hv : ‖vOut‖ ≤ 7) (hu : ‖uIn‖ ≤ 11)
    (hF : ‖rectangleSource (by norm_num) e Λ x hx.choose‖ ≤ 3) :
    ‖x.2.1‖ ≤ 13 ∧ ‖x.2.2‖ ≤ 17 ∧ ‖x.1‖ ≤ 31 := by
  obtain ⟨hw, hd, hfield⟩ := hx.finite_state_bound hx.choose hF
  have hs : Real.sqrt 4 = 2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [hs] at hw hfield
  constructor
  · linarith
  constructor <;> linarith

-- The full-state constant is selected before all data in a critical L4 ball.
example {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ T : ℝ, 0 < T ∧ ∀ {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))),
      (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ 3 →
      ∀ {x : WaveState U V}
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x),
      (∀ u v, ρ ≤ x.1 u v 0) → ‖x‖ ≤ T ∧ ‖rectangleSource hU e Λ x hx.choose‖ ≤ T := by
  obtain ⟨T, hT, hb⟩ := exists_uniform_finite_state hU hU1 hV hUR hc hi hrc hr0 hφ hrd hρ
    (by norm_num : (0 : ℝ) ≤ 3)
  refine ⟨T, hT, ?_⟩
  intro f hf hfn x hx hlo
  exact ⟨(hb le_rfl hf hfn hx hlo).1, (hb le_rfl hf hfn hx hlo).2.1⟩

-- Translation restricts the measure and preserves one common a.e. set.
example (f : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 4))) :
    ‖intervalTranslateLp (a := 2) (U := 1) (by norm_num) (by norm_num) f‖ ≤ ‖f‖ ∧
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      intervalTranslateLp (a := 2) (U := 1) (by norm_num) (by norm_num) f t = f (2 + t) :=
  ⟨intervalTranslateLp_norm_le _ _ _, intervalTranslateLp_ae _ _ _⟩

-- The primitive on a singleton window subtracts the value at its translated origin.
example (f : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 4))) :
    horizontalPrimitive (le_refl (0 : ℝ))
      (intervalTranslateLp (a := 3) (U := 0) (by norm_num) (by norm_num) f) ⟨0, le_rfl, le_rfl⟩ = 0 := by
  rw [horizontalPrimitive_translate (by norm_num) (le_refl (0 : ℝ)) (by norm_num) (by norm_num)]
  exact sub_self _

-- A nonzero shift gives the length-one integral, rather than the integral from zero to three.
example : continuousPrimitive (by norm_num : (0 : ℝ) ≤ 1)
    ((ContinuousMap.const (Icc (0 : ℝ) 4) (5 : ℝ)).comp
      (intervalTranslate (a := 2) (U := 1) (by norm_num) (by norm_num))) ⟨1, by norm_num⟩ = 5 := by
  rw [continuousPrimitive_translate (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [continuousPrimitive, intervalExtension, intervalTranslate]

-- Both coordinates shift, and neither the state nor any induced data budget grows.
example (x : WaveState 4 5) :
    let y := waveTranslate (a := 1) (U := 2) (b := 2) (V := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) x
    ‖y‖ ≤ ‖x‖ ∧
      ‖(ContinuousMap.evalCLM ℝ (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1)).compLpL 2
        (volume.restrict (Icc (0 : ℝ) 2)) y.2.2‖ ≤ ‖x‖ := by
  have hb := waveTranslate_norm_le (a := 1) (U := 2) (b := 2) (V := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) x
  exact ⟨hb, ((wave_trace_norm_le (by norm_num) (by norm_num) _).2.2).trans hb⟩

-- Uniqueness needs no membership in a contraction ball around a chosen seed.
example (e Λ : ℝ) : ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
    ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), U ≤ d → V ≤ d →
    ∀ (z : C(Icc 0 U, WaveVector)) (v : C(Icc 0 V, WaveVector))
      (u : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x y : WaveState U V),
      IsWaveIntegral hU hV e Λ z v u x → IsWaveIntegral hU hV e Λ z v u y →
      (∀ s t, 1 ≤ x.1 s t 0) → (∀ s t, 1 ≤ y.1 s t 0) → ‖x‖ ≤ 7 → ‖y‖ ≤ 7 → x = y :=
  exists_local_wave_uniqueness e Λ 1 7 (by norm_num)

-- A translated window may meet the outer endpoint and have zero longitudinal length.
example {e Λ : ℝ} {z : C(Icc (0 : ℝ) 2, WaveVector)} {v : C(Icc (0 : ℝ) 3, WaveVector)}
    {u : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 2))} {x : WaveState 2 3}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) e Λ z v u x) :
    let y := waveTranslate (a := 1) (U := 1) (b := 3) (V := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) x
    let v₀ : Icc (0 : ℝ) 0 := ⟨0, le_rfl, le_rfl⟩
    IsWaveIntegral (by norm_num) le_rfl e Λ
      (ContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) 1) (ContinuousMap.evalCLM ℝ v₀) y.1)
      (y.2.1 ⟨0, by norm_num⟩)
      ((ContinuousMap.evalCLM ℝ v₀).compLpL 2 (volume.restrict (Icc (0 : ℝ) 1)) y.2.2) y :=
  hx.translate (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Restrict a constructed nonzero-scalar solution in both coordinates, retaining primitive compatibility.
example : ∃ d : ℝ, ∃ hd : 0 < d, ∃ x : WaveState d d,
    x.1 ⟨d, hd.le, le_rfl⟩ ⟨0, le_rfl, hd.le⟩ 1 = d ∧
    let he : 0 ≤ d / 2 := (half_pos hd).le
    let hend : d / 2 + d / 2 ≤ d := by linarith
    let y := waveTranslate he hend he hend x
    let u₀ : Icc 0 (d / 2) := ⟨0, le_rfl, he⟩
    let v₀ : Icc 0 (d / 2) := ⟨0, le_rfl, he⟩
    let z := ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 (d / 2)) (ContinuousMap.evalCLM ℝ v₀) y.1
    let u := (ContinuousMap.evalCLM ℝ v₀).compLpL 2 (volume.restrict (Icc 0 (d / 2))) y.2.2
    IsWaveIntegral he he 0 0 z (y.2.1 u₀) u y ∧
      z = ContinuousMap.const _ (y.1 u₀ v₀) + horizontalPrimitive he u := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨d, hd, hdR, _hd1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 1 zero_le_one
  let hf : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d)) := memLp_const 1
  have hnorm : (eLpNorm (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d))).toReal ≤ 1 := by
    by_cases hm : volume.restrict (Icc (0 : ℝ) d) = 0
    · simp [hm]
    · simp [eLpNorm_const (1 : ℝ) (by norm_num : (∞ : ℝ≥0∞) ≠ 0) hm]
  obtain ⟨x, hx, htraces⟩ := hsolve hd.le hd.le hdR le_rfl le_rfl le_top hf hnorm
  refine ⟨d, hd, x, ?_, ?_⟩
  · rw [htraces.1 ⟨d, hd.le, le_rfl⟩]
    simp [incomingPhi, horizonPhi]
  · exact ⟨hx.translate (half_pos hd).le (half_pos hd).le (half_pos hd).le (by linarith)
        (half_pos hd).le (by linarith),
      hx.translated_incoming_primitive rfl (half_pos hd).le (half_pos hd).le
        (half_pos hd).le (by linarith) (half_pos hd).le (by linarith)⟩

-- The translated second section retains its nonzero corner and its own slope.
example :
    let f : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun t => 2 + t, by fun_prop⟩
    let g : C(Icc (0 : ℝ) 2, ℝ) := ⟨fun t => 3 + 2 * t, by fun_prop⟩
    intervalSplice (by norm_num) (by norm_num) f g
      (intervalTranslate (by norm_num : (0 : ℝ) ≤ 1) le_rfl ⟨2, by norm_num⟩) = 7 := by
  dsimp only
  rw [intervalSplice_right]
  norm_num

-- Unmatched constants do not give false agreement with the second section.
example : intervalSplice (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2)
    (ContinuousMap.const _ (2 : ℝ)) (ContinuousMap.const _ 5) = ContinuousMap.const _ 2 :=
  intervalSplice_const _ _ _ _

-- The primitive includes the first section's integral after crossing the join.
example : continuousPrimitive (by norm_num : (0 : ℝ) ≤ 1 + 2)
    (intervalSplice (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2)
      (ContinuousMap.const _ (5 : ℝ)) (ContinuousMap.const _ 5))
    (intervalTranslate (by norm_num : (0 : ℝ) ≤ 1) le_rfl ⟨2, by norm_num⟩) = 15 := by
  rw [continuousPrimitive_splice (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2)
    (ContinuousMap.const _ (5 : ℝ)) (ContinuousMap.const _ 5) (by rfl), intervalSplice_right]
  norm_num [continuousPrimitive, intervalExtension]

-- A zero-length second section contributes no new values or primitive increment.
example (f : C(Icc (0 : ℝ) 1, ℝ)) (g : C(Icc (0 : ℝ) 0, ℝ)) :
    intervalSplice (by norm_num : (0 : ℝ) ≤ 1) le_rfl f g
      (intervalTranslate (by norm_num : (0 : ℝ) ≤ 1) le_rfl ⟨0, le_rfl, le_rfl⟩) = f ⟨1, by norm_num⟩ := by
  rw [intervalSplice_right]
  exact add_sub_cancel_right _ _

-- Equality of vector-valued L2 classes uses one common exceptional set in u.
example (f : Lp C(Icc (0 : ℝ) 1, WaveVector) 2 (volume.restrict (Icc (0 : ℝ) 3)))
    (g : Lp C(Icc (0 : ℝ) 2, WaveVector) 2 (volume.restrict (Icc (0 : ℝ) 3)))
    (hm : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 3), f u ⟨1, by norm_num⟩ = g u ⟨0, by norm_num⟩) :
    verticalPrimitive (by norm_num : (0 : ℝ) ≤ 1 + 2)
      (intervalSpliceLp (by norm_num) (by norm_num) f g) =
      intervalSpliceLp (by norm_num) (by norm_num)
        (verticalPrimitive (by norm_num) f) (verticalPrimitive (by norm_num) g) :=
  verticalPrimitive_splice _ _ f g hm

-- The uniform width is selected before the solutions; the w trace is not a premise.
example (e Λ : ℝ) : ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
    ∀ {U V W : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W), U ≤ d →
    ∀ (zx zy : C(Icc 0 U, WaveVector)) (vx : C(Icc 0 V, WaveVector)) (vy : C(Icc 0 W, WaveVector))
      (ux uy : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x : WaveState U V) (y : WaveState U W),
      IsWaveIntegral hU hV e Λ zx vx ux x → IsWaveIntegral hU hW e Λ zy vy uy y →
      (∀ u v, 1 ≤ x.1 u v 0) → (∀ u v, 1 ≤ y.1 u v 0) → ‖x‖ ≤ 7 → ‖y‖ ≤ 7 →
      (∀ u, x.1 u ⟨V, hV, le_rfl⟩ = y.1 u ⟨0, le_rfl, hW⟩) →
      (∀ᵐ u ∂volume.restrict (Icc 0 U), x.2.2 u ⟨V, hV, le_rfl⟩ = y.2.2 u ⟨0, le_rfl, hW⟩) →
      vx ⟨V, hV, le_rfl⟩ = vy ⟨0, le_rfl, hW⟩ →
    IsWaveIntegral hU (add_nonneg hV hW) e Λ zx (intervalSplice hV hW vx vy) ux (waveSplice hV hW x y) :=
  exists_vertical_pasting_width e Λ 1 7 (by norm_num)

-- Split and rejoin a constructed nonzero-scalar solution on two positive-height rectangles.
example : ∃ d : ℝ, ∃ hd : 0 < d, ∃ x : WaveState d (d / 2 + d / 2),
    x.1 ⟨d, hd.le, le_rfl⟩ ⟨0, le_rfl, by linarith⟩ 1 = d ∧
    let he : 0 ≤ d / 2 := (half_pos hd).le
    let l := waveTranslate (a := 0) (U := d) (b := 0) (V := d / 2)
      le_rfl (by linarith) le_rfl (by linarith) x
    let r := waveTranslate (a := 0) (U := d) (b := d / 2) (V := d / 2)
      le_rfl (by linarith) he le_rfl x
    let s := waveSplice he he l r
    (∃ z v u, IsWaveIntegral hd.le (add_nonneg he he) 0 0 z v u s) ∧
      waveTranslate (a := 0) (U := d) (b := 0) (V := d / 2) le_rfl (by linarith)
        le_rfl (by linarith) s = l ∧
      waveTranslate (a := 0) (U := d) (b := d / 2) (V := d / 2) le_rfl (by linarith) he le_rfl s = r := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨d, hd, hdR, _hd1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 1 zero_le_one
  let hf : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d)) := memLp_const 1
  have hnorm : (eLpNorm (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d))).toReal ≤ 1 := by
    by_cases hm : volume.restrict (Icc (0 : ℝ) d) = 0
    · simp [hm]
    · simp [eLpNorm_const (1 : ℝ) (by norm_num : (∞ : ℝ≥0∞) ≠ 0) hm]
  have he : 0 ≤ d / 2 := (half_pos hd).le
  obtain ⟨x, hx, htraces⟩ := hsolve hd.le (add_nonneg he he) hdR le_rfl (by linarith) le_top hf hnorm
  refine ⟨d, hd, x, ?_, ?_⟩
  · rw [htraces.1 ⟨d, hd.le, le_rfl⟩]
    simp [incomingPhi, horizonPhi]
  · let l := waveTranslate (a := 0) (U := d) (b := 0) (V := d / 2)
      le_rfl (show 0 + d ≤ d by linarith) le_rfl (show 0 + d / 2 ≤ d / 2 + d / 2 by linarith) x
    let r := waveTranslate (a := 0) (U := d) (b := d / 2) (V := d / 2)
      le_rfl (show 0 + d ≤ d by linarith) he le_rfl x
    have hl := hx.translate hd.le he (a := 0) le_rfl (by linarith) (b := 0) le_rfl (by linarith)
    have hr := hx.translate hd.le he (a := 0) le_rfl (by linarith) he (le_refl (d / 2 + d / 2))
    have hv : intervalTranslate (a := 0) le_rfl (show 0 + d / 2 ≤ d / 2 + d / 2 by linarith) ⟨d / 2, he, le_rfl⟩ =
        intervalTranslate he (le_refl (d / 2 + d / 2)) ⟨0, le_rfl, he⟩ := Subtype.ext (by simp [intervalTranslate])
    have hz (u : Icc 0 d) : l.1 u ⟨d / 2, he, le_rfl⟩ = r.1 u ⟨0, le_rfl, he⟩ := by
      change x.1 _ (intervalTranslate (a := 0) le_rfl (by linarith) _) = x.1 _ (intervalTranslate he le_rfl _)
      rw [hv]
    have hw (u : Icc 0 d) : l.2.1 u ⟨d / 2, he, le_rfl⟩ = r.2.1 u ⟨0, le_rfl, he⟩ := by
      change x.2.1 _ (intervalTranslate (a := 0) le_rfl (by linarith) _) = x.2.1 _ (intervalTranslate he le_rfl _)
      rw [hv]
    have hu : ∀ᵐ u ∂volume.restrict (Icc 0 d), l.2.2 u ⟨d / 2, he, le_rfl⟩ = r.2.2 u ⟨0, le_rfl, he⟩ := by
      filter_upwards [transverseTranslate_ae (a := 0) (U := d) (b := 0) (V := d / 2) le_rfl (by linarith)
        le_rfl (by linarith) x.2.2, transverseTranslate_ae (a := 0) (U := d) (V := d / 2)
        le_rfl (by linarith) he le_rfl x.2.2] with u hl hr
      change transverseTranslate (a := 0) (U := d) (b := 0) (V := d / 2) le_rfl (by linarith)
        le_rfl (by linarith) x.2.2 u _ = transverseTranslate (a := 0) (U := d) (V := d / 2)
        le_rfl (by linarith) he le_rfl x.2.2 u _
      rw [hl, hr]
      change x.2.2 (0 + u) (intervalTranslate (a := 0) le_rfl (by linarith) _) =
        x.2.2 (0 + u) (intervalTranslate he le_rfl _)
      rw [hv]
    exact ⟨⟨_, _, _, hl.splice hr hz hw hu⟩, waveSplice_restrict_left he he l r,
      waveSplice_restrict_right he he l r hz hw hu⟩

-- A jump from 2 to 5 is allowed in L2; its primitive accumulates both lengths.
example : horizontalPrimitive (by norm_num : (0 : ℝ) ≤ 1 + 2)
    (intervalJoinLp (by norm_num : (0 : ℝ) ≤ 2)
      (intervalToLp (by norm_num : (0 : ℝ) ≤ 1) 2 (ContinuousMap.const _ (2 : ℝ)))
      (intervalToLp (by norm_num : (0 : ℝ) ≤ 2) 2 (ContinuousMap.const _ (5 : ℝ))))
    (intervalTranslate (by norm_num : (0 : ℝ) ≤ 1) le_rfl ⟨2, by norm_num⟩) = 12 := by
  rw [horizontalPrimitive_join (by norm_num) (by norm_num), horizontalPrimitive_intervalToLp,
    horizontalPrimitive_intervalToLp, intervalSplice_right]
  norm_num [continuousPrimitive, intervalExtension]

-- Restriction recovers both vector-valued L2 classes without any seam-value premise.
example (f : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (g : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 2))) :
    intervalTranslateLp (a := 0) (U := 1) le_rfl (by norm_num)
      (intervalJoinLp (by norm_num : (0 : ℝ) ≤ 2) f g) = f ∧
    intervalTranslateLp (a := 1) (U := 2) (by norm_num) le_rfl
      (intervalJoinLp (by norm_num : (0 : ℝ) ≤ 2) f g) = g :=
  ⟨intervalJoinLp_restrict_left _ f g, intervalJoinLp_restrict_right (by norm_num) _ f g⟩

-- A zero-width first interval leaves the second L2 class unchanged after restriction.
example (f : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 0)))
    (g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 2))) :
    intervalTranslateLp (a := 0) (U := 2) le_rfl le_rfl
      (intervalJoinLp (by norm_num : (0 : ℝ) ≤ 2) f g) = g :=
  intervalJoinLp_restrict_right le_rfl _ f g

-- Primitive-compatible incoming data retain the first corner and the joined L2 derivative.
example (f : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 1)))
    (g : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 2))) :
    intervalSplice (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2)
      (ContinuousMap.const _ ![2, 3, 4] + horizontalPrimitive (by norm_num) f)
      (ContinuousMap.const _ ![5, 6, 7] + horizontalPrimitive (by norm_num) g) =
    ContinuousMap.const _ ![2, 3, 4] + horizontalPrimitive (by norm_num)
      (intervalJoinLp (by norm_num : (0 : ℝ) ≤ 2) f g) :=
  joined_incoming_primitive (by norm_num) (by norm_num) rfl rfl

-- Pasting itself has no small-side condition and requires only characteristic-data compatibility.
example {e Λ : ℝ} {zx : C(Icc (0 : ℝ) 1, WaveVector)} {zy : C(Icc (0 : ℝ) 2, WaveVector)}
    {vx vy : C(Icc (0 : ℝ) 3, WaveVector)}
    {ux : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 1))}
    {uy : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 2))} {x : WaveState 1 3} {y : WaveState 2 3}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) e Λ zx vx ux x)
    (hy : IsWaveIntegral (by norm_num) (by norm_num) e Λ zy vy uy y)
    (hv : vy = x.2.1 ⟨1, by norm_num⟩) (hc : zx ⟨1, by norm_num⟩ = zy ⟨0, by norm_num⟩) :
    IsWaveIntegral (by norm_num) (by norm_num) e Λ (intervalSplice (by norm_num) (by norm_num) zx zy) vx
      (intervalJoinLp (by norm_num) ux uy) (waveJoin (by norm_num) (by norm_num) x y) :=
  hx.join_of_data hy hv hc

-- A fixed data budget constructs a new positive-width patch, before choosing the old solution.
example (e Λ : ℝ) : ∃ d : ℝ, ∃ hd : 0 < d, d ≤ 1 ∧
    ∀ {U : ℝ} (hU : 0 ≤ U) (zx : C(Icc 0 U, WaveVector)) (vx : C(Icc 0 (d / 2), WaveVector))
      (ux : Lp WaveVector 2 (volume.restrict (Icc 0 U))) (x : WaveState U (d / 2)),
      IsWaveIntegral hU (half_pos hd).le e Λ zx vx ux x → ‖x‖ ≤ 7 →
    ∀ (zy : C(Icc 0 (d / 2), WaveVector)) (uy : Lp WaveVector 2 (volume.restrict (Icc 0 (d / 2)))),
      (∀ u, 1 ≤ zy u 0) → ‖zy‖ ≤ 7 → ‖uy‖ ≤ 3 → zx ⟨U, hU, le_rfl⟩ = zy ⟨0, le_rfl, (half_pos hd).le⟩ →
    ∃ y : WaveState (d / 2) (d / 2),
      IsWaveIntegral (half_pos hd).le (half_pos hd).le e Λ zy (x.2.1 ⟨U, hU, le_rfl⟩) uy y ∧
      IsWaveIntegral (add_nonneg hU (half_pos hd).le) (half_pos hd).le e Λ
        (intervalSplice hU (half_pos hd).le zx zy) vx (intervalJoinLp (half_pos hd).le ux uy)
        (waveJoin hU (half_pos hd).le x y) ∧ ∀ u v, (1 / 2 : ℝ) ≤ y.1 u v 0 := by
  obtain ⟨d, hd, hd1, hext⟩ := exists_horizontal_wave_extension e Λ 1 7 3 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨d, hd, hd1, ?_⟩
  intro U hU zx vx ux x hx hxn zy uy hzr hzn hun hc
  obtain ⟨y, hy, hxy, _hleft, hlo⟩ := hext hU (half_pos hd).le (half_pos hd).le (by linarith) (by linarith)
    zx vx ux x hx hxn zy uy hzr hzn hun hc
  exact ⟨y, hy, hxy, hlo⟩

-- Rejoin positive-width pieces of a constructed physical solution with nonzero scalar data.
example : ∃ d : ℝ, ∃ hd : 0 < d, ∃ x : WaveState (d / 2 + d / 2) d,
    x.1 ⟨d / 2 + d / 2, by linarith, le_rfl⟩ ⟨0, le_rfl, hd.le⟩ 1 = d ∧
    let he : 0 ≤ d / 2 := (half_pos hd).le
    let l := waveTranslate (a := 0) (U := d / 2) (b := 0) (V := d)
      le_rfl (by linarith) le_rfl (by linarith) x
    let r := waveTranslate (a := d / 2) (U := d / 2) (b := 0) (V := d)
      he le_rfl le_rfl (by linarith) x
    let s := waveJoin he he l r
    (∃ z v u, IsWaveIntegral (add_nonneg he he) hd.le 0 0 z v u s) ∧
      waveTranslate (a := 0) (U := d / 2) (b := 0) (V := d) le_rfl (by linarith)
        le_rfl (by linarith) s = l ∧
      waveTranslate (a := d / 2) (U := d / 2) (b := 0) (V := d) he le_rfl le_rfl (by linarith) s = r := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨d, hd, hdR, _hd1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 1 zero_le_one
  let hf : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 (d / 2 + d / 2))) := memLp_const 1
  have hnorm : (eLpNorm (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 (d / 2 + d / 2)))).toReal ≤ 1 := by
    rw [show d / 2 + d / 2 = d by ring]
    by_cases hm : volume.restrict (Icc (0 : ℝ) d) = 0
    · simp [hm]
    · simp [eLpNorm_const (1 : ℝ) (by norm_num : (∞ : ℝ≥0∞) ≠ 0) hm]
  have he : 0 ≤ d / 2 := (half_pos hd).le
  obtain ⟨x, hx, htraces⟩ := hsolve (add_nonneg he he) hd.le (by linarith : d / 2 + d / 2 < 2)
    (by linarith) le_rfl le_top hf hnorm
  refine ⟨d, hd, x, ?_, ?_⟩
  · rw [htraces.1 ⟨d / 2 + d / 2, add_nonneg he he, le_rfl⟩]
    simp [incomingPhi, horizonPhi]
  · let l := waveTranslate (a := 0) (U := d / 2) (b := 0) (V := d)
      le_rfl (show 0 + d / 2 ≤ d / 2 + d / 2 by linarith) le_rfl (show 0 + d ≤ d by linarith) x
    let r := waveTranslate (a := d / 2) (U := d / 2) (b := 0) (V := d)
      he le_rfl le_rfl (show 0 + d ≤ d by linarith) x
    have hl := hx.translate he hd.le (a := 0) le_rfl (by linarith) (b := 0) le_rfl (by linarith)
    have hr := hx.translate he hd.le he (le_refl (d / 2 + d / 2)) (b := 0) le_rfl (by linarith)
    have hu : intervalTranslate (a := 0) le_rfl (show 0 + d / 2 ≤ d / 2 + d / 2 by linarith) ⟨d / 2, he, le_rfl⟩ =
        intervalTranslate he (le_refl (d / 2 + d / 2)) ⟨0, le_rfl, he⟩ := Subtype.ext (by simp [intervalTranslate])
    have hz : l.1 ⟨d / 2, he, le_rfl⟩ = r.1 ⟨0, le_rfl, he⟩ := by
      apply ContinuousMap.ext
      intro v
      change x.1 (intervalTranslate (a := 0) le_rfl (by linarith) _) _ = x.1 (intervalTranslate he le_rfl _) _
      rw [hu]
    have hw : l.2.1 ⟨d / 2, he, le_rfl⟩ = r.2.1 ⟨0, le_rfl, he⟩ := by
      apply ContinuousMap.ext
      intro v
      change x.2.1 (intervalTranslate (a := 0) le_rfl (by linarith) _) _ = x.2.1 (intervalTranslate he le_rfl _) _
      rw [hu]
    exact ⟨⟨_, _, _, hl.join hr hz hw⟩, waveJoin_restrict_left he he l r,
      waveJoin_restrict_right he he l r hz hw⟩

-- The horizon velocity bound also restricts to a singleton time interval.
example {M e Λ : ℝ} {h r : ℝ → ℝ} (hc : Continuous h)
    (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t)) (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) :
    ‖horizonWaveVelocity M e Λ 0 hc hi hrc hr0‖ ≤ ‖horizonWaveVelocity M e Λ 5 hc hi hrc hr0‖ :=
  horizonWaveVelocity_norm_mono hc hi hrc hr0 (by norm_num)

section UniformSubrectangles

variable {M e Λ : ℝ} {h r : ℝ → ℝ}
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
  {ρ : ℝ} (hρ : 0 < ρ)

-- Geometry constants precede both side lengths; geometry needs no U <= 1 hypothesis.
example : ∃ R A : ℝ, 0 < R ∧ 0 ≤ A ∧
    ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V), V ≤ 4 → ∀ hUR : U < r 0,
    ∀ {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V},
      IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x →
      (∀ u v, ρ ≤ x.1 u v 0) → ∀ u v, x.1 u v 0 ≤ R ∧ |x.2.1 u v 0| ≤ A := by
  obtain ⟨R, A, _C, hR, hA, _hC, hb⟩ :=
    exists_uniform_finite_geometry_on_subrectangles (Vmax := 4) hc hi hrc hr0 hφ hrd hρ
  refine ⟨R, A, hR, hA, ?_⟩
  intro U V hU hV hV4 hUR f hf x hx hlo u v
  have hh := hb hU hV hV4 hUR le_rfl hf hx hlo u v
  exact ⟨hh.1, hh.2.2.1⟩

-- At p=infinity one scalar bound covers every prefix and every terminal time up to four.
example (hrp : 0 < r 0) : ∃ B : ℝ, 0 < B ∧
    ∀ {U V : ℝ} (hU : 0 ≤ U) (_hU1 : U ≤ 1) (hV : 0 ≤ V), V ≤ 4 → ∀ hUR : U < r 0,
    ∀ {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))),
      (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ≤ 2 → ∀ {x : WaveState U V},
      IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x →
      (∀ u v, ρ ≤ x.1 u v 0) →
      (∀ u : Icc 0 U, ‖waveCoordinateField 1 x.2.1 u‖ ≤ B) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, |x.2.2 u v 1| ≤ B * (|f u| + 1) := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_finite_scalar_on_subrectangles (by norm_num : (0 : ℝ) ≤ 4)
    hrp hc hi hrc hr0 hφ hrd hρ (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨B, hB, ?_⟩
  intro U V hU hU1 hV hV4 hUR f hf hfn x hx hlo
  have hh := hb hU hU1 hV hV4 hUR le_top hf hfn hx hlo
  exact ⟨hh.1, hh.2.1⟩

-- Positive conformal lower bounds are common to all critical L4 data and side lengths.
example (hrp : 0 < r 0) : ∃ w : ℝ, 0 < w ∧
    ∀ {U V : ℝ} (hU : 0 ≤ U) (_hU1 : U ≤ 1) (hV : 0 ≤ V), V ≤ 4 → ∀ hUR : U < r 0,
    ∀ {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))),
      (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ 2 → ∀ {x : WaveState U V},
      IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x →
      (∀ u v, ρ ≤ x.1 u v 0) → ∀ u v, w ≤ Real.exp (x.1 u v 2) := by
  obtain ⟨_k, w, _hk, hw, hb⟩ := exists_uniform_finite_kappa_on_subrectangles (by norm_num : (0 : ℝ) ≤ 4)
    hrp hc hi hrc hr0 hφ hrd hρ (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨w, hw, ?_⟩
  intro U V hU hU1 hV hV4 hUR f hf hfn x hx hlo u v
  exact (hb hU hU1 hV hV4 hUR le_rfl hf hfn hx hlo u v).2

-- The full bound is chosen before dimensions, exponent, input and actual solution.
example (hrp : 0 < r 0) : ∃ T : ℝ, 0 < T ∧
    ∀ {U V : ℝ} (hU : 0 ≤ U) (_hU1 : U ≤ 1) (hV : 0 ≤ V), V ≤ 4 → ∀ hUR : U < r 0,
    ∀ {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))),
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ 2 →
    ∀ {x : WaveState U V}
      (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
      (∀ u v, ρ ≤ x.1 u v 0) → ‖x‖ ≤ T ∧ ‖rectangleSource hU e Λ x hx.choose‖ ≤ T ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        |x.2.2 u v 2| ≤ r 0 * (f u) ^ 2 + T * (|f u| + 1) :=
  exists_uniform_finite_state_on_subrectangles (by norm_num : (0 : ℝ) ≤ 4) hrp hc hi hrc hr0 hφ hrd hρ (by norm_num)

end UniformSubrectangles

-- Prefix budgets use the restricted measure for both critical and bounded data.
example {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 2))) :
    (eLpNorm f 4 (volume.restrict (Icc (0 : ℝ) (1 / 2)))).toReal ≤
      (eLpNorm f 4 (volume.restrict (Icc (0 : ℝ) 2))).toReal :=
  scalar_prefix_norm_le (by norm_num) hf

example {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc (0 : ℝ) 2))) :
    (eLpNorm f ∞ (volume.restrict (Icc (0 : ℝ) 1))).toReal ≤
      (eLpNorm f ∞ (volume.restrict (Icc (0 : ℝ) 2))).toReal :=
  scalar_prefix_norm_le (by norm_num) hf

-- A zero-width prefix retains the original physical corner, including log(4).
example {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 2))) :
    ((incomingWaveCurve (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 3) le_rfl hf 7).comp
      (intervalTranslate (a := 0) (U := 0) le_rfl (by norm_num))) ⟨0, le_rfl, le_rfl⟩ = ![3, 7, Real.log 4] := by
  let hf0 := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)
  rw [incomingWaveCurve_prefix (by norm_num) le_rfl (by norm_num) (by norm_num) le_rfl hf hf0,
    incomingWaveCurve_apply]
  simp [incomingRadius, incomingPhi, incomingLogOmega]

-- The original physical data remain identifiable after restricting both dimensions.
example {M e Λ : ℝ} {h r : ℝ → ℝ} (hR : 2 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc (0 : ℝ) 2))) {x : WaveState 2 3}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) e Λ
      (incomingWaveCurve (by norm_num) hR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ 3 hc hi hrc hr0) (incomingWaveVelocity hR le_top hf) x) :
    let hf1 := hf.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (by norm_num : (1 : ℝ) ≤ 2)) le_rfl)
    IsWaveIntegral (by norm_num) (le_refl (0 : ℝ)) e Λ
      (incomingWaveCurve (by norm_num) (by linarith : (1 : ℝ) < r 0) le_top hf1 (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ 0 hc hi hrc hr0) (incomingWaveVelocity (by linarith : (1 : ℝ) < r 0) le_top hf1)
      (waveTranslate (a := 0) (U := 1) (b := 0) (V := 0) le_rfl (by norm_num) le_rfl (by norm_num) x) :=
  IsWaveIntegral.horizon_prefix (by norm_num) (by norm_num) hR (by norm_num) le_rfl
    (by norm_num) (by norm_num) hc hi hrc hr0 le_top hf hx

-- Reconstructing a continuous section also accepts a zero-height upper piece.
example (f : C(Icc (0 : ℝ) (2 + 0), WaveVector)) :
    intervalSplice (by norm_num : (0 : ℝ) ≤ 2) le_rfl
      (f.comp (intervalTranslate (a := 0) (U := 2) le_rfl (by norm_num)))
      (f.comp (intervalTranslate (a := 2) (U := 0) (by norm_num) le_rfl)) = f :=
  intervalSplice_reconstruct (by norm_num) le_rfl f

-- Construct a missing corner from three nonzero-scalar pieces, rather than assuming the fourth.
example : ∃ w : ℝ, ∃ hw : 0 < w, ∃ s : WaveState (w + w) (w + w),
    (∃ z v u, IsWaveIntegral (add_nonneg hw.le hw.le) (add_nonneg hw.le hw.le) 0 0 z v u s) ∧
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ u v, ρ ≤ s.1 u v 0) ∧
    s.1 ⟨w, hw.le, by linarith⟩ ⟨0, le_rfl, add_nonneg hw.le hw.le⟩ 1 = w := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨d, hd, hdR, _hd1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 1 zero_le_one
  let hf : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d)) := memLp_const 1
  have hnorm : (eLpNorm (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 d))).toReal ≤ 1 := by
    by_cases hm : volume.restrict (Icc (0 : ℝ) d) = 0
    · simp [hm]
    · simp [eLpNorm_const (1 : ℝ) (by norm_num : (∞ : ℝ≥0∞) ≠ 0) hm]
  obtain ⟨X, hX, htraces⟩ := hsolve hd.le hd.le hdR le_rfl le_rfl le_top hf hnorm
  have hrcX : Continuous (fun q : Icc 0 d × Icc 0 d => X.1 q.1 q.2 0) := by fun_prop
  obtain ⟨q, _hq, hmin⟩ := isCompact_univ.exists_isMinOn
    ⟨(⟨0, le_rfl, hd.le⟩, ⟨0, le_rfl, hd.le⟩), mem_univ _⟩ hrcX.continuousOn
  let ρ := X.1 q.1 q.2 0
  have hρ : 0 < ρ := hX.incoming_radius_pos hd.le hd.le hdR le_top hf q.1 q.2
  have hlo (u v : Icc 0 d) : ρ ≤ X.1 u v 0 := hmin (mem_univ (u, v))
  obtain ⟨d₀, hd₀, _hd₀1, hext⟩ := exists_corner_wave_extension 0 0 ρ ‖X‖ hρ (norm_nonneg X)
  let w := min (d / 4) (d₀ / 2)
  have hw : 0 < w := lt_min (by positivity) (half_pos hd₀)
  have hw4 : w ≤ d / 4 := min_le_left _ _
  have hwD : w ≤ d₀ := (min_le_right _ _).trans (half_le_self hd₀.le)
  have hww : w + w ≤ d := by linarith
  have hwd : w ≤ d := by linarith
  let x := waveTranslate (a := 0) (U := w) (b := 0) (V := w + w) le_rfl (show 0 + w ≤ d by linarith)
    le_rfl (show 0 + (w + w) ≤ d by linarith) X
  let y := waveTranslate (a := w) (U := w) (b := 0) (V := w) hw.le hww le_rfl (show 0 + w ≤ d by linarith) X
  have hx := hX.translate hw.le (add_nonneg hw.le hw.le) (a := 0) le_rfl (by linarith) (b := 0) le_rfl (by linarith)
  have hy := hX.translate hw.le hw.le hw.le hww (b := 0) le_rfl (by linarith)
  have hu : intervalTranslate (a := 0) le_rfl (show 0 + w ≤ d by linarith) ⟨w, hw.le, le_rfl⟩ =
      intervalTranslate hw.le hww ⟨0, le_rfl, hw.le⟩ := Subtype.ext (by simp [intervalTranslate])
  have hv : y.2.1 ⟨0, le_rfl, hw.le⟩ = (x.2.1 ⟨w, hw.le, le_rfl⟩).comp
      (intervalTranslate (a := 0) le_rfl (show 0 + w ≤ w + w by linarith)) := by
    apply ContinuousMap.ext
    intro v
    change X.2.1 (intervalTranslate hw.le hww ⟨0, le_rfl, hw.le⟩) _ =
      X.2.1 (intervalTranslate (a := 0) le_rfl (show 0 + w ≤ d by linarith) ⟨w, hw.le, le_rfl⟩) _
    rw [hu]
    apply congrArg (X.2.1 (intervalTranslate hw.le hww ⟨0, le_rfl, hw.le⟩))
    exact Subtype.ext (by simp [intervalTranslate])
  have hcorner : x.1 ⟨w, hw.le, le_rfl⟩ ⟨0, le_rfl, add_nonneg hw.le hw.le⟩ =
      y.1 ⟨0, le_rfl, hw.le⟩ ⟨0, le_rfl, hw.le⟩ := by
    change X.1 (intervalTranslate (a := 0) le_rfl (show 0 + w ≤ d by linarith) ⟨w, hw.le, le_rfl⟩) _ =
      X.1 (intervalTranslate hw.le hww ⟨0, le_rfl, hw.le⟩) _
    rw [hu]
    apply congrArg (X.1 (intervalTranslate hw.le hww ⟨0, le_rfl, hw.le⟩))
    exact Subtype.ext (by simp [intervalTranslate])
  obtain ⟨z, _hz, _hbottom, _hzr, hjoin, _hleft, _hright, hrad⟩ := hext hw.le hw.le hw.le hw.le hwD hwD
    _ _ _ x _ _ _ y hx hy (waveTranslate_norm_le _ _ _ _ X) (waveTranslate_norm_le _ _ _ _ X)
      (fun u v => (half_le_self hρ.le).trans (hlo _ _)) (fun u v => hlo _ _) hv hcorner
  refine ⟨w, hw, waveJoin hw.le hw.le x z, ⟨_, _, _, hjoin⟩, ⟨ρ / 2, half_pos hρ, hrad⟩, ?_⟩
  have hu' : intervalTranslate (a := 0) le_rfl (show 0 + w ≤ w + w by linarith) ⟨w, hw.le, le_rfl⟩ =
      (⟨w, hw.le, by linarith⟩ : Icc 0 (w + w)) := Subtype.ext (zero_add _)
  rw [← hu']
  change intervalSplice hw.le hw.le x.1 z.1 _ _ 1 = w
  rw [intervalSplice_left]
  change X.1 (intervalTranslate (a := 0) le_rfl (show 0 + w ≤ d by linarith) ⟨w, hw.le, le_rfl⟩)
    (intervalTranslate (a := 0) le_rfl (show 0 + (w + w) ≤ d by linarith)
      ⟨0, le_rfl, add_nonneg hw.le hw.le⟩) 1 = w
  have hv0 : intervalTranslate (a := 0) le_rfl (show 0 + (w + w) ≤ d by linarith)
      ⟨0, le_rfl, add_nonneg hw.le hw.le⟩ = (⟨0, le_rfl, hd.le⟩ : Icc 0 d) := Subtype.ext (zero_add _)
  rw [hv0, htraces.1]
  simp [incomingPhi, horizonPhi, intervalTranslate]

example (f : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 2))) :
    intervalTranslateLp (a := 0) (U := 2) le_rfl (by norm_num) f = f := intervalTranslateLp_zero f

example {z z' : C(Icc (0 : ℝ) 1, WaveVector)} {v v' : C(Icc (0 : ℝ) 2, WaveVector)}
    {d d' : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 1))} {x : WaveState 1 2}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) 0 0 z v d x)
    (hx' : IsWaveIntegral (by norm_num) (by norm_num) 0 0 z' v' d' x) : z = z' ∧ v = v' ∧ d = d' :=
  hx.data_unique hx'

-- A height-zero lower trace still identifies the actual transverse L2 class.
example {z z' : C(Icc (0 : ℝ) 1, WaveVector)} {v : C(Icc (0 : ℝ) 2, WaveVector)}
    {v' : C(Icc (0 : ℝ) 0, WaveVector)} {d d' : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 1))}
    {x : WaveState 1 2} {y : WaveState 1 0}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) 0 0 z v d x)
    (hy : IsWaveIntegral (by norm_num) le_rfl 0 0 z' v' d' y)
    (hb : waveTranslate (a := 0) (U := 1) (b := 0) (V := 0) le_rfl (by norm_num) le_rfl (by norm_num) x = y) :
    IsWaveIntegral (by norm_num) (by norm_num) 0 0 z' v d' x :=
  hx.of_vertical_prefix le_rfl (by norm_num) hy hb

example (x : WaveState 5 6) :
    waveTranslate (a := 1) (U := 1) (b := 1) (V := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (waveTranslate (a := 1) (U := 3) (b := 2) (V := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x) =
    waveTranslate (a := 2) (U := 1) (b := 3) (V := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x := by
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num] using
    waveTranslate_comp (a := 1) (U := 3) (b := 2) (V := 3) (c := 1) (W := 1) (d := 1) (H := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) x

example {x y : WaveState (0 + 2) 1}
    (hl : waveTranslate (a := 0) (U := 0) (b := 0) (V := 1) le_rfl (by norm_num) le_rfl (by norm_num) x =
      waveTranslate (a := 0) (U := 0) (b := 0) (V := 1) le_rfl (by norm_num) le_rfl (by norm_num) y)
    (hr : waveTranslate (a := 0) (U := 2) (b := 0) (V := 1) le_rfl le_rfl le_rfl (by norm_num) x =
      waveTranslate (a := 0) (U := 2) (b := 0) (V := 1) le_rfl le_rfl le_rfl (by norm_num) y) : x = y :=
  waveTranslate_ext_horizontal le_rfl (by norm_num) hl hr

-- The final width is 1 even when the uniform local size d is smaller than 1.
example {M e Λ ρ J : ℝ} {h r : ℝ → ℝ} (hR : 1 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (hρ : 0 < ρ) (hJ : 0 ≤ J) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ {V H : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ H), H ≤ d → V + H ≤ 1 →
      ∀ {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 1))),
        (eLpNorm f 4 (volume.restrict (Icc (0 : ℝ) 1))).toReal ≤ J → ∀ {x : WaveState 1 V},
      IsWaveIntegral (by norm_num) hV e Λ (incomingWaveCurve (by norm_num) hR le_rfl hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hR le_rfl hf) x →
      (∀ u v, ρ ≤ x.1 u v 0) → ∃ y : WaveState 1 (V + H),
      IsWaveIntegral (by norm_num) (add_nonneg hV hH) e Λ
        (incomingWaveCurve (by norm_num) hR le_rfl hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ (V + H) hc hi hrc hr0) (incomingWaveVelocity hR le_rfl hf) y ∧
      waveTranslate (a := 0) (U := 1) (b := 0) (V := V) le_rfl (by norm_num) le_rfl (by linarith) y = x ∧
      ∀ u v, ρ / 2 ≤ y.1 u v 0 := by
  obtain ⟨d, hd, hd1, hext⟩ := exists_horizon_row_extension (Vmax := 1) zero_le_one (by linarith) hc hi hrc hr0 hφ hrd hρ hJ
  refine ⟨d, hd, hd1, ?_⟩
  intro V H hV hH hHd hVH f hf hfn x hx hrx
  exact hext zero_le_one hV hH le_rfl hHd hVH hR le_rfl hf hfn hx hrx

-- Start with nonzero scalar data and extend the entire original width by a positive time.
example : ∃ U H : ℝ, ∃ hU : 0 < U, ∃ hH : 0 < H, ∃ y : WaveState U (U + H),
    (∃ z v d, IsWaveIntegral hU.le (add_nonneg hU.le hH.le) 0 0 z v d y) ∧
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ u v, ρ ≤ y.1 u v 0) ∧
    y.1 ⟨U / 2, (half_pos hU).le, half_le_self hU.le⟩ ⟨0, le_rfl, add_nonneg hU.le hH.le⟩ 1 = U / 2 := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨U, hU, hUR, hU1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 1 zero_le_one
  let hf : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 U)) := memLp_const 1
  have hnorm : (eLpNorm (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 U))).toReal ≤ 1 := by
    by_cases hm : volume.restrict (Icc (0 : ℝ) U) = 0
    · simp [hm]
    · simp [eLpNorm_const (1 : ℝ) (by norm_num : (∞ : ℝ≥0∞) ≠ 0) hm]
  obtain ⟨X, hX, htraces⟩ := hsolve hU.le hU.le hUR le_rfl le_rfl le_top hf hnorm
  have hrcX : Continuous (fun q : Icc 0 U × Icc 0 U => X.1 q.1 q.2 0) := by fun_prop
  obtain ⟨q, _hq, hmin⟩ := isCompact_univ.exists_isMinOn
    ⟨(⟨0, le_rfl, hU.le⟩, ⟨0, le_rfl, hU.le⟩), mem_univ _⟩ hrcX.continuousOn
  let ρ := X.1 q.1 q.2 0
  have hρ : 0 < ρ := hX.incoming_radius_pos hU.le hU.le hUR le_top hf q.1 q.2
  have hex (V : ℝ) (hV : 0 ≤ V) (hVU : V < U) : ∃ x : WaveState U V,
      IsWaveIntegral hU.le hV 0 0 (incomingWaveCurve hU.le hUR le_top hf (horizonPhi (fun _ => 0) (fun _ => 2) 0))
        (horizonWaveVelocity 1 0 0 V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x ∧
      ∀ u v, ρ ≤ x.1 u v 0 := by
    have hs := hX.horizon_prefix hU.le hU.le hUR hU.le hV le_rfl hVU.le hc hi hrc hr0 le_top hf
    exact ⟨_, hs, fun u v => hmin (mem_univ (_, _))⟩
  obtain ⟨H, hH, y, hy, hr, hcompatible⟩ :=
    exists_horizon_continuation hU.le hU1 hU hUR hc hi hrc hr0 hφ hrd hρ zero_le_one le_top hf hnorm hex
  have hhalf := hX.horizon_prefix hU.le hU.le hUR hU.le (half_pos hU).le le_rfl (half_le_self hU.le)
    hc hi hrc hr0 le_top hf
  have hmatch := hcompatible (half_pos hU).le (half_lt_self hU) hhalf
  refine ⟨U, H, hU, hH, y, ⟨_, _, _, hy⟩, ⟨ρ / 2, half_pos hρ, hr⟩, ?_⟩
  have he := congrArg (fun s : WaveState U (U / 2) =>
    s.1 ⟨U / 2, (half_pos hU).le, half_le_self hU.le⟩ ⟨0, le_rfl, (half_pos hU).le⟩ 1) hmatch
  have hvY : intervalTranslate (a := 0) (U := U / 2) le_rfl (show 0 + U / 2 ≤ U + H by linarith)
      ⟨0, le_rfl, (half_pos hU).le⟩ = (⟨0, le_rfl, add_nonneg hU.le hH.le⟩ : Icc 0 (U + H)) := Subtype.ext (zero_add _)
  have hvX : intervalTranslate (a := 0) (U := U / 2) le_rfl (show 0 + U / 2 ≤ U by linarith)
      ⟨0, le_rfl, (half_pos hU).le⟩ = (⟨0, le_rfl, hU.le⟩ : Icc 0 U) := Subtype.ext (zero_add _)
  change y.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) _) _ 1 =
    X.1 (intervalTranslate (a := 0) le_rfl (show 0 + U ≤ U by simp) _) _ 1 at he
  simp only [intervalTranslate_zero, ContinuousMap.id_apply, hvY, hvX] at he
  rw [he, htraces.1]
  simp [incomingPhi, horizonPhi]

example {P : ℝ → Prop} (h0 : P 0)
    (hs : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b ≤ 5 → b ≤ 1 / 10 → P a → P (a + b)) : P 5 :=
  interval_subdivision_induction (by norm_num) (by norm_num) h0 hs

-- Both dimensions can exceed every small-cell size used by local uniqueness.
example {z : C(Icc (0 : ℝ) 2, WaveVector)} {v : C(Icc (0 : ℝ) 3, WaveVector)}
    {d : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 2))} {x y : WaveState 2 3}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) 0 0 z v d x)
    (hy : IsWaveIntegral (by norm_num) (by norm_num) 0 0 z v d y)
    (hrx : ∀ u v, 0 < x.1 u v 0) (hry : ∀ u v, 0 < y.1 u v 0) : x = y :=
  hx.unique_of_positive_radius hy hrx hry

-- No state-norm or positive-radius hypothesis is needed for the physical data.
example {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 2)))
    {v : C(Icc (0 : ℝ) 5, WaveVector)} {x y : WaveState 2 5}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) 0 0
      (incomingWaveCurve (by norm_num) (by norm_num : (2 : ℝ) < 3) le_rfl hf 7) v
      (incomingWaveVelocity (by norm_num : (2 : ℝ) < 3) le_rfl hf) x)
    (hy : IsWaveIntegral (by norm_num) (by norm_num) 0 0
      (incomingWaveCurve (by norm_num) (by norm_num : (2 : ℝ) < 3) le_rfl hf 7) v
      (incomingWaveVelocity (by norm_num : (2 : ℝ) < 3) le_rfl hf) y) : x = y :=
  hx.incoming_unique (by norm_num) (by norm_num) (by norm_num) le_rfl hf hy

example {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc (0 : ℝ) 0)))
    {v : C(Icc (0 : ℝ) 5, WaveVector)} {x y : WaveState 0 5}
    (hx : IsWaveIntegral le_rfl (by norm_num) 0 0
      (incomingWaveCurve le_rfl (by norm_num : (0 : ℝ) < 3) le_top hf 7) v
      (incomingWaveVelocity (by norm_num : (0 : ℝ) < 3) le_top hf) x)
    (hy : IsWaveIntegral le_rfl (by norm_num) 0 0
      (incomingWaveCurve le_rfl (by norm_num : (0 : ℝ) < 3) le_top hf 7) v
      (incomingWaveVelocity (by norm_num : (0 : ℝ) < 3) le_top hf) y) : x = y :=
  hx.incoming_unique le_rfl (by norm_num) (by norm_num) le_top hf hy

example {z : C(Icc (0 : ℝ) 2, WaveVector)} {v : C(Icc (0 : ℝ) 0, WaveVector)}
    {d : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 2))} {x y : WaveState 2 0}
    (hx : IsWaveIntegral (by norm_num) le_rfl 0 0 z v d x)
    (hy : IsWaveIntegral (by norm_num) le_rfl 0 0 z v d y)
    (hrx : ∀ u v, 0 < x.1 u v 0) (hry : ∀ u v, 0 < y.1 u v 0) : x = y :=
  hx.unique_of_positive_radius hy hrx hry

-- Horizontal translation keeps the shifted original data, without resetting the radius gauge.
example {z : C(Icc (0 : ℝ) 3, WaveVector)} {v : C(Icc (0 : ℝ) 4, WaveVector)}
    {d : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 3))} {x : WaveState 3 4}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) 0 0 z v d x) :
    IsWaveIntegral (by norm_num) (by norm_num) 0 0
      (z.comp (intervalTranslate (a := 1) (U := 2) (by norm_num) (by norm_num)))
      ((x.2.1 ⟨1, by norm_num, by norm_num⟩).comp (intervalTranslate (a := 0) (U := 2) le_rfl (by norm_num)))
      (intervalTranslateLp (a := 1) (U := 2) (by norm_num) (by norm_num) d)
      (waveTranslate (a := 1) (U := 2) (b := 0) (V := 2) (by norm_num) (by norm_num) le_rfl (by norm_num) x) :=
  hx.incoming_translate (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example {M e Λ : ℝ} {h r : ℝ → ℝ} (hR : 2 < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc (0 : ℝ) 2)))
    (hf1 : MemLp f ∞ (volume.restrict (Icc (0 : ℝ) 1))) {x : WaveState 2 3} {y : WaveState 1 2}
    (hx : IsWaveIntegral (by norm_num) (by norm_num) e Λ
      (incomingWaveCurve (by norm_num) hR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ 3 hc hi hrc hr0) (incomingWaveVelocity hR le_top hf) x)
    (hy : IsWaveIntegral (by norm_num) (by norm_num) e Λ
      (incomingWaveCurve (by norm_num) (by linarith : (1 : ℝ) < r 0) le_top hf1 (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ 2 hc hi hrc hr0) (incomingWaveVelocity (by linarith : (1 : ℝ) < r 0) le_top hf1) y) :
    waveTranslate (a := 0) (U := 1) (b := 0) (V := 2) le_rfl (by norm_num) le_rfl (by norm_num) x = y :=
  hx.horizon_prefix_unique (by norm_num) (by norm_num) hR (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hc hi hrc hr0 le_top hf hf1 hy

-- Nonzero charge and cosmological terms retain the mass normalization.
example : renormalizedMass 2 (-1) (-3 / 4) (Real.log 4) 1 1 = 2 / 3 := by
  norm_num [renormalizedMass, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

example {r ν l ell ψ e Λ : ℝ} (hr : r ≠ 0) (hν : ν ≠ 0) :
    -2 * r ^ 2 * l * Real.exp (-ell) * ψ ^ 2 =
      horizonFunction r (renormalizedMass r ν l ell e Λ) e Λ * (r * ψ) ^ 2 / (2 * ν) :=
  (renormalizedMass_flux_forms hr hν l ell ψ e Λ).2

section PhysicalMass

variable {M e Λ U V : ℝ} {h r : ℝ → ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
  {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
  {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)

-- Kappa is absolutely continuous and nonincreasing at critical L4 regularity.
example (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let κ := fun t => -Real.exp (intervalExtension hU x.1 t v 2) / (4 * intervalExtension hU N t v)
    AbsolutelyContinuousOnInterval κ 0 U ∧ ∀ᵐ t ∂volume.restrict (Icc 0 U), deriv κ t ≤ 0 := by
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR le_rfl hf (horizonPhi h r 0)
  have hg := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
  obtain ⟨hac, hd⟩ := hx.kappa_horizontal_regular hx.choose rfl hn hl (fun u v => (hg u v).2.2.1.ne) v
  refine ⟨hac, ?_⟩
  filter_upwards [hd, ae_restrict_mem measurableSet_Icc,
    (volume.restrict (Icc 0 U)).ae_ne 0, (volume.restrict (Icc 0 U)).ae_ne U] with t ht hmem ht0 htU
  rw [(ht.hasDerivAt (Icc_mem_nhds (lt_of_le_of_ne hmem.1 ht0.symm) (lt_of_le_of_ne hmem.2 htU))).deriv]
  exact div_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (hg _ v).2.2.2.1.le (hg _ v).2.1.le) (sq_nonneg _)) (hg _ v).2.2.1.le

-- The conformal cancellation holds between arbitrary horizontal endpoints, including equality.
example (v : Icc 0 V) (a b : Icc 0 U) (hab : a ≤ b) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let R := fun t => intervalExtension hU x.1 t v 0
    let m := fun t => intervalExtension hU (massField e Λ x.1 x.2.1 N hx.choose) t v
    let κ := fun t => -Real.exp (intervalExtension hU x.1 t v 2) / (4 * intervalExtension hU N t v)
    let K := fun t => horizonK (R t) (m t) e Λ
    (x.2.1 b v 2 - 2 * K b) - (x.2.1 a v 2 - 2 * K a) =
      2 * K b * (κ b - 1) - 2 * K a * (κ a - 1) - ∫ t in (a : ℝ)..b,
        (2 * K t * deriv κ t + 2 * κ t * deriv m t / (R t) ^ 2 +
          2 * x.2.2 t v 1 * intervalExtension hU x.2.1 t v 1) := by
  obtain ⟨hn, hl⟩ := incomingWave_constraint_data hU hUR le_rfl hf (horizonPhi h r 0)
  exact (hx.conformal_horizontal_identity hx.choose rfl hn hl
    (fun u v => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u v).2.2.1.ne) v).2 a b hab

-- The exceptional set in u is independent of v, including at critical L4.
example :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
      let u := projIcc 0 U hU t
      HasDerivWithinAt (fun s => intervalExtension hU m s v)
        (horizonFunction (x.1 u v 0) (m u v) e Λ * (x.1 u v 0 * x.2.2 t v 1) ^ 2 / (2 * N u v))
        (Icc 0 U) t :=
  hx.incoming_mass_derivative hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf

example (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    let J := fun t => -2 * (intervalExtension hU x.1 t v 0) ^ 2 * intervalExtension hU x.2.1 t v 0 *
      Real.exp (-intervalExtension hU x.1 t v 2) * (x.2.2 t v 1) ^ 2
    IntervalIntegrable J volume 0 U ∧ ∀ u : Icc 0 U,
      m u v = horizonMass M h v + ∫ t in (0 : ℝ)..u, J t :=
  hx.incoming_mass_integral hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf v

example (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    HasDerivWithinAt (intervalExtension hV (m u))
      ((x.1 u v 0 * x.2.1 u v 1) ^ 2 / (2 * (-Real.exp (x.1 u v 2) / (4 * N u v)))) (Icc 0 V) v :=
  hx.outgoing_mass_derivative hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u v

example (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    massField e Λ x.1 x.2.1 N hx.choose u a ≤ massField e Λ x.1 x.2.1 N hx.choose u b :=
  hx.mass_monotone hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u hab

end PhysicalMass

-- A constructed solution with nonzero incoming scalar data has the actual mass fluxes.
example : ∃ U : ℝ, ∃ hU : 0 < U, ∃ x : WaveState U U, ∃ m : C(Icc 0 U, C(Icc 0 U, ℝ)),
    (∃ z v d, IsWaveIntegral hU.le hU.le 0 0 z v d x ∧
      ∃ hr : ∀ u v, x.1 u v 0 ≠ 0, m = massField 0 0 x.1 x.2.1 (radialNuField hU.le 0 0 z x.1 hr) hr) ∧
    (∀ u, Monotone (m u)) ∧ (∀ v, m ⟨0, le_rfl, hU.le⟩ v = 1) ∧
    x.1 ⟨U / 2, (half_pos hU).le, half_le_self hU.le⟩ ⟨0, le_rfl, hU.le⟩ 1 = U / 2 := by
  have hc : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hi : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) ^ 2) (Ioi t) := fun _ => by simp
  have hrc : Continuous (fun _ : ℝ => (2 : ℝ)) := continuous_const
  have hr0 : ∀ _ : ℝ, (2 : ℝ) ≠ 0 := fun _ => by norm_num
  have hφ : ∀ t : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ) / 2) (Ioi t) := fun _ => by simp
  have hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun _ : ℝ => (2 : ℝ))
      (horizonFunction 2 (horizonMass 1 (fun _ => 0) t) 0 0) (Ici 0) t := by
    intro t _ht
    simpa [horizonFunction, horizonMass] using hasDerivWithinAt_const t (Ici (0 : ℝ)) (2 : ℝ)
  obtain ⟨U, hU, hUR, _hU1, hsolve⟩ := exists_local_horizon_wave_of_scalar_bound hc hi hrc hr0
    (by norm_num : (0 : ℝ) < 2) hφ hrd 1 zero_le_one
  let hf : MemLp (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 U)) := memLp_const 1
  have hnorm : (eLpNorm (fun _ : ℝ => (1 : ℝ)) ∞ (volume.restrict (Icc 0 U))).toReal ≤ 1 := by
    by_cases hm : volume.restrict (Icc (0 : ℝ) U) = 0
    · simp [hm]
    · simp [eLpNorm_const (1 : ℝ) (by norm_num : (∞ : ℝ≥0∞) ≠ 0) hm]
  obtain ⟨x, hx, htraces⟩ := hsolve hU.le hU.le hUR le_rfl le_rfl le_top hf hnorm
  refine ⟨U, hU, x, _, ⟨_, _, _, hx, hx.choose, rfl⟩,
    hx.mass_monotone hU.le hU.le hUR hc hi hrc hr0 hφ hrd le_top hf, ?_, ?_⟩
  · intro v
    simpa only [horizonMass, zero_pow (by norm_num : 2 ≠ 0), integral_zero, zero_div, sub_zero] using
      hx.horizon_mass_trace hU.le hU.le hUR hc hi hrc hr0 hφ hrd le_top hf v
  · rw [htraces.1]
    simp [incomingPhi, horizonPhi]

-- The critical Holder power is retained, rather than replaced by a length-one bound.
example {U V δ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) {f : ℝ → ℝ}
    (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (hw : U * Real.exp V ≤ δ) :
    Real.exp ((3 / 4) * V) * (∫ t in (0 : ℝ)..U, |f t|) ≤
      (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal * δ ^ (3 / 4 : ℝ) := by
  have hb := incoming_weighted_integral_le_lp (a := 1) (c := 3 / 4) hU hV
    (by norm_num : (1 : ℝ≥0∞) ≤ 4) hf (by norm_num) (by simpa using hw)
  norm_num at hb ⊢
  exact hb

example {U V δ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) {f : ℝ → ℝ}
    (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) (hw : U * Real.exp V ≤ δ) :
    Real.exp (V / 2) * (∫ t in (0 : ℝ)..U, |f t|) ≤
      (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal * δ := by
  have hb := incoming_weighted_integral_le_lp (a := 1) (c := 1 / 2) hU hV le_top hf
    (by norm_num) (by simpa using hw)
  simpa only [ENNReal.toReal_top, div_zero, sub_zero, Real.rpow_one, one_div_mul_eq_div] using hb

example (V : ℝ) (hV : 0 ≤ V) (f : ℝ → ℝ)
    (hf : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 0))) :
    Real.exp (V / 2) * (∫ t in (0 : ℝ)..0, |f t|) ≤ 0 := by
  have hb := incoming_weighted_integral_le_lp (a := 1) (c := 1 / 2) (δ := 0) le_rfl hV
    (by norm_num : (1 : ℝ≥0∞) ≤ 4) hf (by norm_num) (by simp)
  norm_num at hb ⊢

-- A nonzero continuous source tests the exponential kernel and its strict rate margin.
example (V : ℝ) (hV : 0 ≤ V) (v : Icc 0 V) :
    let ν : C(Icc (0 : ℝ) 1, C(Icc 0 V, ℝ)) := ContinuousMap.const _
      ⟨fun w => Real.exp (w : ℝ), Real.continuous_exp.comp continuous_subtype_val⟩
    let w : WaveRectangle 1 V := ContinuousMap.const _
      ⟨fun w => ![0, Real.exp (-(1 / 2) * (w : ℝ)), 0], by fun_prop⟩
    |scalarTransportCorrection hV ν w ⟨0, by norm_num, by norm_num⟩ v| ≤
      2 * Real.exp ((1 / 2) * v) := by
  let ν : C(Icc (0 : ℝ) 1, C(Icc 0 V, ℝ)) := ContinuousMap.const _
    ⟨fun w => Real.exp (w : ℝ), Real.continuous_exp.comp continuous_subtype_val⟩
  let w : WaveRectangle 1 V := ContinuousMap.const _
    ⟨fun w => ![0, Real.exp (-(1 / 2) * (w : ℝ)), 0], by fun_prop⟩
  change |scalarTransportCorrection hV ν w ⟨0, by norm_num, by norm_num⟩ v| ≤ _
  have hb := scalarTransportCorrection_weighted_bound (hV := hV) (a := 1) (c := 1 / 2) (N := 1) (S := 1)
    (by norm_num) zero_le_one zero_le_one ν w
    (fun u v => by simp [ν, abs_of_pos (Real.exp_pos _)])
    (fun u v => by simp [w, abs_of_pos (Real.exp_pos _)]) ⟨0, by norm_num, by norm_num⟩ v
  norm_num at hb ⊢
  exact hb

example {U : ℝ} (ν : C(Icc 0 U, C(Icc (0 : ℝ) 0, ℝ))) (w : WaveRectangle U 0)
    (u : Icc 0 U) : scalarTransportCorrection le_rfl ν w u ⟨0, le_rfl, le_rfl⟩ = 0 := by
  change (∫ t in (0 : ℝ)..0, -ν u (projIcc 0 0 le_rfl t) * w u (projIcc 0 0 le_rfl t) 1) = 0
  simp only [intervalIntegral.integral_same]

example {U V e Λ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {z : C(Icc 0 U, WaveVector)} {v : C(Icc 0 V, WaveVector)}
    {d : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ z v d x)
    {z₀ : WaveVector} (hz : z = ContinuousMap.const _ z₀ + horizontalPrimitive hU d)
    (hd : ∀ᵐ u ∂volume.restrict (Icc 0 U), d u 0 = -1)
    (hr : ∀ u v, 1 ≤ x.1 u v 0) (hin : ∀ u, |z u 0| ≤ 2)
    (hn : ∀ u v, |radialNuField hV e Λ z x.1 hx.choose u v| ≤ 2 * Real.exp (v : ℝ))
    (hl : ∀ u v, |x.2.1 u v 0| ≤ 1)
    (hh : ∀ t : Icc 0 V, Real.exp ((1 / 2) * t) * |x.1 ⟨0, le_rfl, hU⟩ t 0 * v t 1| ≤ 3)
    (hf : Real.exp ((1 / 2) * V) * (∫ t in (0 : ℝ)..U, |d t 1|) ≤ 4)
    (hw : U * Real.exp V ≤ 1 / 16) :
    (∀ u v, |x.2.1 u v 1| ≤ 22 * Real.exp (-(1 / 2) * (v : ℝ))) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        |x.2.2 u v 1| ≤ 2 * |d u 1| + 88 * Real.exp ((1 / 2) * v) := by
  have hs := hx.outer_scalar_bound (a := 1) (c := 1 / 2) (ρ := 1) (R := 2) (N := 2)
    (L := 1) (H := 3) (J := 4) (δ := 1 / 16) hx.choose hz hd
    (by norm_num) (by norm_num) zero_lt_one (by norm_num) (by norm_num) zero_le_one
    (by norm_num) (by norm_num) (by norm_num) hr hin (by simpa using hn) hl hh hf (by simpa using hw) (by norm_num)
  norm_num at hs ⊢
  exact hs

example {M e Λ U V : ℝ} {h r : ℝ → ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    (hfn : (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ 4)
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (hlo : ∀ u v, 1 ≤ x.1 u v 0)
    (hν : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ 2 * Real.exp (v : ℝ))
    (hl : ∀ u v, |x.2.1 u v 0| ≤ 1)
    (hh : ∀ v : Icc 0 V, Real.exp ((1 / 2) * v) * |h v| ≤ 3)
    (hw : U * Real.exp V ≤ 1 / 16) :
    let E := 2 * (3 + r 0 * (4 * (1 / 16 : ℝ) ^ (3 / 4 : ℝ)))
    (∀ u v, |x.2.1 u v 1| ≤ E * Real.exp (-(1 / 2) * (v : ℝ))) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V,
        |x.2.2 u v 1| ≤ r 0 * |f u| + 4 * E * Real.exp ((1 / 2) * v) := by
  have hs := hx.horizon_outer_scalar (a := 1) (c := 1 / 2) (ρ := 1) (N := 2) (L := 1)
    (H := 3) (A := 4) (δ := 1 / 16) hU hV hUR hc hi hrc hr0 hφ hrd
    le_rfl hf (by norm_num) hfn (by norm_num) (by norm_num) (by norm_num) zero_lt_one
    (by norm_num) zero_le_one (by norm_num) (by norm_num) hlo (by simpa using hν) hl hh (by simpa using hw) (by norm_num)
  norm_num at hs ⊢
  exact hs

-- Prefix square estimates keep the critical length power, including p=infinity.
example {U : ℝ} {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (u : Icc 0 U) :
    (∫ t in (0 : ℝ)..u, f t ^ 2) ≤
      (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ^ 2 * (u : ℝ) ^ (1 / 2 : ℝ) := by
  have hb := incoming_integral_sq_le_lp_power (by norm_num : (2 : ℝ≥0∞) ≤ 4) hf u
  norm_num at hb ⊢
  exact hb

example {U : ℝ} {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) (u : Icc 0 U) :
    (∫ t in (0 : ℝ)..u, f t ^ 2) ≤
      (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ^ 2 * u := by
  simpa using incoming_integral_sq_le_lp_power le_top hf u

example (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 0))) :
    (∫ t in (0 : ℝ)..0, f t ^ 2) ≤ 0 := by
  have hb := incoming_integral_sq_le_lp_power (by norm_num : (2 : ℝ≥0∞) ≤ 4) hf ⟨0, le_rfl, le_rfl⟩
  norm_num at hb ⊢

example {U : ℝ} (hU : 0 ≤ U) {f q ψ : ℝ → ℝ}
    (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    (hn : (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ 3)
    (hi : IntervalIntegrable (fun t => q t * ψ t ^ 2) volume 0 U)
    (hq : ∀ᵐ t ∂volume.restrict (Icc 0 U), q t ≤ 5)
    (hψ : ∀ᵐ t ∂volume.restrict (Icc 0 U), |ψ t| ≤ 2 * |f t| + 4) (u : Icc 0 U) :
    (∫ t in (0 : ℝ)..u, q t * ψ t ^ 2) ≤ 5 * (72 * (u : ℝ) ^ (1 / 2 : ℝ) + 32 * u) := by
  have hb := weighted_quadratic_integral_le_lp hU (by norm_num : (2 : ℝ≥0∞) ≤ 4)
    hf (by norm_num : (0 : ℝ) ≤ 3) hn (by norm_num) (by norm_num) (by norm_num) hi hq hψ u
  norm_num at hb ⊢
  exact hb

section PhysicalOuterFeedback

variable {M e Λ U V : ℝ} {h r : ℝ → ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
  {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)

example {R L : ℝ} (hR : 0 ≤ R)
    (hr : ∀ u v, x.1 u v 0 ≤ R) (hl : ∀ u v, |x.2.1 u v 0| ≤ L) (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    |massField e Λ x.1 x.2.1 N hx.choose u v - horizonMass M h v| ≤
      R * L / 2 * ((-Real.exp (x.1 u v 2) / (4 * N u v))⁻¹ - 1) :=
  hx.mass_kappa_bound hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf hR hr hl u v

example (hr : ∀ u v, x.1 u v 0 ≤ 2) (hl : ∀ u v, |x.2.1 u v 0| ≤ 3)
    (u : Icc 0 U) (v : Icc 0 V)
    (he : (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU (radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose) t v)) ≤ Real.log (4 / 3)) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    3 / 4 ≤ -Real.exp (x.1 u v 2) / (4 * N u v) ∧
      |massField e Λ x.1 x.2.1 N hx.choose u v - horizonMass M h v| ≤ 1 := by
  have hb := hx.mass_constraint_bound hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3) hr hl u v he
  simp only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at hb
  norm_num at hb
  exact hb

example (hfn : (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ 4)
    (hlo : ∀ u v, 1 ≤ x.1 u v 0) (hrhi : ∀ u v, x.1 u v 0 ≤ 3)
    (hνlo : ∀ (u : Icc 0 U) (v : Icc 0 V), (1 / 2) * Real.exp (v : ℝ) ≤
      -radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose u v)
    (hνhi : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ 2 * Real.exp (v : ℝ))
    (hl : ∀ u v, |x.2.1 u v 0| ≤ 1)
    (hh : ∀ v : Icc 0 V, Real.exp ((1 / 2) * v) * |h v| ≤ 3)
    (hw : U * Real.exp V ≤ 1 / 16) (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let E := 2 * (3 + r 0 * (4 * (1 / 16 : ℝ) ^ (3 / 4 : ℝ)))
    let B := 12 * ((r 0) ^ 2 * 16 * Real.exp (-(v : ℝ)) * (u : ℝ) ^ (1 / 2 : ℝ) + (4 * E) ^ 2 * u)
    (∫ t in (0 : ℝ)..u, intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 / (-intervalExtension hU N t v)) ≤ B ∧
    Real.exp (-B) ≤ -Real.exp (x.1 u v 2) / (4 * N u v) ∧
    |massField e Λ x.1 x.2.1 N hx.choose u v - horizonMass M h v| ≤ (3 / 2) * (Real.exp B - 1) := by
  have hb := hx.horizon_outer_feedback (a := 1) (c := 1 / 2) (ρ := 1) (R := 3) (n := 1 / 2)
    (N := 2) (L := 1) (H := 3) (A := 4) (δ := 1 / 16) hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
    (by norm_num) hfn (by norm_num) (by norm_num) (by norm_num) zero_lt_one (by norm_num) (by norm_num)
    (by norm_num) zero_le_one (by norm_num) (by norm_num) hlo hrhi (by simpa using hνlo)
    (by simpa using hνhi) hl hh (by simpa using hw) (by norm_num) u v
  norm_num at hb ⊢
  exact hb

-- Both radius and lambda improve without an assumed lambda budget.
example (hlo : ∀ u v, 1 ≤ x.1 u v 0)
    (haxis : ∀ v : Icc 0 V, r v ∈ Icc 2 3)
    (hpot : ∀ t ∈ Icc (1 : ℝ) 3, |radialPotential t e Λ| ≤ 1)
    (hν : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      x.1 hx.choose u v| ≤ 2 * Real.exp (v : ℝ))
    (hout : ∀ v : Icc 0 V, |horizonFunction (r v) (horizonMass M h v) e Λ| ≤ (1 / 16) * Real.exp (-2 * v))
    (hw : U * Real.exp V ≤ 1 / 64) (u : Icc 0 U) (v : Icc 0 V) :
    63 / 32 ≤ x.1 u v 0 ∧ x.1 u v 0 ≤ 3 ∧
      |x.2.1 u v 0| ≤ (3 / 16) * Real.exp (-2 * v) + 24 * u * Real.exp (v : ℝ) ∧
      |x.2.1 u v 0| ≤ 9 / 16 := by
  have hb := hx.horizon_outer_radial (a := 1) (d := 2) (ρ := 1) (R := 3) (rmin := 2)
    (N := 2) (P := 1) (H := 1 / 16) (δ := 1 / 64) hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
    zero_le_one (by norm_num) zero_lt_one (by norm_num) (by norm_num) zero_le_one (by norm_num)
    hpot hlo haxis (by simpa using hν) hout (by simpa using hw) u v
  norm_num at hb
  simpa only [neg_mul] using hb.2.2

example (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    N u v = -Real.exp (∫ t in (0 : ℝ)..v,
      2 * (-Real.exp (intervalExtension hV (x.1 u) t 2) / (4 * intervalExtension hV (N u) t)) *
        horizonK (intervalExtension hV (x.1 u) t 0) (intervalExtension hV (m u) t) e Λ) :=
  hx.radialNu_mass_exponential hx.choose
    (fun u v => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u v).2.2.1) u v

example (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    x.1 u v 0 * N u v = -(r 0 - (u : ℝ)) * Real.exp (∫ t in (0 : ℝ)..v,
      Real.exp (intervalExtension hV (x.1 u) t 2) *
        radialPotential (intervalExtension hV (x.1 u) t 0) e Λ / intervalExtension hV (N u) t) := by
  have hb := radialNuField_flux_exponential hx.choose (hx.incoming_radius_pos hU hV hUR le_rfl hf)
    (fun u v => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u v).2.2.1) u v
  dsimp only at hb
  rw [incomingWaveCurve_apply] at hb
  exact hb

example (u : Icc 0 U) :
    x.1 u ⟨0, le_rfl, hV⟩ 0 * radialNuField hV e Λ
      (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose u ⟨0, le_rfl, hV⟩ = -(r 0 - (u : ℝ)) := by
  have hb := radialNuField_flux_exponential hx.choose (hx.incoming_radius_pos hU hV hUR le_rfl hf)
    (fun u v => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u v).2.2.1) u ⟨0, le_rfl, hV⟩
  dsimp only at hb
  rw [incomingWaveCurve_apply] at hb
  simpa [incomingRadius] using hb

end PhysicalOuterFeedback

example : horizonFunction 2 (renormalizedMass 2 (-1) (1 / 8) (Real.log 4) 1 (1 / 4)) 1 (1 / 4) = 1 / 8 ∧
    2 * (-Real.exp (Real.log 4) / (4 * (-1))) *
      horizonK 2 (renormalizedMass 2 (-1) (1 / 8) (Real.log 4) 1 (1 / 4)) 1 (1 / 4) = -3 / 16 := by
  have hb := renormalizedMass_first_order (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (-1 : ℝ) ≠ 0) (1 / 8) (Real.log 4) 1 (1 / 4)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hb ⊢
  norm_num [radialPotential] at hb ⊢
  exact ⟨hb.1.symm, hb.2.symm⟩

example {U V : ℝ} (z w : WaveRectangle U V) (N : C(Icc 0 U, C(Icc 0 V, ℝ)))
    (hr : ∀ u v, z u v 0 ≠ 0) (hN : ∀ u v, N u v ≠ 0) (u : Icc 0 U) (v : Icc 0 V) :
    w u v 0 = (-Real.exp (z u v 2) / (4 * N u v)) * horizonFunction (z u v 0) (massField 1 2 z w N hr u v) 1 2 :=
  massField_lambda_eq_kappa z w N hr hN u v

example {U V e Λ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {z : C(Icc 0 U, WaveVector)} {w : C(Icc 0 V, WaveVector)}
    {d : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ z w d x) {c : WaveVector}
    (hz : z = ContinuousMap.const _ c + horizontalPrimitive hU d)
    (hd : ∀ᵐ u ∂volume.restrict (Icc 0 U), d u 0 = -1)
    (hr : ∀ u v, 1 ≤ x.1 u v 0) (haxis : ∀ v, x.1 ⟨0, le_rfl, hU⟩ v 0 ≤ 3)
    (hP : ∀ t ∈ Icc (1 : ℝ) 3, |radialPotential t e Λ| ≤ 1)
    (hν : ∀ u v, radialNuField hV e Λ z x.1 hx.choose u v ≤ 0)
    (hΩ : ∀ u v, Real.exp (x.1 u v 2) ≤ -4 * radialNuField hV e Λ z x.1 hx.choose u v)
    (u : Icc 0 U) (v : Icc 0 V) (hw : w v 0 = 0) :
    |x.2.1 u v 0| ≤ 12 * (x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0) := by
  have hb := hx.radial_flux_gap_bound hx.choose hz hd zero_lt_one (by norm_num : (1 : ℝ) ≤ 3)
    zero_le_one hP hr haxis hν hΩ u v
  simpa only [hw, abs_zero, mul_zero, zero_add, div_one, mul_one, show (4 : ℝ) * 3 = 12 by norm_num] using hb.2.2

example {u v δ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : u * Real.exp (2 * v) ≤ δ) :
    (∫ t in (0 : ℝ)..v, |3 * Real.exp (-2 * t) + 5 * u * Real.exp (2 * t)|) ≤ (3 + 5 * δ) / 2 := by
  exact exponential_error_integral_bound (by norm_num) hu hv (by norm_num) (by norm_num)
    (fun t _ => by rw [abs_of_nonneg (by positivity)]) hw

example {u C D : ℝ} (hu : 0 ≤ u) (hC : 0 ≤ C) (hD : 0 ≤ D) {f : ℝ → ℝ}
    (hf : |f 0| ≤ C + D * u) : (∫ t in (0 : ℝ)..0, |f t|) ≤ (C + D * u) / 2 := by
  apply exponential_error_integral_bound (a := 2) (u := u) (by norm_num) hu le_rfl hC hD
  · intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    simpa only [ht0, mul_zero, Real.exp_zero, mul_one] using hf
  · simp only [mul_zero, Real.exp_zero, mul_one, le_refl]

example : ∃ K : NNReal, LipschitzOnWith K (fun t => radialPotential t 1 (1 / 4)) (Icc (1 : ℝ) 3) :=
  radialPotential_lipschitzOn zero_lt_one

section PhysicalNuComparison

variable {M e Λ U V : ℝ} {h r : ℝ → ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
  {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U))) {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)

example (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let G := fun (q : Icc 0 U) (t : ℝ) => Real.exp (intervalExtension hV (x.1 q) t 2) *
      radialPotential (intervalExtension hV (x.1 q) t 0) e Λ / intervalExtension hV (N q) t
    (-N u v) = ((r 0 - (u : ℝ)) / r 0) * (r v / x.1 u v 0) *
      (-horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v) *
        Real.exp (∫ t in (0 : ℝ)..v, G u t - G ⟨0, le_rfl, hU⟩ t) :=
  hx.horizon_radial_ratio hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v

variable {δ : ℝ} {J : NNReal} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 16)
  (hfn : (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ 4)
  (hpot : ∀ t ∈ Icc (1 : ℝ) 3, |radialPotential t e Λ| ≤ 1)
  (hlip : LipschitzOnWith J (fun t => radialPotential t e Λ) (Icc (1 : ℝ) 3))
  (hlo : ∀ u v, 1 ≤ x.1 u v 0) (hrhi : ∀ u v, x.1 u v 0 ≤ 3)
  (hνlo : ∀ (u : Icc 0 U) (v : Icc 0 V), (1 / 2) * Real.exp (v : ℝ) ≤
    -radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v)
  (hνhi : ∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
    x.1 hx.choose u v| ≤ 2 * Real.exp (v : ℝ))
  (hlam : ∀ u v, |x.2.1 u v 0| ≤ 1)
  (hout : ∀ v : Icc 0 V, Real.exp ((1 / 2) * v) * |h v| ≤ 3)
  (hw : U * Real.exp V ≤ δ)

example (hp4 : p = 4) (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ r 0 / 4)
    (heps : let E := 2 * (3 + r 0 * (4 * δ ^ (3 / 4 : ℝ)))
      768 * (r 0) ^ 2 * (u : ℝ) ^ (1 / 2 : ℝ) + (48 * (4 * E) ^ 2 + 8 * J) * δ ≤ Real.log (4 / 3)) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let S := -horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v
    (9 / 16) * S ≤ -N u v ∧ -N u v ≤ (3 / 2) * S := by
  subst p
  have hb := hx.horizon_outer_nu_comparison (a := 1) (c := 1 / 2) (ρ := 1) (R := 3) (n := 1 / 2)
    (N := 2) (L := 1) (H := 3) (A := 4) (P := 1) hU hV hUR hc hi hrc hr0 hφ hrd hp hf
    (by norm_num) hfn zero_lt_one (by norm_num) (by norm_num) (by norm_num) zero_lt_one
    (by norm_num) (by norm_num) (by norm_num) zero_le_one (by norm_num) hδ zero_le_one hpot hlip hlo hrhi
    (by simpa using hνlo) (by simpa using hνhi) hlam hout (by simpa using hw) (by norm_num; linarith) u v
  norm_num only [ENNReal.toReal_ofNat, div_one, mul_one, one_mul] at hb
  let E := 2 * (3 + r 0 * (4 * δ ^ (3 / 4 : ℝ)))
  let ε := 768 * (r 0) ^ 2 * (u : ℝ) ^ (1 / 2 : ℝ) + (48 * (4 * E) ^ 2 + 8 * J) * δ
  have heq : 48 * (r 0) ^ 2 * 16 * (u : ℝ) ^ (1 / 2 : ℝ) + (48 * (4 * E) ^ 2 + 4 * J * 2) * δ = ε := by
    dsimp only [ε]
    ring
  rw [heq] at hb
  let S := -horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v
  have hS : 0 ≤ S := (neg_pos.2 (horizon_normalization _ (v : ℝ)).1).le
  have hinit : (3 / 4 : ℝ) ≤ (r 0 - (u : ℝ)) / r 0 := by
    apply (le_div_iff₀ (hU.trans_lt hUR)).2
    linarith only [hu]
  have hel : (3 / 4 : ℝ) ≤ Real.exp (-ε) := by
    have hh := Real.exp_le_exp.2 (neg_le_neg heps)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at hh
    norm_num only at hh
    exact hh
  have heu : Real.exp ε ≤ (4 / 3 : ℝ) := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] using Real.exp_le_exp.2 heps
  have hlo' := mul_le_mul (mul_le_mul_of_nonneg_right hinit hS) hel (by positivity : 0 ≤ (3 / 4 : ℝ))
    (mul_nonneg (div_nonneg (sub_pos.2 (u.property.2.trans_lt hUR)).le (hU.trans hUR.le)) hS)
  have hhi' := mul_le_mul (mul_le_mul_of_nonneg_right (show 1 + 2 * δ ≤ (9 / 8 : ℝ) by linarith only [hδsmall]) hS)
    heu (Real.exp_pos _).le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 8) hS)
  constructor
  · exact (show (9 / 16 : ℝ) * S ≤ ((r 0 - (u : ℝ)) / r 0) * S * Real.exp (-ε) by nlinarith only [hlo']).trans hb.2.1
  · exact hb.2.2.trans (show (1 + 2 * δ) * S * Real.exp ε ≤ (3 / 2 : ℝ) * S by nlinarith only [hhi'])

example (hpTop : p = ∞) (u : Icc 0 U) (v : Icc 0 V) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let E := 2 * (3 + r 0 * (4 * δ))
    let ε := 768 * (r 0) ^ 2 * u + (48 * (4 * E) ^ 2 + 8 * J) * δ
    let S := -horizonNu (fun t => horizonK (r t) (horizonMass M h t) e Λ) v
    ((r 0 - (u : ℝ)) / r 0) * S * Real.exp (-ε) ≤ -N u v ∧
      -N u v ≤ (1 + 2 * δ) * S * Real.exp ε := by
  subst p
  have hb := hx.horizon_outer_nu_comparison (a := 1) (c := 1 / 2) (ρ := 1) (R := 3) (n := 1 / 2)
    (N := 2) (L := 1) (H := 3) (A := 4) (P := 1) hU hV hUR hc hi hrc hr0 hφ hrd hp hf
    (by norm_num) hfn zero_lt_one (by norm_num) (by norm_num) (by norm_num) zero_lt_one
    (by norm_num) (by norm_num) (by norm_num) zero_le_one (by norm_num) hδ zero_le_one hpot hlip hlo hrhi
    (by simpa using hνlo) (by simpa using hνhi) hlam hout (by simpa using hw) (by norm_num; linarith) u v
  norm_num only [ENNReal.toReal_top, div_zero, sub_zero, Real.rpow_one, div_one, mul_one, one_mul] at hb ⊢
  let E := 2 * (3 + r 0 * (4 * δ))
  have heq : 48 * (r 0) ^ 2 * 16 * (u : ℝ) + (48 * (4 * E) ^ 2 + 4 * J * 2) * δ =
      768 * (r 0) ^ 2 * u + (48 * (4 * E) ^ 2 + 8 * J) * δ := by ring
  rw [heq] at hb
  exact hb.2

end PhysicalNuComparison

example : (3 / 4 : ℝ) ≤ 1 - 1 / (4 : ℝ≥0∞).toReal ∧
    (1 / 2 : ℝ) ≤ 1 - 2 / (4 : ℝ≥0∞).toReal := incoming_exponent_bounds le_rfl

example : (3 / 4 : ℝ) ≤ 1 - 1 / (∞ : ℝ≥0∞).toReal ∧
    (1 / 2 : ℝ) ≤ 1 - 2 / (∞ : ℝ≥0∞).toReal := incoming_exponent_bounds le_top

example : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (p : ℝ≥0∞), 4 ≤ p →
    ∀ u ∈ Icc (0 : ℝ) δ, 3 * u ^ (1 - 2 / p.toReal) + 5 * δ ≤ Real.log (4 / 3) := by
  obtain ⟨δ, hδ, hδ1, _, _, _, herr⟩ := exists_small_outer_width zero_lt_one zero_lt_one
    (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)) 2 3 3 5
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro p hp u hu
  have hb := (Real.rpow_le_rpow_of_exponent_ge' hu.1 (hu.2.trans hδ1)
    (by norm_num) (incoming_exponent_bounds hp).2).trans
    (Real.rpow_le_rpow hu.1 hu.2 (by norm_num : (0 : ℝ) ≤ 1 / 2))
  exact (add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 3)) le_rfl).trans herr

example {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-1) * Real.exp (2 * t) ≤ -horizonNu (fun w => 1 + Real.exp (-2 * w)) t ∧
      -horizonNu (fun w => 1 + Real.exp (-2 * w)) t ≤ Real.exp 1 * Real.exp (2 * t) := by
  have hb := horizonNu_exponential_bounds (a := 2) (d := 2) (C := 2)
    (K := fun w => 1 + Real.exp (-2 * w)) (by fun_prop) (by norm_num) (by norm_num) (fun w _ => by
      rw [show 2 * (1 + Real.exp (-2 * w)) - 2 = 2 * Real.exp (-2 * w) by ring,
        abs_of_nonneg (by positivity)]) ht
  norm_num only [show -(2 : ℝ) / 2 = -1 by norm_num, div_self (by norm_num : (2 : ℝ) ≠ 0)] at hb
  exact hb

example (B : Background) {s : ℝ} (hs : 0 < s) :
    ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧ δ < B.event ∧
      ∀ h : ℝ → ℝ, Continuous h → (∀ t, ‖h t‖ ≤ η * Real.exp (-s * t)) →
        (∀ t ∈ Ici (0 : ℝ), 0 < h t) →
        ∃ (r : ℝ → ℝ) (n N : ℝ), B.OutgoingEstimates h r s ∧ 0 < n ∧ n ≤ 1 ∧ 1 ≤ N ∧
          ∀ t ∈ Ici (0 : ℝ),
            n * Real.exp (B.outerRate * t) ≤
              -horizonNu (fun w => horizonK (r w) (horizonMass B.mass h w) B.charge B.cosmological) t ∧
            -horizonNu (fun w => horizonK (r w) (horizonMass B.mass h w) B.charge B.cosmological) t ≤
              N * Real.exp (B.outerRate * t) := by
  obtain ⟨η, δ, hη, hδ, hδR, hd⟩ := B.exists_small_tail_outgoing_data hs
  refine ⟨η, δ, hη, hδ, hδR, ?_⟩
  intro h hc hb hp
  obtain ⟨r, hrc, hrb, _, _, _, hOut⟩ := hd h hc hb hp
  obtain ⟨n, N, hn, hn1, hN, hν⟩ := hOut.nu_bounds hs hc (horizon_mass_integrable hs hη.le hc hb)
    hrc (fun t => ((sub_pos.2 hδR).trans_le (hrb t)).ne')
  exact ⟨r, n, N, hOut, hn, hn1, hN, hν⟩

example {M e Λ a c ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (ha : 0 < a) (hc0 : 0 ≤ c) (hac : c < a) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (c * t) * |h t| ≤ H)
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass M h t) e Λ| ≤ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
      (x : WaveState U V)
      (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → c ≤ a * (1 - 1 / p.toReal) →
      U * Real.exp (a * V) ≤ δ → (∀ u v, ρ ≤ x.1 u v 0) →
      (∀ (u : Icc 0 U) (v : Icc 0 V), (nH / 2) * Real.exp (a * v) ≤
        -radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v) →
      (∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        x.1 hx.choose u v| ≤ (2 * NH) * Real.exp (a * v)) →
      ∀ (u : Icc 0 U) (v : Icc 0 V),
        let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
        ρ < x.1 u v 0 ∧ (nH / 2) * Real.exp (a * v) < -ν u v ∧
          |ν u v| < (2 * NH) * Real.exp (a * v) := by
  obtain ⟨δ, L, hδ, _, _, _, hb⟩ := exists_horizon_outer_bootstrap hc hi hrc hr0 hφ hrd
    ha hc0 hac hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, hδ, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb hwidth hlo hνlo hνhi u v
  have h := hb U V hU hV hUR p hp f hf x hx hfn hcb hwidth hlo hνlo hνhi u v
  have hn := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1
  dsimp only
  rw [abs_of_neg hn]
  refine ⟨by linarith only [h.1, hρ], ?_, ?_⟩
  · exact (mul_lt_mul_of_pos_right (by linarith only [hnH]) (Real.exp_pos _)).trans_le h.2.2.2.1
  · exact h.2.2.2.2.trans_lt (mul_lt_mul_of_pos_right (by linarith only [hNH]) (Real.exp_pos _))

example {U V : ℝ} {f : ℝ × Icc (0 : ℝ) V → ℝ} (hf : Continuous f)
    (hz : ∀ v, f (0, v) ≤ -1)
    (hi : ∀ t ∈ Icc (0 : ℝ) U,
      (∀ q ∈ Icc (0 : ℝ) t, ∀ v, f (q, v) ≤ 0) → ∀ v, f (t, v) ≤ -1 / 2) :
    ∀ t ∈ Icc (0 : ℝ) U, ∀ v, f (t, v) < 0 := by
  exact continuous_prefix_bootstrap hf (fun v => (hz v).trans_lt (by norm_num))
    (fun t ht hp v => (hi t ht hp v).trans_lt (by norm_num))

example {f : ℝ × Fin 3 → ℝ} (hf : Continuous f) (hz : ∀ k, f (0, k) < 0) :
    ∀ t ∈ Icc (0 : ℝ) 0, ∀ k, f (t, k) < 0 := by
  apply continuous_prefix_bootstrap hf hz
  intro t ht _ k
  have he : t = 0 := le_antisymm ht.2 ht.1
  simpa only [he] using hz k

example {A U V : ℝ} (hV : 0 ≤ V) (hUA : U ≤ A)
    (zIn : C(Icc 0 A, WaveVector)) (z : WaveRectangle A V) (hr : ∀ u v, z u v 0 ≠ 0) :
    let τ := intervalTranslate (a := 0) (U := U) le_rfl (show 0 + U ≤ A by simpa using hUA)
    radialNuField hV 1 (1 / 4) (zIn.comp τ) (z.comp τ) (fun u v => hr (τ u) v) =
      (radialNuField hV 1 (1 / 4) zIn z hr).comp τ := radialNuField_comp_left hV 1 (1 / 4) zIn z hr _

section PhysicalOuterExistence

variable {M e Λ a c ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
  (ha : 0 < a) (hc0 : 0 ≤ c) (hac : c < a) (hρ : 0 < ρ)
  (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
  (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
  (hνaxis : ∀ t ∈ Ici (0 : ℝ),
    nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) t ∧
    -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) t ≤ NH * Real.exp (a * t))
  (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (c * t) * |h t| ≤ H)
  (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass M h t) e Λ| ≤ W)

include hφ hrd ha hc0 hac hρ hnH hNH hH hW hA haxis hνaxis hout hlout

example : ∃ δ : ℝ, 0 < δ ∧
    ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
      (x : WaveState U V)
      (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
      c ≤ a * (1 - 1 / p.toReal) → U * Real.exp (a * V) ≤ δ →
      ∀ (u : Icc 0 U) (v : Icc 0 V),
        let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
        ρ < x.1 u v 0 ∧ (nH / 2) * Real.exp (a * v) < -ν u v ∧
          |ν u v| < (2 * NH) * Real.exp (a * v) := by
  obtain ⟨δ, L, hδ, _, _, _, hb⟩ := exists_horizon_outer_bounds
    hc hi hrc hr0 hφ hrd ha hc0 hac hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, hδ, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hcb hwidth u v
  have hb' := hb U V hU hV hUR p hp f hf x hx hfn hcb hwidth u v
  have hn := (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hf u v).2.2.1
  dsimp only
  rw [abs_of_neg hn]
  refine ⟨by linarith only [hb'.1, hρ], ?_, ?_⟩
  · exact (mul_lt_mul_of_pos_right (by linarith only [hnH]) (Real.exp_pos _)).trans_le hb'.2.2.2.1
  · exact hb'.2.2.2.2.trans_lt (mul_lt_mul_of_pos_right (by linarith only [hNH]) (Real.exp_pos _))

example (hcp : c ≤ a * (3 / 4)) : ∃ δ : ℝ, 0 < δ ∧
    ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U))),
      (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A → U * Real.exp (a * V) ≤ δ →
      ∃! x : WaveState U V,
        IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x ∧
        ∀ u v, 7 * ρ / 4 ≤ x.1 u v 0 := by
  obtain ⟨δ, L, hδ, _, _, _, hs⟩ := exists_horizon_outer_wave
    hc hi hrc hr0 hφ hrd ha hc0 hac hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, hδ, ?_⟩
  intro U V hU hV hUR f hf hfn hw
  have hcb : c ≤ a * (1 - 1 / (4 : ℝ≥0∞).toReal) := by norm_num; exact hcp
  obtain ⟨x, ⟨hx, hb⟩, _⟩ := hs U V hU hV hUR 4 le_rfl f hf hfn hcb hw
  exact ⟨x, ⟨hx, fun u v => (hb u v).1⟩, fun y hy => hy.1.incoming_unique hU hV hUR le_rfl hf hx⟩

example : ∃ δ : ℝ, 0 < δ ∧
    ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (f : ℝ → ℝ) (hf : MemLp f ∞ (volume.restrict (Icc 0 U))),
      (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ≤ A → U * Real.exp (a * V) ≤ δ →
      ∃! x : WaveState U V,
        IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x := by
  obtain ⟨δ, L, hδ, _, _, _, hs⟩ := exists_horizon_outer_wave
    hc hi hrc hr0 hφ hrd ha hc0 hac hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, hδ, ?_⟩
  intro U V hU hV hUR f hf hfn hw
  have hcb : c ≤ a * (1 - 1 / (∞ : ℝ≥0∞).toReal) := by simpa using hac.le
  obtain ⟨x, ⟨hx, _⟩, _⟩ := hs U V hU hV hUR ∞ le_top f hf hfn hcb hw
  exact ⟨x, hx, fun y hy => hy.incoming_unique hU hV hUR le_top hf hx⟩

end PhysicalOuterExistence

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ici (0 : ℝ),
    ‖horizonFunction 2 (1 + Real.exp (-2 * t)) 1 (1 / 4) - horizonFunction 2 1 1 (1 / 4)‖ ≤
      C * Real.exp (-2 * t) := by
  apply horizonFunction_exponential_bound (R := 2) (M := 1) (δ := 0) (ε := 1)
    (r := fun _ => 2) (m := fun t => 1 + Real.exp (-2 * t)) (by norm_num) le_rfl (by norm_num) zero_le_one
  · intro t _
    simp only [sub_self, norm_zero, zero_mul, le_refl]
  · intro t _
    rw [show 1 + Real.exp (-2 * t) - 1 = Real.exp (-2 * t) by ring,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]

example (B : Background) : radialPotential B.event B.charge B.cosmological < 0 := by
  rw [B.radialPotential_event]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos B.outerRate_pos) (by norm_num)

example (B : Background) : ∃ η : ℝ, 0 < η ∧ η < B.event ∧
    radialPotential (B.event - η / 2) B.charge B.cosmological ≤ -B.outerRate / 8 := by
  obtain ⟨η, hη, hηR, hp⟩ := B.exists_negative_radial_potential
  exact ⟨η, hη, hηR, hp _ ⟨by linarith only [hη], by linarith only [hη]⟩⟩

section SignedRadialFlux

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {z : C(Icc 0 U, WaveVector)} {w : C(Icc 0 V, WaveVector)}
  {d : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ z w d x) {c : WaveVector}
  (hz : z = ContinuousMap.const _ c + horizontalPrimitive hU d)
  (hd : ∀ᵐ u ∂volume.restrict (Icc 0 U), d u 0 = -1)

example (hr : ∀ u v, 1 ≤ x.1 u v 0) (v : Icc 0 V)
    (hp : ∀ q, radialPotential (x.1 q v 0) e Λ ≤ -1 / 4)
    (hΩ : ∀ q, 2 * Real.exp (v : ℝ) ≤ Real.exp (x.1 q v 2)) (u : Icc 0 U) :
    x.1 u v 0 * x.2.1 u v 0 ≤ x.1 ⟨0, le_rfl, hU⟩ v 0 * w v 0 - (1 / 2) * u * Real.exp (v : ℝ) := by
  have hb := hx.radial_flux_negative_bound (a := 1) hx.choose hz zero_le_one
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 2) hr v
    (by simpa only [neg_div] using hp) (by simpa only [one_mul] using hΩ) u
  norm_num at hb ⊢
  exact hb

example (hν : ∀ (u : Icc 0 U) (v : Icc 0 V), 2 * Real.exp (3 * v) ≤
      -radialNuField hV e Λ z x.1 hx.choose u v) (u : Icc 0 U) (v : Icc 0 V) :
    2 * u * Real.exp (3 * v) ≤ x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0 :=
  hx.radial_gap_weighted_lower hx.choose hz hd hν u v

end SignedRadialFlux

example {u v δ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hw : u * Real.exp v ≤ δ) :
    let E := 2 * (3 + 2 * (4 * δ ^ (3 / 4 : ℝ)))
    12 * (64 * Real.exp (-v) * u ^ (1 / 2 : ℝ) + (4 * E) ^ 2 * u) ≤
      768 * δ ^ (1 / 2 : ℝ) + 92928 * δ := by
  have hb := outer_constraint_envelope (p := 4) (a := 1) (c := 1 / 2) (ρ := 1) (R := 3)
    (r₀ := 2) (n := 1 / 2) (N := 2) (L := 1) (H := 3) (A := 4) le_rfl zero_le_one
    (by norm_num) (by norm_num) zero_lt_one (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) zero_le_one (by norm_num) (by norm_num) hδ hδ1 hu hv (by simpa using hw)
  norm_num at hb ⊢
  exact hb

example {u v δ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hw : u * Real.exp v ≤ δ) :
    let E := 2 * (3 + 2 * (4 * δ))
    12 * (64 * Real.exp (-v) * u + (4 * E) ^ 2 * u) ≤
      768 * δ ^ (1 / 2 : ℝ) + 92928 * δ := by
  have hb := outer_constraint_envelope (p := ∞) (a := 1) (c := 1 / 2) (ρ := 1) (R := 3)
    (r₀ := 2) (n := 1 / 2) (N := 2) (L := 1) (H := 3) (A := 4) le_top zero_le_one
    (by norm_num) (by norm_num) zero_lt_one (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) zero_le_one (by norm_num) (by norm_num) hδ hδ1 hu hv (by simpa using hw)
  norm_num at hb ⊢
  exact hb

example (B : Background) {s H dH c A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s) (hA : 0 ≤ A) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ T σ τ : ℝ, 0 < δ ∧ 0 ≤ T ∧ 0 < σ ∧ 0 < τ ∧
      ∀ (V : ℝ) (hV : 0 ≤ V), T ≤ V →
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ)
        (hf : MemLp f p (volume.restrict (Icc 0 (δ * Real.exp (-B.outerRate * V))))),
        (eLpNorm f p (volume.restrict (Icc 0 (δ * Real.exp (-B.outerRate * V))))).toReal ≤ A →
        c ≤ B.outerRate * (1 - 1 / p.toReal) →
        ∃ (hU : 0 ≤ δ * Real.exp (-B.outerRate * V)) (hUR : δ * Real.exp (-B.outerRate * V) < r 0)
          (x : WaveState (δ * Real.exp (-B.outerRate * V)) V),
          IsWaveIntegral hU hV B.charge B.cosmological (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x ∧
          x.1 ⟨δ * Real.exp (-B.outerRate * V), hU, le_rfl⟩ ⟨V, hV, le_rfl⟩ 0 ≤ B.event - σ ∧
          x.2.1 ⟨δ * Real.exp (-B.outerRate * V), hU, le_rfl⟩ ⟨V, hV, le_rfl⟩ 0 ≤ -τ := by
  obtain ⟨δ, T, σ, τ, hδ, hδr, hT, hσ, hτ, hsx⟩ := B.exists_outer_trapped_prefix
    hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  refine ⟨δ, T, σ, τ, hδ, hT, hσ, hτ, ?_⟩
  intro V hV hTV p hp f hf hfn hcb
  let U := δ * Real.exp (-B.outerRate * V)
  have hU : 0 ≤ U := mul_nonneg hδ.le (Real.exp_pos _).le
  have hUδ : U ≤ δ := mul_le_of_le_one_right hδ.le
    (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 B.outerRate_pos.le) hV))
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  have hUR : U < r 0 := hUδ.trans_lt (hδr.trans_lt (by linarith only [hrp]))
  have hw : U * Real.exp (B.outerRate * V) = δ := by
    dsimp only [U]
    rw [mul_assoc, ← Real.exp_add, show -B.outerRate * V + B.outerRate * V = 0 by ring, Real.exp_zero, mul_one]
  obtain ⟨x, ⟨hx, hbnd⟩, _⟩ := hsx U V hU hV hUR p hp f hf hfn hcb hw.le
  exact ⟨hU, hUR, x, hx, hbnd ⟨U, hU, le_rfl⟩ ⟨V, hV, le_rfl⟩ hTV hw⟩

section ActualRadialLevels

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {z : C(Icc 0 U, WaveVector)} {w : C(Icc 0 V, WaveVector)}
  {d : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ z w d x) {c : WaveVector}
  (hz : z = ContinuousMap.const _ c + horizontalPrimitive hU d)
  (hd : ∀ᵐ u ∂volume.restrict (Icc 0 U), d u 0 = -1)

example (v : Icc 0 V) (hν : ∀ u, radialNuField hV e Λ z x.1 hx.choose u v < 0)
    (u q : Icc 0 U) (hr : x.1 u v 0 = x.1 q v 0) : u = q :=
  (hx.radial_strictAnti hx.choose hz hd v hν).injective hr

example (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ∈ Ioo 0 U) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hν : radialNuField hV e Λ z x.1 hx.choose u v = -2) (hlam : x.2.1 u v 0 = -3) :
    ∃ ψ : ℝ → ℝ, ψ v = u ∧ HasDerivAt ψ (-3 / 2) v ∧
      ∀ᶠ t in 𝓝 (v : ℝ), ψ t ∈ Ioo 0 U ∧ t ∈ Ioo 0 V ∧
        intervalExtension hV (intervalExtension hU x.1 (ψ t)) t 0 = x.1 u v 0 := by
  have hν0 : radialNuField hV e Λ z x.1 hx.choose u v ≠ 0 := by rw [hν]; norm_num
  obtain ⟨ψ, hψ, hD, hg⟩ := hx.exists_radial_level_chart hx.choose hz hd u v hu hv hν0
  rw [hν, hlam] at hD
  norm_num at hD
  exact ⟨ψ, hψ, by simpa only [neg_div] using hD.hasDerivAt, hg⟩

example (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ∈ Ioo 0 U) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hν : radialNuField hV e Λ z x.1 hx.choose u v < 0) (hlam : x.2.1 u v 0 < 0) :
    ∃ ψ : ℝ → ℝ, ψ v = u ∧ ContinuousAt ψ v ∧ deriv ψ v < 0 := by
  obtain ⟨ψ, hψ, hD, _hg⟩ := hx.exists_radial_level_chart hx.choose hz hd u v hu hv hν.ne
  have hD := hD.hasDerivAt
  refine ⟨ψ, hψ, hD.continuousAt, ?_⟩
  rw [hD.deriv]
  exact div_neg_of_pos_of_neg (neg_pos.2 hlam) hν

end ActualRadialLevels

section PhysicalOuterLevel

variable (B : Background) {s H dH c A : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s) (hA : 0 ≤ A)

include hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA

example (hcp : c ≤ B.outerRate * (3 / 4)) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y T j J τ : ℝ, 0 < δ ∧ Y ∈ Ioo B.inner B.event ∧ 0 ≤ T ∧ 0 < j ∧ 0 < τ ∧
      ∀ (V : ℝ) (hV : 0 ≤ V), T ≤ V →
      ∀ (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 (δ * Real.exp (-B.outerRate * V))))),
        (eLpNorm f 4 (volume.restrict (Icc 0 (δ * Real.exp (-B.outerRate * V))))).toReal ≤ A →
        ∃ (hU : 0 ≤ δ * Real.exp (-B.outerRate * V)) (hUR : δ * Real.exp (-B.outerRate * V) < r 0)
          (x : WaveState (δ * Real.exp (-B.outerRate * V)) V),
          IsWaveIntegral hU hV B.charge B.cosmological (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x ∧
          ∃ u : Icc 0 (δ * Real.exp (-B.outerRate * V)),
            x.1 u ⟨V, hV, le_rfl⟩ 0 = Y ∧ 0 < (u : ℝ) ∧ (u : ℝ) < δ * Real.exp (-B.outerRate * V) ∧
            j ≤ u * Real.exp (B.outerRate * V) ∧ u * Real.exp (B.outerRate * V) ≤ J ∧
            x.2.1 u ⟨V, hV, le_rfl⟩ 0 ≤ -τ := by
  obtain ⟨δ, Y, T, j, J, n₀, N₀, τ, L, hδ, hδr, hY, hT, hj, _hJ, _hJδ, _hn, _hN, hτ, _hL, hsolve⟩ :=
    B.exists_outer_level_prefix hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  refine ⟨δ, Y, T, j, J, τ, hδ, hY, hT, hj, hτ, ?_⟩
  intro V hV hTV f hf hfn
  let U := δ * Real.exp (-B.outerRate * V)
  have hU : 0 ≤ U := mul_nonneg hδ.le (Real.exp_pos _).le
  have hUδ : U ≤ δ := mul_le_of_le_one_right hδ.le
    (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 B.outerRate_pos.le) hV))
  have hrp : 0 < r 0 := (sub_pos.2 hdHR).trans_le (hrb 0)
  have hUR : U < r 0 := hUδ.trans_lt (hδr.trans_lt (by linarith only [hrp]))
  have hw : U * Real.exp (B.outerRate * V) = δ := by
    dsimp only [U]
    rw [mul_assoc, ← Real.exp_add, show -B.outerRate * V + B.outerRate * V = 0 by ring, Real.exp_zero, mul_one]
  have hcb : c ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by norm_num; exact hcp
  obtain ⟨x, ⟨hx, hg⟩, _⟩ := hsolve U V hU hV hUR 4 le_rfl f hf hfn hcb hw.le
  obtain ⟨⟨u, hu, _hun⟩, hub⟩ := hg ⟨V, hV, le_rfl⟩ hTV (by change δ / 2 ≤ U * Real.exp (B.outerRate * V); rw [hw]; linarith only [hδ])
  obtain ⟨hup, huU, hjb, hJb, _hnb, _hNb, htb, _hLb, _hchart⟩ := hub u hu
  exact ⟨hU, hUR, x, hx, u, hu, hup, huU, hjb, hJb, by linarith only [htb]⟩

example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y T b C : ℝ, 0 < δ ∧ Y ∈ Ioo B.inner B.event ∧ 0 ≤ T ∧ 0 < b ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f ∞ (volume.restrict (Icc 0 U))),
        (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ≤ A → U * Real.exp (B.outerRate * V) ≤ δ →
        ∃ (x : WaveState U V) (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x),
          ∀ (v : Icc 0 V), (v : ℝ) ∈ Ioo 0 V → T ≤ (v : ℝ) → δ / 2 ≤ U * Real.exp (B.outerRate * v) →
            ∃ (u : Icc 0 U) (ψ : ℝ → ℝ),
              x.1 u v 0 = Y ∧ ψ v = u ∧ DifferentiableAt ℝ ψ v ∧
              (-radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose u v) * (-deriv ψ v) = -x.2.1 u v 0 ∧
              b ≤ -deriv ψ v / u ∧ -deriv ψ v / u ≤ C ∧
              ∀ᶠ t in 𝓝 (v : ℝ), ψ t ∈ Ioo 0 U ∧ t ∈ Ioo 0 V ∧
                intervalExtension hV (intervalExtension hU x.1 (ψ t)) t 0 = Y := by
  obtain ⟨δ, Y, T, j, J, n₀, N₀, τ, L, hδ, _hδr, hY, hT, _hj, _hJ, _hJδ, _hn, hN, hτ, _hL, hsolve⟩ :=
    B.exists_outer_level_prefix hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  refine ⟨δ, Y, T, τ / N₀, L / n₀, hδ, hY, hT, div_pos hτ hN, ?_⟩
  intro U V hU hV hUR f hf hfn hw
  have hcb : c ≤ B.outerRate * (1 - 1 / (∞ : ℝ≥0∞).toReal) := by simpa using hca.le
  obtain ⟨x, ⟨hx, hg⟩, _⟩ := hsolve U V hU hV hUR ∞ le_top f hf hfn hcb hw
  refine ⟨x, hx, ?_⟩
  intro v hvint hv hwv
  obtain ⟨⟨u, hu, _hun⟩, hub⟩ := hg v hv hwv
  obtain ⟨_hup, _huU, _hjb, _hJb, _hnb, _hNb, _htb, _hLb, hchart⟩ := hub u hu
  obtain ⟨ψ, hψ, hD, hJac, hlow, hhigh, hgraph⟩ := hchart hvint
  exact ⟨u, ψ, hu, hψ, hD.differentiableAt, hJac, hlow, hhigh, hgraph⟩

end PhysicalOuterLevel

example {a δ t : ℝ} (ha : 0 < a) (hδ : 0 < δ) (ht : 0 < t) :
    let V := t + Real.log (4 / 3 : ℝ) / a
    let U := δ * Real.exp (-a * V)
    0 < t ∧ t < V ∧ U * Real.exp (a * V) = δ ∧ δ / 2 < U * Real.exp (a * t) := by
  let V := t + Real.log (4 / 3 : ℝ) / a
  let U := δ * Real.exp (-a * V)
  have hV : t < V := lt_add_of_pos_right _ (div_pos (Real.log_pos (by norm_num)) ha)
  have htop : U * Real.exp (a * V) = δ := by
    dsimp only [U]
    rw [mul_assoc, ← Real.exp_add, show -a * V + a * V = 0 by ring, Real.exp_zero, mul_one]
  refine ⟨ht, hV, htop, ?_⟩
  have he : -a * V + a * t = -Real.log (4 / 3 : ℝ) := by dsimp only [V]; field_simp; ring
  change δ / 2 < δ * Real.exp (-a * V) * Real.exp (a * t)
  rw [mul_assoc, ← Real.exp_add, he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
  norm_num
  linarith only [hδ]

section NonnestedPhysicalOverlap

variable {M e Λ : ℝ} {h r : ℝ → ℝ} (hR : 3 < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  {f : ℝ → ℝ} (hf2 : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 2)))
  (hf3 : MemLp f 4 (volume.restrict (Icc (0 : ℝ) 3))) {x : WaveState 2 3} {y : WaveState 3 2}
  (hx : IsWaveIntegral (by norm_num) (by norm_num) e Λ
    (incomingWaveCurve (by norm_num) (by linarith : (2 : ℝ) < r 0) le_rfl hf2 (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ 3 hc hi hrc hr0) (incomingWaveVelocity (by linarith : (2 : ℝ) < r 0) le_rfl hf2) x)
  (hy : IsWaveIntegral (by norm_num) (by norm_num) e Λ
    (incomingWaveCurve (by norm_num) hR le_rfl hf3 (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ 2 hc hi hrc hr0) (incomingWaveVelocity hR le_rfl hf3) y)

example : x.1 ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = y.1 ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ ∧
    x.2.1 ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ = y.2.1 ⟨2, by norm_num⟩ ⟨2, by norm_num⟩ :=
  hx.horizon_overlap (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num) hR
    hc hi hrc hr0 le_rfl hf2 hf3 hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : x.1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = y.1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ :=
  (hx.horizon_overlap (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num) hR
    hc hi hrc hr0 le_rfl hf2 hf3 hy (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

end NonnestedPhysicalOverlap

example : ∃ v : ℝ → ℝ, ContinuousOn v (Ioo 0 (Real.exp (-1))) ∧
    Tendsto v (𝓝[>] (0 : ℝ)) atTop ∧
    ∀ u ∈ Ioo 0 (Real.exp (-1)), 1 < v u ∧ Real.exp (-v u) = u ∧ HasDerivAt v (-1 / u) u := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
    convert ((hasDerivAt_id t).neg.exp) using 1 <;> simp
  have hc : ContinuousOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by fun_prop
  have ha : StrictAntiOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    fun _ _ _ _ h => Real.exp_lt_exp.2 (neg_lt_neg h)
  have hl : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  obtain ⟨v, hcv, hlim, hright, _hleft⟩ := exists_arrival_inverse (t₀ := 1) hc ha hl
    (fun _ _ => Real.exp_pos _) (fun t _ => ⟨(hd t).differentiableAt, by rw [(hd t).deriv]; exact neg_neg_of_pos (Real.exp_pos _)⟩)
    (by norm_num)
  refine ⟨v, hcv, hlim, ?_⟩
  intro u hu
  obtain ⟨ht, he, hv⟩ := hright u hu
  rw [(hd (v u)).deriv, he] at hv
  refine ⟨ht, he, ?_⟩
  simpa only [inv_neg, neg_div, one_div] using hv

section PhysicalAllTimeArrival

variable (B : Background) {s H dH c A : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s) (hc0 : 0 ≤ c) (hca : c < B.outerRate) (hcs : c ≤ s) (hA : 0 ≤ A)

include hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA

example (hcp : c ≤ B.outerRate * (3 / 4)) :
    ∃ δ Y T ε : ℝ, 0 < δ ∧ Y ∈ Ioo B.inner B.event ∧ 0 ≤ T ∧ 0 < ε ∧
      ∀ (f : ℝ → ℝ), MemLp f 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ g inv : ℝ → ℝ, StrictAntiOn g (Ioi T) ∧ Tendsto g atTop (𝓝 0) ∧
          ContinuousOn inv (Ioo 0 ε) ∧ Tendsto inv (𝓝[>] (0 : ℝ)) atTop ∧
          (∀ u ∈ Ioo 0 ε, T + 1 < inv u ∧ g (inv u) = u ∧ HasDerivAt inv (deriv g (inv u))⁻¹ u) ∧
          ∀ t ∈ Ioi (T + 1), inv (g t) = t := by
  obtain ⟨δ, Y, T, j, J, b, C, ε, hδ, _hδr, hY, hT, _hj, _hJ, _hJδ, _hb, _hC, hε, hsolve⟩ :=
    B.exists_outer_arrival hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  refine ⟨δ, Y, T, ε, hδ, hY, hT, hε, ?_⟩
  intro f hf hfn
  have hcb : c ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by norm_num; exact hcp
  obtain ⟨g, inv, _hcg, hag, hlim, hci, hli, hright, hleft, _hphys⟩ := hsolve 4 le_rfl f hf hfn hcb
  exact ⟨g, inv, hag, hlim, hci, hli, hright, hleft⟩

example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y T : ℝ, 0 < δ ∧ Y ∈ Ioo B.inner B.event ∧ 0 ≤ T ∧
      ∀ (f : ℝ → ℝ), MemLp f ∞ (volume.restrict (Icc 0 δ)) →
        (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ g : ℝ → ℝ, ∀ t ∈ Ioi T, ∃ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR le_top hfU) x) (u : Icc 0 U) (v : Icc 0 V),
          (u : ℝ) = g t ∧ (v : ℝ) = t ∧ x.1 u v 0 = Y ∧ DifferentiableAt ℝ g t ∧
          (-radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0)) x.1 hx.choose u v) * (-deriv g t) = -x.2.1 u v 0 := by
  obtain ⟨δ, Y, T, j, J, b, C, ε, hδ, _hδr, hY, hT, _hj, _hJ, _hJδ, _hb, _hC, _hε, hsolve⟩ :=
    B.exists_outer_arrival hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  refine ⟨δ, Y, T, hδ, hY, hT, ?_⟩
  intro f hf hfn
  have hcb : c ≤ B.outerRate * (1 - 1 / (∞ : ℝ≥0∞).toReal) := by simpa using hca.le
  obtain ⟨g, _inv, _hcg, _hag, _hlim, _hci, _hli, _hright, _hleft, hphys⟩ := hsolve ∞ le_top f hf hfn hcb
  refine ⟨g, ?_⟩
  intro t ht
  obtain ⟨_hgpos, _hlo, _hhi, _hslo, _hshi, U, V, hU, hV, hUR, hfU, x, hx, u, v, hu, hv, _hui, _hvi, hrY, _hw, hD, hJac⟩ := hphys t ht
  exact ⟨U, V, hU, hV, hUR, hfU, x, hx, u, v, hu, hv, hrY, hD.differentiableAt, hJac⟩

example : ∃ δ T ε : ℝ, 0 < δ ∧ 0 ≤ T ∧ 0 < ε ∧
    ∀ (f : ℝ → ℝ), MemLp f ∞ (volume.restrict (Icc 0 δ)) →
      (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
      ∃ g : ℝ → ℝ, ∀ u ∈ Ioo 0 ε, ∃! t : ℝ, T < t ∧ g t = u := by
  obtain ⟨δ, _Y, T, _j, _J, _b, _C, ε, hδ, _hδr, _hY, hT, _hj, _hJ, _hJδ, _hb, _hC, hε, hsolve⟩ :=
    B.exists_outer_arrival hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut hc0 hca hcs hA
  refine ⟨δ, T, ε, hδ, hT, hε, ?_⟩
  intro f hf hfn
  have hcb : c ≤ B.outerRate * (1 - 1 / (∞ : ℝ≥0∞).toReal) := by simpa using hca.le
  obtain ⟨g, inv, _hcg, hag, _hlim, _hci, _hli, hright, _hleft, _hphys⟩ := hsolve ∞ le_top f hf hfn hcb
  refine ⟨g, ?_⟩
  intro u hu
  obtain ⟨ht, he, _hd⟩ := hright u hu
  have htT : T < inv u := by linarith only [ht]
  exact ⟨inv u, ⟨htT, he⟩, fun t ht => hag.injOn ht.1 htT (ht.2.trans he.symm)⟩

end PhysicalAllTimeArrival

example (B : Background) {Y R : ℝ} (hY : B.inner < Y) (hYR : Y ≤ R) (hR : R < B.event) :
    ∃ q : ℝ, 0 < q ∧ ∀ r ∈ Icc Y R, ∀ m : ℝ, B.mass ≤ m →
      horizonFunction r m B.charge B.cosmological ≤ -q := by
  obtain ⟨ε, q, hε, hq, hbound⟩ := B.exists_band_margin hY hYR hR
  exact ⟨q, hq, fun r hr m hm => hbound r hr m (by linarith only [hε, hm])⟩

example (B : Background) {Y : ℝ} (hY : Y ∈ Ioo B.inner B.event) :
    ∃ ε q : ℝ, 0 < ε ∧ 0 < q ∧ ∀ m : ℝ, B.mass - ε ≤ m →
      horizonFunction Y m B.charge B.cosmological ≤ -q := by
  obtain ⟨ε, q, hε, hq, hbound⟩ := B.exists_band_margin hY.1 le_rfl hY.2
  exact ⟨ε, q, hε, hq, fun m hm => hbound Y ⟨le_rfl, le_rfl⟩ m hm⟩

section SegmentFlux

variable {U V e Λ : ℝ} {hV : 0 ≤ V} {zIn : C(Icc 0 U, WaveVector)} {x : WaveState U V}
  (hr : ∀ u v, x.1 u v 0 ≠ 0) (hrp : ∀ u v, 0 < x.1 u v 0)
  (hnu : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v < 0)

example (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b)
    (hP : ∀ w ∈ Icc a b, radialPotential (x.1 u w 0) e Λ = 0)
    (hκ : ∀ w ∈ Icc a b, -Real.exp (x.1 u w 2) / (4 * radialNuField hV e Λ zIn x.1 hr u w) ≤ 1) :
    x.1 u b 0 * radialNuField hV e Λ zIn x.1 hr u b =
      x.1 u a 0 * radialNuField hV e Λ zIn x.1 hr u a := by
  have hh := radialNuField_flux_segment_bound hr hrp hnu u a b hab
    (P := 0) (fun w hw => by rw [hP w hw, abs_zero]) hκ
  simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero, one_mul] at hh
  nlinarith only [hh.1, hh.2]

example (u : Icc 0 U) (a : Icc 0 V) {P : ℝ}
    (hP : |radialPotential (x.1 u a 0) e Λ| ≤ P)
    (hκ : -Real.exp (x.1 u a 2) / (4 * radialNuField hV e Λ zIn x.1 hr u a) ≤ 1) :
    let W := x.1 u a 0 * (-radialNuField hV e Λ zIn x.1 hr u a)
    Real.exp (-(4 * P) * ((a : ℝ) - a)) * W ≤ W ∧ W ≤ Real.exp (4 * P * ((a : ℝ) - a)) * W := by
  exact radialNuField_flux_segment_bound hr hrp hnu u a a le_rfl
    (fun w hw => by have he : w = a := le_antisymm hw.2 hw.1; simpa only [he] using hP)
    (fun w hw => by have he : w = a := le_antisymm hw.2 hw.1; simpa only [he] using hκ)

end SegmentFlux

section PhysicalBand

variable (B : Background) {Y R U V : ℝ} {h r : ℝ → ℝ}
  (hY : B.inner < Y) (hYR : Y < R) (hR : R < B.event)
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
  {x : WaveState U V}
  (hx : IsWaveIntegral hU hV B.charge B.cosmological
    (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
    (incomingWaveVelocity hUR hp hf) x)

include hY hYR hR hφ hrd hx

example : ∃ ε l d c C : ℝ, 0 < ε ∧ 0 < l ∧ 0 < d ∧ 0 < c ∧ 0 < C ∧
    let N := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField B.charge B.cosmological x.1 x.2.1 N hx.choose
    ∀ (u : Icc 0 U) (a b : Icc 0 V), a ≤ b →
      (∀ w ∈ Icc a b, x.1 u w 0 ∈ Icc Y R) →
      (∀ w ∈ Icc a b, 1 / 2 ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) →
      B.mass - ε ≤ m u a →
      (∀ w ∈ Icc a b, l ≤ -x.2.1 u w 0) ∧ (b : ℝ) - a ≤ d ∧
      ∀ n₀ N₀ : ℝ, n₀ ≤ (u : ℝ) * (-N u a) → (u : ℝ) * (-N u a) ≤ N₀ →
        c * n₀ ≤ (u : ℝ) * (-N u b) ∧ (u : ℝ) * (-N u b) ≤ C * N₀ := by
  obtain ⟨ε, q, P, hε, hq, _hP, hsolve⟩ := B.exists_band_geometry hY hYR.le hR
  let d := (R - Y) / ((1 / 2) * q)
  let c := (Y / R) * Real.exp (-(4 * P) * d)
  let C := (R / Y) * Real.exp (4 * P * d)
  have hY0 : 0 < Y := B.inner_pos.trans hY
  have hR0 : 0 < R := hY0.trans hYR
  have hc0 : 0 < c := mul_pos (div_pos hY0 hR0) (Real.exp_pos _)
  have hC0 : 0 < C := mul_pos (div_pos hR0 hY0) (Real.exp_pos _)
  refine ⟨ε, (1 / 2) * q, d, c, C, hε, by positivity, div_pos (sub_pos.2 hYR) (by positivity), hc0, hC0, ?_⟩
  dsimp only
  intro u a b hab hrange hk hm
  obtain ⟨hl, ht, hlo, hhi⟩ := hsolve hU hV hUR hc hi hrc hr0 hφ hrd hp hf hx u a b hab
    (1 / 2) (by norm_num) hrange hk hm
  refine ⟨hl, ht, ?_⟩
  intro n₀ N₀ hn hN
  exact ⟨(mul_le_mul_of_nonneg_left hn hc0.le).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_left hN hC0.le)⟩

example (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0) :
    x.2.1 u b 0 < 0 ∧ x.1 u b 0 ≤ x.1 u a 0 :=
  hx.outgoing_trapped_radius hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha

-- The actual flux gives both exponential factors, without a small-energy premise.
example (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0) :
    let S := fun t => intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)
    let J := ∫ t in (a : ℝ)..b, S t
    let q := fun v => Real.exp (x.1 u v 2) / (4 * (-x.2.1 u v 0))
    IntervalIntegrable S volume a b ∧ 0 ≤ J ∧ q b = q a * Real.exp (-J) ∧
      q b ≤ q a ∧ -x.2.1 u b 0 = -x.2.1 u a 0 * Real.exp (x.1 u b 2 - x.1 u a 2 + J) := by
  obtain ⟨hJi, hJ0, heq, _hpos, hanti, hfactor⟩ :=
    hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a b hab ha
  exact ⟨hJi, hJ0, heq, hanti, hfactor⟩

-- Coincident endpoints require no open time interval or strict a < b hypothesis.
example (u : Icc 0 U) (a : Icc 0 V) (ha : x.2.1 u a 0 < 0) :
    0 < Real.exp (x.1 u a 2) / (4 * (-x.2.1 u a 0)) ∧
      (∫ t in (a : ℝ)..a, intervalExtension hV (x.1 u) t 0 *
        (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) = 0 := by
  have hh := hx.trapped_q_transport hU hV hUR hc hi hrc hr0 hφ hrd hp hf u a a le_rfl ha
  exact ⟨hh.2.2.2.1, intervalIntegral.integral_same⟩

end PhysicalBand

example {U V W e Λ : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W) (hVW : V ≤ W)
    (zIn : C(Icc 0 U, WaveVector)) (z : WaveRectangle U W) (y : WaveRectangle U V)
    (hr : ∀ u v, z u v 0 ≠ 0) (hy : ∀ u v, y u v 0 ≠ 0)
    (he : ∀ u v, y u v = z u ⟨v, v.property.1, v.property.2.trans hVW⟩) (u : Icc 0 U) :
    radialNuField hV e Λ zIn y hy u ⟨V, hV, le_rfl⟩ =
      radialNuField hW e Λ zIn z hr u ⟨V, hV, hVW⟩ :=
  radialNuField_prefix_eq hV hW hVW e Λ zIn z y hr hy he u ⟨V, hV, le_rfl⟩

-- One finite-history width works for both endpoint exponents, without a kappa premise.
example {M e Λ T ρ A : ℝ} {h r : ℝ → ℝ}
    (hT : 0 ≤ T) (hrp : 0 < r 0) (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t) :
    let P := fun (p : ℝ≥0∞) (hp : 4 ≤ p) (δ : ℝ) =>
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ δ → V ≤ T →
        (∀ u v, ρ ≤ x.1 u v 0) → ∀ u v,
          (3 / 4 : ℝ) ≤ -Real.exp (x.1 u v 2) / (4 * radialNuField hV e Λ
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v)
    ∃ δ : ℝ, 0 < δ ∧ P 4 le_rfl δ ∧ P ∞ le_top δ := by
  dsimp only
  obtain ⟨δ, hδ, _hδ1, _hδr, hsolve⟩ := exists_finite_small_width_kappa hT hrp hρ hA
    (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)) hc hi hrc hr0 hφ hrd
  have hexp : Real.exp (-Real.log (4 / 3 : ℝ)) = (3 / 4 : ℝ) := by
    norm_num [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro U V hU hV hUR f hf x hx hfn hUU hVT hlo u v
    simpa only [hexp] using (hsolve U V hU hV hUR 4 le_rfl f hf x hx hfn hUU hVT hlo u v).2
  · intro U V hU hV hUR f hf x hx hfn hUU hVT hlo u v
    simpa only [hexp] using (hsolve U V hU hV hUR ∞ le_top f hf x hx hfn hUU hVT hlo u v).2

-- A zero-height physical rectangle cannot contain the asserted first contact.
example {M e Λ U Y : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U 0}
    (hx : IsWaveIntegral hU le_rfl e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ 0 hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hinit : Y < r 0 - U) : ¬∃ u v, x.1 u v 0 ≤ Y := by
  intro hbad
  obtain ⟨t, ht, _⟩ := hx.exists_first_radius_contact hU le_rfl hUR hc hi hrc hr0 hφ hrd hp hf hinit hbad
  exact ht.not_ge t.property.2

section LateMassAndBand

variable (B : Background) {s H dH A : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

include hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut

example {ε : ℝ} (hε : 0 < ε) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let P := fun (p : ℝ≥0∞) (hp : 4 ≤ p) (U₀ T : ℝ) =>
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ U₀ →
        ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
          let N := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          B.mass - ε ≤ massField B.charge B.cosmological x.1 x.2.1 N hx.choose u v
    ∃ U₀ T : ℝ, 0 < U₀ ∧ 0 ≤ T ∧ P 4 le_rfl U₀ T ∧ P ∞ le_top U₀ T := by
  dsimp only
  obtain ⟨U₀, T, hU₀, _hU₀r, hT, hsolve⟩ :=
    B.exists_late_mass_lower hs hH hdH hdHR hA hε hc hb hrc hrb hrd hrdec hOut
  refine ⟨U₀, T, hU₀, hT, ?_, ?_⟩
  · intro U V hU hV hUR f hf x hx
    exact hsolve U V hU hV hUR 4 le_rfl f hf x hx
  · intro U V hU hV hUR f hf x hx
    exact hsolve U V hU hV hUR ∞ le_top f hf x hx

example {Y R : ℝ} (hY : B.inner < Y) (hYR : Y ≤ R) (hR : R < B.event) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ T : ℝ, 0 < U₀ ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (_hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ U₀ →
        ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) → x.1 u v 0 ∈ Icc Y R → x.2.1 u v 0 < 0 := by
  obtain ⟨U₀, T, q, _P, hU₀, _hU₀r, hT, hq, _hP, hsolve⟩ :=
    B.exists_late_band_geometry hY hYR hR hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  refine ⟨U₀, T, hU₀, hT, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hUU u v hTv hrange
  have hg := hx.interior_gauge hU hV hUR hc (horizon_mass_integrable hs hH hc hb) hrc
    (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
    (horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb) hrd hp hf u v
  obtain ⟨hl, _ht, _hlo, _hhi⟩ := hsolve U V hU hV hUR p hp f hf x hx hfn hUU u v v hTv le_rfl
    _ hg.2.2.2.1 (fun w hw => by have he : w = v := le_antisymm hw.2 hw.1; simpa only [he] using hrange)
    (fun w hw => by have he : w = v := le_antisymm hw.2 hw.1; rw [he])
  have hh := hl v ⟨le_rfl, le_rfl⟩
  have hpos := mul_pos hg.2.2.2.1 hq
  linarith only [hh, hpos]

example {Y R : ℝ} (hY : B.inner < Y) (hYR : Y < R) (hR : R < B.event) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ T d : ℝ, 0 < U₀ ∧ 0 ≤ T ∧ 0 < d ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ U₀ →
        ∀ (u : Icc 0 U) (a b : Icc 0 V), T ≤ (a : ℝ) → a ≤ b →
          (∀ w ∈ Icc a b, x.1 u w 0 ∈ Icc Y R) →
          (∀ w ∈ Icc a b, 1 / 2 ≤ -Real.exp (x.1 u w 2) /
            (4 * radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u w)) →
          (b : ℝ) - a ≤ d := by
  obtain ⟨U₀, T, q, _P, hU₀, _hU₀r, hT, hq, _hP, hsolve⟩ :=
    B.exists_late_band_geometry hY hYR.le hR hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  refine ⟨U₀, T, (R - Y) / ((1 / 2) * q), hU₀, hT,
    div_pos (sub_pos.2 hYR) (by positivity), ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hUU u a b hTa hab hrange hk
  exact (hsolve U V hU hV hUR p hp f hf x hx hfn hUU u a b hTa hab (1 / 2)
    (by norm_num) hrange hk).2.1

example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y U₀ D : ℝ, 0 < δ ∧ B.inner < Y ∧ Y < B.event ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < D ∧
      ∀ (f : ℝ → ℝ), MemLp f ∞ (volume.restrict (Icc 0 δ)) →
        (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR le_top hfU) x),
          U ≤ U₀ → (∀ u v, Y ≤ x.1 u v 0) →
          (∀ u v, (1 / 2 : ℝ) ≤ -Real.exp (x.1 u v 2) /
            (4 * radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0)) x.1 hx.choose u v)) →
          U * Real.exp (B.outerRate * V) ≤ D := by
  obtain ⟨δ, R, hδ, _hδr, hR, hsolve⟩ := B.exists_band_width hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  let Y := (B.inner + R) / 2
  have hY : B.inner < Y := by dsimp only [Y]; linarith only [hR.1]
  have hYR : Y ≤ R := by dsimp only [Y]; linarith only [hR.1]
  obtain ⟨U₀, D, hU₀, hU₀δ, hD, hwide⟩ := hsolve Y hY hYR
  exact ⟨δ, Y, U₀, D, hδ, hY, hYR.trans_lt hR.2, hU₀, hU₀δ, hD,
    fun f hf hfn => hwide ∞ le_top f hf hfn⟩

example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y U₀ T : ℝ, 0 < δ ∧ B.inner < Y ∧ Y < B.event ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ 0 ≤ T ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hfU) x),
          U ≤ U₀ → (∀ u v, Y ≤ x.1 u v 0) →
          (∀ u v, (1 / 2 : ℝ) ≤ -Real.exp (x.1 u v 2) /
            (4 * radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose u v)) →
          T ≤ V → ∀ u : Icc 0 U,
            (1 / 2 : ℝ) < -Real.exp (x.1 u ⟨V, hV, le_rfl⟩ 2) /
              (4 * radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose u ⟨V, hV, le_rfl⟩) := by
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (by linarith only [hs])
  obtain ⟨δ, R, hδ, _hδr, hR, hsolve⟩ := B.exists_band_improvement hs hH hdH hdHR hA hc0 hca hcs
    (Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)) hc hb hrc hrb hrd hrdec hOut
  let Y := (B.inner + R) / 2
  have hY : B.inner < Y := by dsimp only [Y]; linarith only [hR.1]
  have hYR : Y ≤ R := by dsimp only [Y]; linarith only [hR.1]
  obtain ⟨U₀, T, _D, _n, _N, _L, hU₀, hU₀δ, hT, _hD, _hn, _hN, _hL, himprove⟩ := hsolve Y hY hYR
  refine ⟨δ, Y, U₀, T, hδ, hY, hYR.trans_lt hR.2, hU₀, hU₀δ, hT, ?_⟩
  intro p hp f hf hfn U V hU hV hUR hfU x hx hUU hlo hk hTV u
  have hcb : c ≤ B.outerRate * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 B.outerRate_pos.le
    have hcB : c ≤ B.outerRate / 2 := min_le_right _ _
    nlinarith only [hh, hcB, B.outerRate_pos]
  have hbound := ((himprove p hp f hf hfn hcb U V hU hV hUR hfU x hx hUU hlo hk).2.2 hTV u).2.1
  norm_num [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at hbound
  exact (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans_le hbound

-- The positive scalar weight and the width are common to all p, including infinity.
-- No kappa, nu, lambda or exponential-width bound is supplied as a premise.
example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y U₀ D c E : ℝ, 0 < δ ∧ B.inner < Y ∧ Y < B.event ∧
      0 < U₀ ∧ U₀ ≤ δ ∧ 0 < D ∧ 0 < c ∧ 0 ≤ E ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (hfU : MemLp f p (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR hp hfU) x),
          U ≤ U₀ → (∀ u v, Y ≤ x.1 u v 0) →
          U * Real.exp (B.outerRate * V) ≤ D ∧ ∀ u v,
            (3 / 4 : ℝ) ≤ -Real.exp (x.1 u v 2) / (4 * radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) x.1 hx.choose u v) ∧
            |x.2.1 u v 1| ≤ E * Real.exp (-c * v) := by
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (by linarith only [hs])
  obtain ⟨δ, R, hδ, _hδr, hR, hsolve⟩ :=
    B.exists_band_bounds hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  let Y := (B.inner + R) / 2
  have hY : B.inner < Y := by dsimp only [Y]; linarith only [hR.1]
  have hYR : Y ≤ R := by dsimp only [Y]; linarith only [hR.1]
  obtain ⟨U₀, D, _n, _N, _L, E, hU₀, hU₀δ, hD, _hn, _hN, _hL, hE, hbound⟩ := hsolve Y hY hYR
  refine ⟨δ, Y, U₀, D, c, E, hδ, hY, hYR.trans_lt hR.2, hU₀, hU₀δ, hD, hc0, hE, ?_⟩
  intro p hp f hf hfn U V hU hV hUR hfU x hx hUU hlo
  have hcb : c ≤ B.outerRate * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 B.outerRate_pos.le
    have hcB : c ≤ B.outerRate / 2 := min_le_right _ _
    nlinarith only [hh, hcB, B.outerRate_pos]
  have hh := hbound p hp f hf hfn hcb U V hU hV hUR hfU x hx hUU hlo
  exact ⟨hh.1, fun u v => (hh.2.1 u v).2.2.2.2⟩

-- The data radius budget supplies the initial margin, and one width works at both p endpoints.
example (hdHgap : dH < B.event - B.inner) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let P := fun (p : ℝ≥0∞) (hp : 4 ≤ p) (δ Y U₀ D : ℝ) =>
      ∀ (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∀ (U : ℝ) (hU : 0 < U) (hUR : U < r 0) (hfU : MemLp f p (volume.restrict (Icc 0 U))),
          U ≤ U₀ → ∃ T : ℝ, ∃ hT : 0 < T, ∃ x : WaveState U T,
            IsWaveIntegral hU.le hT.le B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) x ∧
            (∀ u v, Y ≤ x.1 u v 0) ∧ x.1 ⟨U, hU.le, le_rfl⟩ ⟨T, hT.le, le_rfl⟩ 0 = Y ∧
            (∀ (u : Icc 0 U) (v : Icc 0 T), (v : ℝ) < T → Y < x.1 u v 0) ∧
            U * Real.exp (B.outerRate * T) ≤ D
    ∃ δ Y U₀ D : ℝ, 0 < δ ∧ B.inner < Y ∧ Y < r 0 ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < D ∧
      P 4 le_rfl δ Y U₀ D ∧ P ∞ le_top δ Y U₀ D := by
  dsimp only
  have hrinit : B.inner < r 0 := by linarith only [hdHgap, hrb 0]
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (by linarith only [hs])
  have hcb (p : ℝ≥0∞) (hp : 4 ≤ p) : c ≤ B.outerRate * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 B.outerRate_pos.le
    have hcB : c ≤ B.outerRate / 2 := min_le_right _ _
    nlinarith only [hh, hcB, B.outerRate_pos]
  obtain ⟨δ, R, hδ, _hδr, hR, hRr, hsolve⟩ :=
    B.exists_band_passage hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨U₀, D, _n, _N, _L, _E, hU₀, hU₀δ, _hU₀1, _hU₀r, hD, _hn, _hN, _hL, _hE, hpass⟩ :=
    hsolve R hR.1 le_rfl
  refine ⟨δ, R, U₀, D, hδ, hR.1, hRr, hU₀, hU₀δ, hD, ?_, ?_⟩
  · intro f hf hfn U hU hUR hfU hUU
    obtain ⟨T, hT, x, hx, hlo, hhit, hbefore, hw, _hg⟩ :=
      hpass 4 le_rfl f hf hfn (hcb 4 le_rfl) U hU hUR hfU hUU
    exact ⟨T, hT, x, hx, hlo, hhit, hbefore, hw⟩
  · intro f hf hfn U hU hUR hfU hUU
    obtain ⟨T, hT, x, hx, hlo, hhit, hbefore, hw, _hg⟩ :=
      hpass ∞ le_top f hf hfn (hcb ∞ le_top) U hU hUR hfU hUU
    exact ⟨T, hT, x, hx, hlo, hhit, hbefore, hw⟩

-- Uniform crossing times and an actual positive-radius extension below the matching level.
example (hdHgap : dH < B.event - B.inner) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y U₀ j D : ℝ, 0 < δ ∧ B.inner < Y ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < j ∧ 0 < D ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∀ (U : ℝ) (hU : 0 < U) (hUR : U < r 0) (hfU : MemLp f p (volume.restrict (Icc 0 U))),
          U ≤ U₀ → ∃ T : ℝ, ∃ hT : 0 < T, ∃ H' : ℝ, ∃ hH' : 0 < H', ∃ z : WaveState U (T + H'),
            IsWaveIntegral hU.le (add_nonneg hT.le hH'.le) B.charge B.cosmological
              (incomingWaveCurve hU.le hUR hp hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological (T + H') hc hi hrc hr0)
              (incomingWaveVelocity hUR hp hfU) z ∧
            z.1 ⟨U, hU.le, le_rfl⟩ ⟨T, hT.le, le_add_of_nonneg_right hH'.le⟩ 0 = Y ∧
            (∀ u v, Y / 2 ≤ z.1 u v 0) ∧
            (∀ v : Icc 0 (T + H'), T < (v : ℝ) → z.1 ⟨U, hU.le, le_rfl⟩ v 0 < Y) ∧
            j ≤ U * Real.exp (B.outerRate * T) ∧ U * Real.exp (B.outerRate * T) ≤ D := by
  dsimp only
  have hrinit : B.inner < r 0 := by linarith only [hdHgap, hrb 0]
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (by linarith only [hs])
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hsolve⟩ :=
    B.exists_band_crossing hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨U₀, j, D, _n, _N, _L, _E, τ, hU₀, hU₀δ, hU₀1, _hU₀r, hj, hD, _hn, _hN, _hL, _hE, hτ, hcross⟩ :=
    hsolve R hR.1 le_rfl
  refine ⟨δ, R, U₀, j, D, hδ, hR.1, hU₀, hU₀δ, hj, hD, ?_⟩
  intro p hp f hf hfn U hU hUR hfU hUU
  have hcb : c ≤ B.outerRate * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 B.outerRate_pos.le
    have hcB : c ≤ B.outerRate / 2 := min_le_right _ _
    nlinarith only [hh, hcB, B.outerRate_pos]
  obtain ⟨T, hT, x, hx, hlo, hhit, _hbefore, hjT, hDT, _hnlo, _hnhi, hlam, _hg⟩ :=
    hcross p hp f hf hfn hcb U hU hUR hfU hUU
  have hneg : x.2.1 ⟨U, hU.le, le_rfl⟩ ⟨T, hT.le, le_rfl⟩ 0 < 0 := by linarith only [hlam, hτ]
  obtain ⟨H', hH', z, hz, _hmatch, hfloor, hbelow⟩ := hx.extend_past_trapped_level hU.le hT.le
    (hUU.trans hU₀1) hUR (B.inner_pos.trans hR.1) hA hc (horizon_mass_integrable hs hH hc hb) hrc
    (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne')
    (horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb) hrd hp hfU
    ((scalar_prefix_norm_le (hUU.trans hU₀δ) hf).trans hfn) hlo hhit hneg
  have he := hz.horizon_overlap hU.le (add_nonneg hT.le hH'.le) hUR hU.le hT.le hUR hc
    (horizon_mass_integrable hs hH hc hb) hrc (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne') hp hfU hfU hx
    ⟨hU.le, le_rfl⟩ ⟨hU.le, le_rfl⟩ ⟨hT.le, le_add_of_nonneg_right hH'.le⟩ ⟨hT.le, le_rfl⟩
  exact ⟨T, hT, H', hH', z, hz, (congrArg (fun z : WaveVector => z 0) he.1).trans hhit,
    hfloor, hbelow, hjT, hDT⟩

-- The chart is inside an actual larger physical rectangle, with positive uniform speed and exact Jacobian.
example (hdHgap : dH < B.event - B.inner) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y U₀ b C : ℝ, 0 < δ ∧ B.inner < Y ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < b ∧ 0 ≤ C ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∀ (U : ℝ), 0 < U → U < U₀ → ∃ W V : ℝ, ∃ hW : 0 ≤ W, ∃ hV : 0 ≤ V, ∃ hWR : W < r 0,
            ∃ hfW : MemLp f p (volume.restrict (Icc 0 W)), ∃ z : WaveState W V,
            ∃ hz : IsWaveIntegral hW hV B.charge B.cosmological
              (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hWR hp hfW) z,
            ∃ (u : Icc 0 W) (v : Icc 0 V),
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose
            (u : ℝ) = U ∧ (u : ℝ) ∈ Ioo 0 W ∧ (v : ℝ) ∈ Ioo 0 V ∧
            (∀ u v, Y / 2 ≤ z.1 u v 0) ∧ z.1 u v 0 = Y ∧ ∃ ψ : ℝ → ℝ,
              ψ v = u ∧ HasStrictDerivAt ψ (-z.2.1 u v 0 / ν u v) v ∧
              (-ν u v) * (-deriv ψ v) = -z.2.1 u v 0 ∧
              b ≤ -deriv ψ v / u ∧ -deriv ψ v / u ≤ C ∧
              ∀ᶠ t in 𝓝 (v : ℝ), ψ t ∈ Ioo 0 W ∧ t ∈ Ioo 0 V ∧
                intervalExtension hV (intervalExtension hW z.1 (ψ t)) t 0 = Y := by
  dsimp only
  have hrinit : B.inner < r 0 := by linarith only [hdHgap, hrb 0]
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (by linarith only [hs])
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hsolve⟩ :=
    B.exists_band_charts hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨U₀, j, D, n, N, L, _E, τ, hU₀, hU₀δ, hj, hD, hn, hN, hL, _hE, hτ, hcharts⟩ := hsolve R hR.1 le_rfl
  refine ⟨δ, R, U₀, τ / (N * D), L / (n * j), hδ, hR.1, hU₀, hU₀δ, by positivity, by positivity, ?_⟩
  intro p hp f hf hfn U hU hUU
  have hcb : c ≤ B.outerRate * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 B.outerRate_pos.le
    have hcB : c ≤ B.outerRate / 2 := min_le_right _ _
    nlinarith only [hh, hcB, B.outerRate_pos]
  obtain ⟨T, hT, _hjT, _hDT, W, V, hW, hV, hWR, hfW, z, hz, hUW, hTV,
    _hWU₀, hlo, hhit, _hnlo, _hnhi, _hlam, _hL, _hk, _hscalar, _hpre, ψ, hψ, hdψ, hjac, hbnd, hBnd, hgraph⟩ :=
    hcharts p hp f hf hfn hcb U hU hUU
  exact ⟨W, V, hW, hV, hWR, hfW, z, hz, ⟨U, hU.le, hUW.le⟩, ⟨T, hT.le, hTV.le⟩,
    rfl, ⟨hU, hUW⟩, ⟨hT, hTV⟩, hlo, hhit, ψ, hψ, hdψ, hjac, hbnd, hBnd, hgraph⟩

-- A common late-time threshold gives the actual global Jacobian and matching error decay for every p >= 4.
example (hdHgap : dH < B.event - B.inner) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y ε j D b C K γ Cerr : ℝ, 0 < δ ∧ Y ∈ Ioo B.inner B.event ∧ 0 < ε ∧ ε ≤ δ ∧
      0 < j ∧ 0 < D ∧ 0 < b ∧ 0 ≤ C ∧ 0 < K ∧ 0 < γ ∧ 0 ≤ Cerr ∧
      ∀ (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ), MemLp f p (volume.restrict (Icc 0 δ)) →
        (eLpNorm f p (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ arrival g : ℝ → ℝ, Tendsto arrival (𝓝[>] (0 : ℝ)) atTop ∧ Tendsto g atTop (𝓝 0) ∧
          (∀ U ∈ Ioo 0 (ε / 2), g (arrival U) = U) ∧
          ∀ t ∈ Ici K, g t ∈ Ioo 0 (ε / 2) ∧ arrival (g t) = t ∧
            j ≤ g t * Real.exp (B.outerRate * t) ∧ g t * Real.exp (B.outerRate * t) ≤ D ∧
            b ≤ -deriv g t / g t ∧ -deriv g t / g t ≤ C ∧
            ∃ W V : ℝ, ∃ hW : 0 ≤ W, ∃ hV : 0 ≤ V, ∃ hWR : W < r 0,
            ∃ hfW : MemLp f p (volume.restrict (Icc 0 W)), ∃ z : WaveState W V,
            ∃ hz : IsWaveIntegral hW hV B.charge B.cosmological
              (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hWR hp hfW) z,
            ∃ (u : Icc 0 W) (v : Icc 0 V),
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0)) z.1 hz.choose
            (u : ℝ) = g t ∧ (v : ℝ) = t ∧ (u : ℝ) ∈ Ioo 0 W ∧ (v : ℝ) ∈ Ioo 0 V ∧
            z.1 u v 0 = Y ∧ HasStrictDerivAt g (-z.2.1 u v 0 / ν u v) v ∧
            (-ν u v) * (-deriv g v) = -z.2.1 u v 0 ∧
            |(-Real.exp (z.1 u v 2) / (4 * ν u v)) - 1| +
              |massField B.charge B.cosmological z.1 z.2.1 ν hz.choose u v - B.mass| ≤
                Cerr * Real.exp (-γ * (v : ℝ)) := by
  dsimp only
  have hrinit : B.inner < r 0 := by linarith only [hdHgap, hrb 0]
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (by linarith only [hs])
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hsolve⟩ :=
    B.exists_band_arrival hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨ε, j, D, b, C, K, _n, _N, _L, _E, _τ, σ, Cerr,
    hε, hεδ, hj, hD, hb, hC, hK, _hn, _hN, _hL, _hE, _hτ, hσ, hσε, hCerr, hglobal⟩ := hsolve R hR.1 le_rfl
  refine ⟨δ, R, ε, j, D, b, C, K, min B.outerRate (2 * c), Cerr,
    hδ, hR, hε, hεδ, hj, hD, hb, hC, hK, lt_min B.outerRate_pos (mul_pos (by norm_num) hc0), hCerr, ?_⟩
  intro p hp f hf hfn
  have hcb : c ≤ B.outerRate * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 B.outerRate_pos.le
    have hcB : c ≤ B.outerRate / 2 := min_le_right _ _
    nlinarith only [hh, hcB, B.outerRate_pos]
  obtain ⟨arrival, g, _hvc, hva, hvl, htime, htimeσ, _hgc, _hga, hgl, hright, hleft, hphysical⟩ :=
    hglobal p hp f hf hfn hcb
  refine ⟨arrival, g, hvl, hgl, hleft, ?_⟩
  intro t ht
  obtain ⟨hgt, hrt, _hdg, hjt, hDt, hbt, hCt⟩ := hright t (htime.trans_le ht)
  have hU : g t ∈ Ioo 0 ε := ⟨hgt.1, hgt.2.trans (half_lt_self hε)⟩
  have hgtσ : g t ≤ σ := by
    by_contra hnot
    have hh := hva ⟨hσ, hσε.trans (half_lt_self hε)⟩ hU (lt_of_not_ge hnot)
    rw [hrt] at hh
    exact (not_lt_of_ge (htimeσ.le.trans ht)) hh
  obtain ⟨hT, _hjT, _hDT, _hbl, _hCh, W, V, hW, hV, hWR, hfW, z, hz, hUW, hTV,
    _hWε, _hfloor, hhit, _hlam, _hnlo, _hnhi, _hl, _hL, _hk, _hscalar, _hpre, _hda, _hjac, hgd, herr⟩ := hphysical (g t) hU
  exact ⟨hgt, hrt, hjt, hDt, hbt, hCt, W, V, hW, hV, hWR, hfW, z, hz,
    ⟨g t, hU.1.le, hUW.le⟩, ⟨arrival (g t), hT.le, hTV.le⟩,
    rfl, hrt, ⟨hU.1, hUW⟩, ⟨hT, hTV⟩, hhit, (hgd hgt.2).1, (hgd hgt.2).2, herr hgtσ⟩

-- The quantitative prefix estimate includes p=infinity and both zero-coordinate boundaries.
example {ρ D : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ B.event + dH) (hD : 0 ≤ D) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ C γ : ℝ, 0 < U₀ ∧ 0 ≤ C ∧ 0 < γ ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_top hf) x),
        (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ U₀ →
        (∀ u v, ρ ≤ x.1 u v 0) → U * Real.exp (B.outerRate * V) ≤ D → ∀ u : Icc 0 U,
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
          let v : Icc 0 V := ⟨V, hV, le_rfl⟩
          |(-Real.exp (x.1 u v 2) / (4 * ν u v)) - 1| +
            |massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v - B.mass| ≤ C * Real.exp (-γ * V) := by
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (by linarith only [hs])
  obtain ⟨U₀, C, hU₀, _hU₀r, hC, hsolve⟩ := B.exists_bounded_width_feedback_decay
    hs hH hdH hdHR hA hρ hρR hD hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  refine ⟨U₀, C, min B.outerRate (2 * c), hU₀, hC, lt_min B.outerRate_pos (mul_pos (by norm_num) hc0), ?_⟩
  intro U V hU hV hUR f hf x hx hfn hUU hlo hwidth u
  exact hsolve U V hU hV hUR ∞ le_top f hf x hx hfn
    (by simpa only [ENNReal.toReal_top, div_zero, sub_zero, mul_one] using hca.le) hUU hlo hwidth u

-- One conformal decay constant works for every p>=4, retaining the requested rate c.
example {ρ D c : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ B.event + dH) (hD : 0 ≤ D)
    (hc0 : 0 < c) (hca : c ≤ (3 / 4) * B.outerRate) (hcs : c ≤ s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ C : ℝ, 0 < U₀ ∧ 0 ≤ C ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A → U ≤ U₀ →
        (∀ u v, ρ ≤ x.1 u v 0) → U * Real.exp (B.outerRate * V) ≤ D → ∀ u : Icc 0 U,
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
          let v : Icc 0 V := ⟨V, hV, le_rfl⟩
          |x.2.1 u v 2 - 2 * horizonK (x.1 u v 0)
            (massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v) B.charge B.cosmological| ≤
              C * Real.exp (-(min B.outerRate (2 * c)) * V) := by
  obtain ⟨U₀, C, hU₀, _hU₀r, hC, hsolve⟩ := B.exists_bounded_width_conformal_decay
    hs hH hdH hdHR hA hρ hρR hD hc0 (by linarith only [hca, B.outerRate_pos]) hcs
    hc hb hrc hrb hrd hrdec hOut
  refine ⟨U₀, C, hU₀, hC, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hUU hlo hwidth u
  have hcb : c ≤ B.outerRate * (1 - 1 / p.toReal) := by
    have hh := mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 B.outerRate_pos.le
    exact hca.trans (by simpa only [mul_comm B.outerRate] using hh)
  exact hsolve U V hU hV hUR p hp f hf x hx hfn hcb hUU hlo hwidth u

-- At p=infinity, the same constants apply in any later physical rectangle, with no nesting premise.
example (hdHgap : dH < B.event - B.inner) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ ε C : ℝ, 0 < δ ∧ 0 < ε ∧ ε ≤ δ ∧ 0 < C ∧
      ∀ (f : ℝ → ℝ), MemLp f ∞ (volume.restrict (Icc 0 δ)) →
        (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ arrival : ℝ → ℝ, Tendsto arrival (𝓝[>] (0 : ℝ)) atTop ∧
          ∀ u ∈ Ioo 0 ε, ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V),
            IsWaveIntegral hU hV B.charge B.cosmological
              (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR le_top hfU) x →
            ∀ (huU : u ∈ Icc 0 U), arrival u ≤ V →
              ∀ v : Icc 0 V, arrival u ≤ (v : ℝ) →
                x.2.1 ⟨u, huU⟩ v 0 < 0 ∧
                Real.exp (x.1 ⟨u, huU⟩ v 2) / (4 * (-x.2.1 ⟨u, huU⟩ v 0)) ≤ C / u ∧
                Real.exp (x.1 ⟨u, huU⟩ v 2) ≤ (4 * C / u) * (-x.2.1 ⟨u, huU⟩ v 0) := by
  have hrinit : B.inner < r 0 := by linarith only [hdHgap, hrb 0]
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (by linarith only [hs])
  obtain ⟨δ, R, hδ, _hδr, hR, hsolve⟩ :=
    B.exists_matching_q_control hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨ε, _cq, C, hε, hεδ, _hcq, hC, hdata⟩ := hsolve R hR.1 le_rfl
  refine ⟨δ, ε, C, hδ, hε, hεδ, hC, ?_⟩
  intro f hf hfn
  obtain ⟨arrival, _hac, _haa, hal, hphysical⟩ := hdata ∞ le_top f hf hfn
    (by simpa only [ENNReal.toReal_top, div_zero, sub_zero, mul_one] using hca.le)
  refine ⟨arrival, hal, ?_⟩
  intro u hu U V hU hV hUR hfU x hx huU htV v htv
  obtain ⟨_hhit, _hqlo, _hqhi, htail⟩ := (hphysical u hu).2 U V hU hV hUR hfU x hx huU
    ⟨(hphysical u hu).1.le, htV⟩
  obtain ⟨hl, _hr, _hqpos, hq, he⟩ := htail v htv
  exact ⟨hl, hq, he⟩

end LateMassAndBand

-- Trapped crossings of the same level agree without nesting or a first-contact premise.
example {M e Λ A B U V u t s Y : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hfA : MemLp f p (volume.restrict (Icc 0 A))) (hfU : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState A B} {y : WaveState U V}
    (hx : IsWaveIntegral hA hB e Λ (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ B hc hi hrc hr0) (incomingWaveVelocity hAR hp hfA) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hfU) y)
    (huA : u ∈ Icc 0 A) (huU : u ∈ Icc 0 U) (htB : t ∈ Icc 0 B) (hsV : s ∈ Icc 0 V)
    (hxt : x.1 ⟨u, huA⟩ ⟨t, htB⟩ 0 = Y) (hys : y.1 ⟨u, huU⟩ ⟨s, hsV⟩ 0 = Y)
    (hlt : x.2.1 ⟨u, huA⟩ ⟨t, htB⟩ 0 < 0) (hls : y.2.1 ⟨u, huU⟩ ⟨s, hsV⟩ 0 < 0) : t = s :=
  hx.trapped_level_time_unique hA hB hAR hU hV hUR hc hi hrc hr0 hφ hrd hp hfA hfU hy
    huA huU htB hsV hxt hys hlt hls

-- The exact recovered-nu comparison transfers the physical kappa on arbitrary overlaps.
example {M e Λ A B U V u v : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hfA : MemLp f p (volume.restrict (Icc 0 A))) (hfU : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState A B} {y : WaveState U V}
    (hx : IsWaveIntegral hA hB e Λ (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ B hc hi hrc hr0) (incomingWaveVelocity hAR hp hfA) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hfU) y)
    (huA : u ∈ Icc 0 A) (huU : u ∈ Icc 0 U) (hvB : v ∈ Icc 0 B) (hvV : v ∈ Icc 0 V) :
    -Real.exp (x.1 ⟨u, huA⟩ ⟨v, hvB⟩ 2) / (4 * radialNuField hB e Λ
      (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0)) x.1 hx.choose ⟨u, huA⟩ ⟨v, hvB⟩) =
    -Real.exp (y.1 ⟨u, huU⟩ ⟨v, hvV⟩ 2) / (4 * radialNuField hV e Λ
      (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0)) y.1 hy.choose ⟨u, huU⟩ ⟨v, hvV⟩) := by
  rw [(hx.horizon_overlap hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy huA huU hvB hvV).1,
    hx.horizon_overlap_nu hA hB hAR hU hV hUR hc hi hrc hr0 hp hfA hfU hy huA huU hvB hvV]

-- Equal-width first-contact witnesses agree even when their terminal times were chosen independently.
example {M e Λ U V S Y : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hS : 0 ≤ S) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState U V} {y : WaveState U S}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hy : IsWaveIntegral hU hS e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ S hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) y)
    (hxhit : x.1 ⟨U, hU, le_rfl⟩ ⟨V, hV, le_rfl⟩ 0 = Y)
    (hyhit : y.1 ⟨U, hU, le_rfl⟩ ⟨S, hS, le_rfl⟩ 0 = Y)
    (hxfirst : ∀ (u : Icc 0 U) (v : Icc 0 V), (v : ℝ) < V → Y < x.1 u v 0)
    (hyfirst : ∀ (u : Icc 0 U) (v : Icc 0 S), (v : ℝ) < S → Y < y.1 u v 0) : V = S := by
  exact le_antisymm
    (hx.first_contact_time_order hU hV hUR hU hS hUR le_rfl hc hi hrc hr0 hφ hrd hp hf hf hy hxhit hxfirst hyhit).1
    (hy.first_contact_time_order hU hS hUR hU hV hUR le_rfl hc hi hrc hr0 hφ hrd hp hf hf hx hyhit hyfirst hxhit).1

-- Ordered widths force the reverse strict time order; no nested-rectangle hypothesis is used.
example {M e Λ U V W S Y : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hW : 0 ≤ W) (hS : 0 ≤ S) (hWR : W < r 0) (hWU : W < U)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hfU : MemLp f p (volume.restrict (Icc 0 U))) (hfW : MemLp f p (volume.restrict (Icc 0 W)))
    {x : WaveState U V} {y : WaveState W S}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hfU) x)
    (hy : IsWaveIntegral hW hS e Λ (incomingWaveCurve hW hWR hp hfW (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ S hc hi hrc hr0) (incomingWaveVelocity hWR hp hfW) y)
    (hxhit : x.1 ⟨U, hU, le_rfl⟩ ⟨V, hV, le_rfl⟩ 0 = Y)
    (hxfirst : ∀ (u : Icc 0 U) (v : Icc 0 V), (v : ℝ) < V → Y < x.1 u v 0)
    (hyhit : y.1 ⟨W, hW, le_rfl⟩ ⟨S, hS, le_rfl⟩ 0 = Y) : V < S :=
  (hx.first_contact_time_order hU hV hUR hW hS hWR hWU.le hc hi hrc hr0 hφ hrd hp hfU hfW hy hxhit hxfirst hyhit).2 hWU

section WeightedScalar

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
  {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
  (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)

example (hlo : ∀ u v, 1 ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ 1)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ Real.exp v)
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ 1)
    (hout : ∀ v : Icc 0 V, |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| ≤ 1)
    (hinput : (∫ t in (0 : ℝ)..U, |uIn t 1|) ≤ 1)
    (hwidth : U * Real.exp V ≤ 2) (u : Icc 0 U) (v : Icc 0 V) :
    |x.2.1 u v 1| ≤ 2 * Real.exp 2 := by
  have hs := hx.weighted_scalar_bound hr hzin hinu
    (a := 1) (c := 0) (ρ := 1) (R := 1) (N := 1) (L := 1) (H := 1) (J := 1) (δ := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hlo hin
    (by simpa only [one_mul] using hν) hlam (by simpa using hout)
    (by simpa using hinput) (by simpa only [one_mul] using hwidth)
  convert hs.1 u v using 1
  norm_num

example {a c ρ R N L δ : ℝ} (hc : 0 ≤ c) (hac : c < a) (hρ : 0 < ρ)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ L)
    (hout : ∀ v : Icc 0 V, Real.exp (c * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 1| ≤ 0)
    (hinput : Real.exp (c * V) * (∫ t in (0 : ℝ)..U, |uIn t 1|) ≤ 0)
    (hwidth : U * Real.exp (a * V) ≤ δ) (u : Icc 0 U) (v : Icc 0 V) : x.2.1 u v 1 = 0 := by
  have hs := hx.weighted_scalar_bound hr hzin hinu hc hac hρ hR hN hL le_rfl le_rfl
    hlo hin hν hlam hout hinput hwidth
  simpa using hs.1 u v

end WeightedScalar

example {M e Λ a c ρ R n N L H A δ : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (hc0 : 0 < c) (hca : c ≤ (3 / 4) * a) (ha : 0 < a)
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hn : 0 < n) (hN : 0 ≤ N)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
      (x : WaveState U V)
      (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x),
      (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
      (∀ u v, ρ ≤ x.1 u v 0) → (∀ u v, x.1 u v 0 ≤ R) →
      (∀ u (v : Icc 0 V), n * Real.exp (a * v) ≤ -radialNuField hV e Λ
        (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose u v) →
      (∀ u v, |radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        x.1 hx.choose u v| ≤ N * Real.exp (a * v)) →
      (∀ u v, |x.2.1 u v 0| ≤ L) → (∀ v : Icc 0 V, Real.exp (c * v) * |h v| ≤ H) →
      U * Real.exp (a * V) ≤ δ → T ≤ V → ∀ u : Icc 0 U,
        let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
        let v : Icc 0 V := ⟨V, hV, le_rfl⟩
        3 / 4 ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) ∧
        |massField e Λ x.1 x.2.1 ν hx.choose u v - horizonMass M h V| ≤ R * L / 6 := by
  have hη : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨T, hT, hsolve⟩ := exists_late_weighted_feedback hc hi hrc hr0 hφ hrd hc0
    (by linarith only [hca, ha] : c < a) hρ hR hn hN hL hH hA hδ hη
  refine ⟨T, hT, ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn hlo hrhi hnlo hnhi hlam hout hwidth hTV u
  have hcb : c ≤ a * (1 - 1 / p.toReal) :=
    hca.trans (by simpa only [mul_comm a] using mul_le_mul_of_nonneg_left (incoming_exponent_bounds hp).1 ha.le)
  have hb := (hsolve U V hU hV hUR p hp f hf x hx hfn hcb hlo hrhi hnlo hnhi hlam hout hwidth hTV u).2
  norm_num [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at hb
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  ring

section InnerTransport

variable {M e Λ : ℝ} {h r : ℝ → ℝ}
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)

example {U V k d : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0) (hk0 : 0 < k)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let K := fun w => horizonK (x.1 u w 0) (massField e Λ x.1 x.2.1 N hx.choose u w) e Λ
    (∀ w ∈ Icc a b, 1 / 2 ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) →
    (∀ w ∈ Icc a b, |K w + k| ≤ k / 4) →
    (∀ w ∈ Icc a b, |x.2.1 u w 2 - 2 * K w| ≤ d) →
      -N u b ≤ (-N u a) * Real.exp (-((3 / 4) * k) * ((b : ℝ) - a)) := by
  dsimp only
  intro hk hK herr
  have hh := (hx.inner_segment_transport hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
    (by norm_num : (0 : ℝ) < 1 / 2) (by positivity : 0 ≤ k / 4) (by linarith only [hk0] : k / 4 < k)
    u a b hab ha hk hK herr).1.2
  rw [show (2 : ℝ) * (1 / 2) * (k - k / 4) = (3 / 4) * k by ring] at hh
  exact hh

-- No longitudinal radiation means no outgoing mass gain, even for bounded rough data.
example {U V κ₀ R : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0) (hκ₀ : 0 < κ₀)
    {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0)
    (hRa : x.1 u a 0 ≤ R) (hz : ∀ w ∈ Icc a b, x.2.1 u w 1 = 0) :
    let N := radialNuField hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField e Λ x.1 x.2.1 N hx.choose
    (∀ w ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) → m u b = m u a := by
  dsimp only
  intro hk
  have hh := hx.trapped_mass_increment_bound hU hV hUR hc hi hrc hr0 hφ hrd le_top hf
    hκ₀ (H := 0) le_rfl (c := 0) le_rfl u a b hab ha hRa (fun w hw => by simp [hz w hw]) hk
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div, zero_mul] at hh
  exact sub_eq_zero.mp (hh.2.antisymm hh.1)

-- A strict exponent margin chooses the small-flux time before all rectangles and incoming data.
example {k ε d κ₀ R H c β l τ : ℝ}
    (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k) (hH : 0 ≤ H) (hl : 0 < l) (hτ : 0 < τ)
    (hmargin : 0 < 2 * c - max 0 (2 * (k + ε) + d - 2 * c) * β) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
      (x : WaveState U V)
      (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
      (u : Icc 0 U) (a b : Icc 0 V), a ≤ b → l ≤ -x.2.1 u a 0 → x.1 u a 0 ≤ R →
      (b : ℝ) ≤ (1 + β) * a → T ≤ (a : ℝ) →
      (∀ w ∈ Icc a b, |x.2.1 u w 1| ≤ H * Real.exp (-c * w)) →
      let N := radialNuField hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0)) x.1 hx.choose
      let K := fun w => horizonK (x.1 u w 0) (massField e Λ x.1 x.2.1 N hx.choose u w) e Λ
      (∀ w ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u w 2) / (4 * N u w)) →
      (∀ w ∈ Icc a b, |K w + k| ≤ ε) →
      (∀ w ∈ Icc a b, |x.2.1 u w 2 - 2 * K w| ≤ d) →
        (∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
          (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ τ := by
  let η := 2 * c - max 0 (2 * (k + ε) + d - 2 * c) * β
  have hlim : Tendsto (fun t : ℝ => (R * H ^ 2 / l) * β * t * Real.exp (-η * t)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 η hmargin).const_mul ((R * H ^ 2 / l) * β)
    simpa only [Real.rpow_one, mul_zero, mul_assoc] using hh
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually_lt_const hτ)
  refine ⟨max 0 T, le_max_left _ _, ?_⟩
  intro U V hU hV hUR p hp f hf x hx u a b hab hlam hRa hwindow hTa hscalar
  dsimp only
  intro hk hK herr
  have hh := (hx.early_inner_flux_bound hU hV hUR hc hi hrc hr0 hφ hrd hp hf hκ₀ hε hεk hH hl
    u a b hab hlam hRa hwindow hscalar hk hK herr).2
  exact hh.trans (hT a ((le_max_right _ _).trans hTa)).le

end InnerTransport

-- The split estimate has no terminal-time constant, including a degenerate initial interval.
example {U V : ℝ} (hV : 0 ≤ V)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (w : WaveRectangle U V) (u : Icc 0 U)
    (hν : ∀ v, |ν u v| ≤ Real.exp (-(v : ℝ)))
    (hw : ∀ v, |w u v 1| ≤ Real.exp (-(v : ℝ))) (b : Icc 0 V) :
    |scalarTransportCorrection hV ν w u b| ≤ 3 / 2 := by
  have hh := scalarTransportCorrection_split_bound (hV := hV)
    (a := 2) (c := 1) (q := 1) (N := 1) (H := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ν w u ⟨0, le_rfl, hV⟩ b b.property.1
    (fun v hv => by
      have hv0 : (v : ℝ) = 0 := le_antisymm hv v.property.1
      simpa only [hv0, neg_zero, mul_zero, Real.exp_zero, one_mul] using hν v)
    (fun v _ => by simpa using hν v) (fun v _ => by simpa using hw v)
  norm_num at hh ⊢
  exact hh

section EarlyScalar

variable {M e Λ : ℝ} {h r : ℝ → ℝ}
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)

-- Matching and observation times may depend on the incoming coordinate without a new null set.
example {U V A N H : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hN : 0 ≤ N) (hH : 0 ≤ H) {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (hpoint : ∀ᵐ t ∂volume.restrict (Icc 0 U), |f t| ≤ A * t ^ (-1 / 4 : ℝ))
    (T B : ℝ → Icc 0 V) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), 0 < t → T t ≤ B t → t * Real.exp (T t) ≤ 1 →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
      let K := fun v => horizonK (x.1 u v 0) (massField e Λ x.1 x.2.1 ν hx.choose u v) e Λ
      x.2.1 u (T t) 0 < 0 → 1 ≤ x.1 u (B t) 0 →
      (∀ v ≤ T t, |ν u v| ≤ N * Real.exp v) →
      (∀ v ≤ B t, |x.2.1 u v 1| ≤ H * Real.exp (-(1 / 2) * v)) →
      (∀ v ∈ Icc (T t) (B t), 3 / 4 ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
      (∀ v ∈ Icc (T t) (B t), |K v + 3 / 4| ≤ 1 / 4) →
        |x.2.2 t (B t) 1| ≤ (r 0 * A) * t ^ (-1 / 4 : ℝ) +
          (N * H) * (14 / 5) * t ^ (-1 / 2 : ℝ) := by
  have hh := hx.early_scalar_incoming_bound hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
    (a := 1) (c := 1 / 2) (κ₀ := 3 / 4) (k := 3 / 4) (ε := 1 / 4) (ρ := 1) (D := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hN hH (by norm_num) (by simpa using hpoint)
  filter_upwards [hh] with t ht
  intro ht0 hTb hwidth
  dsimp only
  intro htrap hrb hpre hscalar hk hK
  have hs := ht (T t) (B t) ht0 hTb (by simpa only [one_mul] using hwidth) htrap hrb
    (by simpa only [one_mul] using hpre) hscalar hk hK
  norm_num at hs ⊢
  exact hs

-- At p=infinity the power conversion preserves f itself, with arbitrary coordinate-dependent times.
example {U V N H : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hN : 0 ≤ N) (hH : 0 ≤ H) {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x)
    (T B : ℝ → Icc 0 V) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), 0 < t → T t ≤ B t → t * Real.exp (T t) ≤ 1 →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
      let K := fun v => horizonK (x.1 u v 0) (massField e Λ x.1 x.2.1 ν hx.choose u v) e Λ
      x.2.1 u (T t) 0 < 0 → 1 ≤ x.1 u (B t) 0 →
      (∀ v ≤ T t, |ν u v| ≤ N * Real.exp v) →
      (∀ v ≤ B t, |x.2.1 u v 1| ≤ H * Real.exp (-(1 / 2) * v)) →
      (∀ v ∈ Icc (T t) (B t), 3 / 4 ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
      (∀ v ∈ Icc (T t) (B t), |K v + 3 / 4| ≤ 1 / 4) →
        |x.2.2 t (B t) 1| ≤ r 0 * |f t| + (N * H) * (14 / 5) * t ^ (-1 / 2 : ℝ) := by
  have hh := hx.early_scalar_history_power hU hV hUR hc hi hrc hr0 hφ hrd le_top hf
    (a := 1) (c := 1 / 2) (κ₀ := 3 / 4) (k := 3 / 4) (ε := 1 / 4) (ρ := 1) (D := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hN hH (by norm_num)
  filter_upwards [hh] with t ht
  intro ht0 hTb hwidth
  dsimp only
  intro htrap hrb hpre hscalar hk hK
  have hs := ht (T t) (B t) ht0 hTb (by simpa only [one_mul] using hwidth) htrap hrb
    (by simpa only [one_mul] using hpre) hscalar hk hK
  norm_num at hs ⊢
  exact hs

-- The raw history estimate retains bounded incoming data and vanishing radiation at p=infinity.
example {U V a c k ε κ₀ ρ N : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc0 : 0 ≤ c) (hac : c < a) (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k)
    (hρ : 0 < ρ) (hN : 0 ≤ N) {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ (T b : Icc 0 V), T ≤ b →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
      let K := fun v => horizonK (x.1 u v 0) (massField e Λ x.1 x.2.1 ν hx.choose u v) e Λ
      x.2.1 u T 0 < 0 → ρ ≤ x.1 u b 0 →
      (∀ v ≤ T, |ν u v| ≤ N * Real.exp (a * v)) → (∀ v ≤ b, x.2.1 u v 1 = 0) →
      (∀ v ∈ Icc T b, κ₀ ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
      (∀ v ∈ Icc T b, |K v + k| ≤ ε) → |x.2.2 t b 1| ≤ (r 0 / ρ) * |f t| := by
  filter_upwards [hx.early_scalar_history hU hV hUR hc hi hrc hr0 hφ hrd le_top hf
    hc0 hac hκ₀ hε hεk hρ hN (H := 0) le_rfl] with t ht
  intro T b hTb
  dsimp only
  intro htrap hrb hpre hzero hk hK
  simpa using ht T b hTb htrap hrb hpre (fun v hv => by simp [hzero v hv]) hk hK

end EarlyScalar

section EarlyConstraint

-- At p=4 the incoming and history contributions have distinct, positive time rates.
example {z u v C F G : ℝ} {w ψ : ℝ → ℝ} (hz : 0 ≤ z) (hzu : z ≤ u)
    (hC : 0 ≤ C) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hi : IntervalIntegrable (fun y => w y * ψ y ^ 2) volume z u)
    (hw : ∀ᵐ y ∂volume.restrict (Ioc z u), w y ≤ C * Real.exp ((2 / 17) * v) * y)
    (hψ : ∀ᵐ y ∂volume.restrict (Ioc z u),
      |ψ y| ≤ F * y ^ (-1 / 4 : ℝ) + G * y ^ (-1 / 2 : ℝ))
    (hwidth : u * Real.exp ((16 / 17) * v) ≤ 1) :
    (∫ y in z..u, w y * ψ y ^ 2) ≤
      C * (F ^ 2 / (3 / 4) * Real.exp (-(22 / 17) * v) +
        G ^ 2 / (1 / 2) * Real.exp (-(14 / 17) * v)) := by
  have hh := linear_weight_power_energy (s := 3 / 4) (t := 1 / 2) hz hzu
    (by norm_num) (by norm_num) hC hF hG hi hw
    (by simpa only [show (3 / 4 : ℝ) - 1 = -1 / 4 by norm_num,
      show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] using hψ) hwidth
  norm_num at hh ⊢
  exact hh

-- These are the two constraint margins under the manuscript's small early time window.
example {k c ε β : ℝ} (hk : 0 < k) (hc : k / 2 < c)
    (hε : ε ≤ k / 3) (hβ : 0 ≤ β) (hβ1 : β < 1 / 8) :
    0 < (2 * k - 2 * (k + ε) * β) / (1 + β) ∧
      0 < (2 * c - 2 * (k + ε) * β) / (1 + β) := by
  have h1 := mul_le_mul_of_nonneg_right hε hβ
  have h2 := mul_lt_mul_of_pos_left hβ1 hk
  have hα : 0 < 1 + β := by linarith only [hβ]
  constructor <;> apply div_pos _ hα <;> nlinarith only [h1, h2, hk, hc]

variable {M e Λ : ℝ} {h r : ℝ → ℝ}
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)

-- The actual energy vanishes for zero scalar data, including p=infinity and arbitrary entry times.
example {U V a c k ε κ₀ β ρ R n N D : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc0 : 0 < c) (hac : c < a) (hκ₀ : 0 < κ₀) (hε : 0 ≤ ε) (hεk : ε < k)
    (hβ : 0 ≤ β) (hρ : 0 < ρ) (hR : 0 ≤ R) (hn : 0 < n) (hN : 0 ≤ N) (hD : 0 ≤ D)
    {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x)
    (hzf : ∀ᵐ y ∂volume.restrict (Icc 0 U), f y = 0)
    (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (hrow : ∀ w ∈ Icc z u, ρ ≤ x.1 w b 0 ∧ x.1 w b 0 ≤ R)
    (hwidth : (u : ℝ) * Real.exp ((a / (1 + β)) * b) ≤ D) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
    let K := fun w v => horizonK (x.1 w v 0) (massField e Λ x.1 x.2.1 ν hx.choose w v) e Λ
    (∀ y ∈ Ioc (z : ℝ) u,
      let w := projIcc 0 U hU y
      ∃ T : Icc 0 V, T ≤ b ∧ (b : ℝ) ≤ (1 + β) * T ∧ x.2.1 w T 0 < 0 ∧
        n ≤ y * (-ν w T) ∧ y * Real.exp (a * T) ≤ D ∧
        (∀ v ≤ T, |ν w v| ≤ N * Real.exp (a * v)) ∧
        (∀ v ≤ b, x.2.1 w v 1 = 0) ∧
        (∀ v ∈ Icc T b, κ₀ ≤ -Real.exp (x.1 w v 2) / (4 * ν w v)) ∧
        (∀ v ∈ Icc T b, |K w v + k| ≤ ε)) →
      (∫ y in (z : ℝ)..u, intervalExtension hU x.1 y b 0 * (x.2.2 y b 1) ^ 2 /
        (-intervalExtension hU ν y b)) ≤ 0 := by
  dsimp only
  intro hmatch
  have hpnt : ∀ᵐ y ∂volume.restrict (Icc 0 U), |f y| ≤ 0 * y ^ (-1 / (∞ : ℝ≥0∞).toReal) := by
    filter_upwards [hzf] with y hy
    simp [hy]
  have hh := hx.early_constraint_bound hU hV hUR hc hi hrc hr0 hφ hrd le_top hf
    hc0 hac hκ₀ hε hεk hβ hρ hR hn hN (H := 0) le_rfl hD (A := 0) le_rfl hpnt
    z u hzu b hrow hwidth (fun y hy => by
      obtain ⟨T, hTb, hwin, htrap, hentry, hscale, hpre, hzero, hk, hK⟩ := hmatch y hy
      exact ⟨T, hTb, hwin, htrap, hentry, hscale, hpre,
        fun v hv => by simp [hzero v hv], hk, hK⟩)
  simpa only [mul_zero, zero_div, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using hh

end EarlyConstraint

section EarlyFeedback

example {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x)
    (z u : Icc 0 U) (hzu : z ≤ u) (v : Icc 0 V) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
    let S := fun t => intervalExtension hU x.1 t v 0 * (x.2.2 t v 1) ^ 2 /
      (-intervalExtension hU ν t v)
    (∫ t in (0 : ℝ)..z, S t) ≤ Real.log (4 / 3) → (∫ t in (z : ℝ)..u, S t) ≤ 0 →
      3 / 4 ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) := by
  dsimp only
  intro hleft hright
  have hh := (hx.horizon_constraint_join hU hV hUR hc hi hrc hr0 hφ hrd le_top hf
    z u hzu v hleft hright).2.1
  norm_num [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at hh
  exact hh

variable (B : Background) {s H dH A ρ D₀ c : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
  (hρ : 0 < ρ) (hρR : ρ ≤ B.event + dH) (hD₀ : 0 ≤ D₀)
  (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

-- The large rectangle need not satisfy the small width condition of its controlled prefix.
example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ C : ℝ, 0 < U₀ ∧ 0 ≤ C ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_top hf) x),
        (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ≤ A →
        ∀ z : Icc 0 U, (z : ℝ) ≤ U₀ → (∀ w ≤ z, ∀ v, ρ ≤ x.1 w v 0) →
          (z : ℝ) * Real.exp (B.outerRate * V) ≤ D₀ →
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
          let v : Icc 0 V := ⟨V, hV, le_rfl⟩
          Real.exp (-(C * Real.exp (-(min B.outerRate (2 * c)) * V))) ≤
            -Real.exp (x.1 z v 2) / (4 * ν z v) := by
  obtain ⟨U₀, C, _E, hU₀, _hUr, hC, _hE, hbound⟩ :=
    B.exists_prefix_feedback_decay hs hH hdH hdHR hA hρ hρR hD₀ hc0 hca hcs hc hb hrc hrb hrd hrdec hOut
  refine ⟨U₀, C, hU₀, hC, ?_⟩
  intro U V hU hV hUR f hf x hx hfn z hz hlo hwidth
  have he := (hbound U V hU hV hUR ∞ le_top f hf x hx hfn
    (by simpa using hca.le) z hz hlo hwidth).1
  have hk := (hx.horizon_kappa_exponential hU hV hUR hc _ hrc _
    (horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb) hrd le_top hf
    ⟨V, hV, le_rfl⟩).2 z
  exact (Real.exp_le_exp.2 (neg_le_neg he)).trans_eq hk.symm

-- A common time improves the early kappa bootstrap from 1/2 to 3/4 at p=4.
example {Apt D k n N He Kmax : ℝ} (hApt : 0 ≤ Apt) (hD : 0 ≤ D)
    (hk : 0 < k) (hck : k / 2 < c) (hn : 0 < n) (hN : 0 ≤ N) (hHe : 0 ≤ He) (hKmax : 0 ≤ Kmax)
    (hcb : c ≤ B.outerRate * (3 / 4)) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ U₀ T₀ : ℝ, 0 < U₀ ∧ 0 ≤ T₀ ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
        (∀ᵐ y ∂volume.restrict (Icc 0 U), |f y| ≤ Apt * y ^ (-1 / 4 : ℝ)) → U ≤ U₀ →
        ∀ z : Icc 0 U, (∀ w ≤ z, ∀ v, ρ ≤ x.1 w v 0) →
          (z : ℝ) * Real.exp (B.outerRate * V) ≤ D₀ →
          let u : Icc 0 U := ⟨U, hU, le_rfl⟩
          let v : Icc 0 V := ⟨V, hV, le_rfl⟩
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
          let K := fun w t => horizonK (x.1 w t 0)
            (massField B.charge B.cosmological x.1 x.2.1 ν hx.choose w t) B.charge B.cosmological
          (∀ w, ρ ≤ x.1 w v 0 ∧ x.1 w v 0 ≤ B.event + dH) →
          U * Real.exp ((B.outerRate / (1 + 1 / 16)) * V) ≤ D → |K u v| ≤ Kmax →
          (∀ y ∈ Ioc (z : ℝ) U,
            let w := projIcc 0 U hU y
            ∃ T : Icc 0 V, T ≤ v ∧ V ≤ (1 + 1 / 16) * T ∧ x.2.1 w T 0 < 0 ∧
              n ≤ y * (-ν w T) ∧ y * Real.exp (B.outerRate * T) ≤ D ∧
              (∀ t ≤ T, |ν w t| ≤ N * Real.exp (B.outerRate * t)) ∧
              (∀ t ≤ v, |x.2.1 w t 1| ≤ He * Real.exp (-c * t)) ∧
              (∀ t ∈ Icc T v, 1 / 2 ≤ -Real.exp (x.1 w t 2) / (4 * ν w t)) ∧
              (∀ t ∈ Icc T v, |K w t + k| ≤ k / 4)) →
            T₀ ≤ V → 3 / 4 ≤ -Real.exp (x.1 u v 2) / (4 * ν u v) := by
  have hmargin : 0 < 2 * (B.outerRate / (1 + 1 / 16)) * (c / B.outerRate) -
      2 * (k + k / 4) * (1 / 16) / (1 + 1 / 16) := by
    have he : 2 * (B.outerRate / (1 + 1 / 16)) * (c / B.outerRate) -
        2 * (k + k / 4) * (1 / 16) / (1 + 1 / 16) = (64 * c - 5 * k) / 34 := by
      field_simp [B.outerRate_pos.ne']
      ring
    rw [he]
    apply div_pos _ (by norm_num)
    linarith only [hk, hck]
  obtain ⟨U₀, _C, T₀, hU₀, _hUr, _hC, hT, hbound⟩ :=
    B.exists_early_geometric_feedback hs hH hdH hdHR hA hApt hρ hρR hD₀ hD hc0 hca hcs
      (κ₀ := 1 / 2) (ε := k / 4) (β := 1 / 16) (by norm_num) (by positivity) (by linarith only [hk])
      (by norm_num) hn hN hHe hKmax (p := 4) le_rfl (by norm_num; exact hcb) hmargin
      hc hb hrc hrb hrd hrdec hOut
  refine ⟨U₀, T₀, hU₀, hT, ?_⟩
  intro U V hU hV hUR f hf x hx hfn hpoint hUU z hlo hprewidth
  dsimp only
  intro hrow hwidth hK hmatch hTV
  exact (hbound U V hU hV hUR f hf x hx hfn (by simpa only [ENNReal.toReal_ofNat] using hpoint)
    hUU z hlo hprewidth hrow hwidth hK hmatch).2.2 hTV

end EarlyFeedback

section ArrivalScalar

-- Vanishing pre-entry radiation removes its forcing, not the independent inner amplitude.
example {U V a c q N M H : ℝ} {hV : 0 ≤ V}
    (hac : c < a) (hqc : 0 < q + c) (hN : 0 ≤ N) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (ν : C(Icc 0 U, C(Icc 0 V, ℝ))) (w : WaveRectangle U V)
    (u : Icc 0 U) (T b : Icc 0 V) (hTb : T ≤ b)
    (hpre : ∀ v ≤ T, |ν u v| ≤ N * Real.exp (a * v))
    (hpost : ∀ v ∈ Icc T b, |ν u v| ≤ M * Real.exp (-q * ((v : ℝ) - T)))
    (hzero : ∀ v ≤ T, w u v 1 = 0)
    (hw : ∀ v ∈ Icc T b, |w u v 1| ≤ H * Real.exp (-c * v)) :
    |scalarTransportCorrection hV ν w u b| ≤ M * H / (q + c) * Real.exp (-c * T) := by
  have hh := scalarTransportCorrection_two_amplitudes (hV := hV) hac hqc hN hM le_rfl hH
    ν w u T b hTb hpre hpost (fun v hv => by simp [hzero v hv]) hw
  simpa only [mul_zero, zero_div, zero_mul, zero_add] using hh

variable {U V R e Λ φ₀ N E He A H₀ : ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
  {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
  {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
    (incomingWaveVelocity hUR le_rfl hf) x)
  (hN : 0 ≤ N) (hE : 0 ≤ E) (hHe : 0 ≤ He) (hA : 0 ≤ A)
  (hpoint : ∀ᵐ t ∂volume.restrict (Icc 0 U), |f t| ≤ A * t ^ (-1 / 4 : ℝ))

-- The critical p=4 equality c=a*(1-1/p) is retained in the normalized estimate.
example :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ (T b : Icc 0 V), 0 < t → T ≤ b →
      t * Real.exp (4 * T) ≤ 1 →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) x.1 hx.choose
      1 ≤ t * (-ν u T) →
      (∀ v ≤ T, |ν u v| ≤ N * Real.exp (4 * v)) →
      (∀ v ∈ Icc T b, |ν u v| ≤ (-ν u T) * Real.exp (-1 * ((v : ℝ) - T))) →
      (∀ v ≤ T, |x.2.1 u v 1| ≤ E * Real.exp (-3 * v)) →
      (∀ v ∈ Icc T b, |x.2.1 u v 1| ≤ He * Real.exp (-3 * v)) →
        |x.1 u b 0 * x.2.2 t b 1| ≤ (-ν u T) * Real.exp (-3 * T) * (R * A + N * E + He / 4) := by
  have hpt : ∀ᵐ t ∂volume.restrict (Icc 0 U), |f t| ≤ A * t ^ (-1 / (4 : ℝ≥0∞).toReal) := by
    simpa only [ENNReal.toReal_ofNat] using hpoint
  filter_upwards [hx.entry_normalized_zeta hU hV hUR le_rfl hf
    (a := 4) (c := 3) (q := 1) (n := 1) (D := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hN hE hHe hA (by norm_num) hpt] with t ht
  intro T b ht0 hTb hwidth
  dsimp only
  intro hentry hpre hpost hwpre hwpost
  have hh := ht T b ht0 hTb hwidth hentry hpre hpost hwpre hwpost
  norm_num at hh ⊢
  exact hh

-- Compose the actual vertical and horizontal identities. The inner feedback is He/64.
example (z u : Icc 0 U) (hz : 0 < (z : ℝ)) (hzu : z ≤ u) (b : Icc 0 V)
    (T : C(Icc (z : ℝ) u, Icc 0 V)) :
    let τ := fun t => T (projIcc (z : ℝ) u hzu t)
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) x.1 hx.choose
    τ z = b →
    (∀ t ∈ Icc (z : ℝ) u, ν (projIcc 0 U hU t) (τ t) < 0) →
    (∀ t ∈ Icc (z : ℝ) u, -(1 / 4) ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧
      x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0) →
    (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
      (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) →
    (∀ w ∈ Icc z u, 1 ≤ x.1 w b 0) →
    (∀ t ∈ Icc (z : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
      (1 / 4) * Real.exp (-4 * ((b : ℝ) - τ t))) →
    (∀ t ∈ Icc (z : ℝ) u,
      let w := projIcc 0 U hU t
      τ t ≤ b ∧ t * Real.exp (4 * τ t) ≤ 1 ∧ 1 ≤ t * (-ν w (τ t)) ∧
        (∀ v ≤ τ t, |ν w v| ≤ N * Real.exp (4 * v)) ∧
        (∀ v ∈ Icc (τ t) b, |ν w v| ≤ (-ν w (τ t)) * Real.exp (-1 * ((v : ℝ) - τ t))) ∧
        (∀ v ≤ τ t, |x.2.1 w v 1| ≤ E * Real.exp (-3 * v)) ∧
        (∀ v ∈ Icc (τ t) b, |x.2.1 w v 1| ≤ He * Real.exp (-3 * v))) →
    Real.exp (3 * b) * |x.1 z b 0 * x.2.1 z b 1| ≤ H₀ →
      Real.exp (3 * b) * |x.2.1 u b 1| ≤ H₀ + (R * A + N * E) / 16 + He / 64 := by
  dsimp only
  intro hτz hν hentry hder hr hlam hhist hθ
  have hpt : ∀ᵐ t ∂volume.restrict (Icc 0 U), |f t| ≤ A * t ^ (-1 / (4 : ℝ≥0∞).toReal) := by
    simpa only [ENNReal.toReal_ofNat] using hpoint
  have hζ : ∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.1 (projIcc 0 U hU t) b 0 * x.2.2 t b 1| ≤
        (-radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) x.1 hx.choose
          (projIcc 0 U hU t) (T (projIcc (z : ℝ) u hzu t))) *
            Real.exp (-3 * (T (projIcc (z : ℝ) u hzu t) : ℝ)) * (R * A + N * E + He / 4) := by
    filter_upwards [hx.entry_normalized_zeta hU hV hUR le_rfl hf
      (a := 4) (c := 3) (q := 1) (n := 1) (D := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hN hE hHe hA (by norm_num) hpt] with t ht
    intro htm
    obtain ⟨hTb, hwidth, hn, hpre, hpost, hwpre, hwpost⟩ := hhist t htm
    have hh := ht (T (projIcc (z : ℝ) u hzu t)) b (hz.trans_le htm.1)
      hTb hwidth hn hpre hpost hwpre hwpost
    norm_num at hh ⊢
    exact hh
  have hR : 0 ≤ R := (hU.trans_lt hUR).le
  have hh := hx.arrival_scalar_feedback hU hV hUR le_rfl hf
    (c := 3) (ℓ := 4) (ρ := 1) (L := 1 / 4) (Lᵧ := 1 / 4) (B := R * A + N * E + He / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
    z u hzu b T hτz hν hentry hder hr hlam hζ hθ
  exact hh.trans_eq (by norm_num; ring)

end ArrivalScalar

section EarlyScalarClosure

-- The matching radius is chosen before the error constant and its late-time threshold.
example (B : Background) {R L : ℝ} (hR : B.inner < R) (hRe : R ≤ B.event) (hL : 0 < L) :
    ∃ Y ∈ Ioo B.inner R, ∀ C η : ℝ, 0 < η → ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      ∀ {U V : ℝ} {h r : ℝ → ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
        (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
        (_hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
        (_hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
          (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
        {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_top hf) x)
        (u : Icc 0 U) (v : Icc 0 V), T₀ ≤ v → x.1 u v 0 = Y →
        let ν := radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
        |(-Real.exp (x.1 u v 2) / (4 * ν u v)) - 1| +
          |massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u v - B.mass| ≤ C * Real.exp (-η * v) →
          |x.2.1 u v 0| ≤ L := by
  obtain ⟨Y, hY, hbound⟩ := B.exists_small_matching_speed hR hRe hL
  refine ⟨Y, hY, ?_⟩
  intro C η hη
  obtain ⟨T₀, hT, hb⟩ := hbound C η hη
  refine ⟨T₀, hT, ?_⟩
  intro U V h r hU hV hUR hc hi hrc hr0 hφ hrd f hf x hx u v hTv hrY
  dsimp only
  intro hm
  have hh := hb hU hV hUR hc hi hrc hr0 hφ hrd le_top hf hx u v hTv hrY
    ((le_add_of_nonneg_left (abs_nonneg _)).trans hm)
  rw [abs_of_neg (neg_pos.1 hh.1)]
  exact hh.2

-- A positive admissible speed budget exists for every positive pair of decay gaps.
example {ρ q s : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hs : 0 < s) :
    ∃ L : ℝ, 0 < L ∧ Real.exp 1 * L ^ 2 / (ρ ^ 2 * s * q) ≤ 1 / 4 := by
  exact exists_small_scalar_speed hρ hq hs

-- At p=4 and c=a*(1-1/p), the actual scalar bootstrap improves strictly.
example {M e Λ ρ R N E A H L l : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0) (hrinit : 0 < r 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hE : 0 ≤ E) (hA : 0 ≤ A) (hH : 0 ≤ H) (hL : 0 ≤ L) (hl : 0 < l)
    (hsmall : Real.exp 1 * L ^ 2 / (12 * ρ ^ 2) ≤ 1 / 4) :
    ∃ He T₀ : ℝ, 0 < He ∧ E ≤ He ∧ 0 ≤ T₀ ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x),
        (∀ᵐ t ∂volume.restrict (Icc 0 U), |f t| ≤ A * t ^ (-1 / 4 : ℝ)) →
        ∀ (z u : Icc 0 U) (_hz : 0 < (z : ℝ)) (hzu : z ≤ u) (b : Icc 0 V)
          (T : C(Icc (z : ℝ) u, Icc 0 V)),
          let τ := fun t => T (projIcc (z : ℝ) u hzu t)
          let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
          let K := fun w v => horizonK (x.1 w v 0) (massField e Λ x.1 x.2.1 ν hx.choose w v) e Λ
          τ z = b →
          (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
            (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) →
          (∀ w ∈ Icc z u, ρ ≤ x.1 w b 0) →
          (∀ t ∈ Icc (z : ℝ) u,
            let w := projIcc 0 U hU t
            T₀ ≤ τ t ∧ τ t ≤ b ∧ (b : ℝ) ≤ (1 + 1 / 16) * τ t ∧
              l ≤ -x.2.1 w (τ t) 0 ∧ -x.2.1 w (τ t) 0 ≤ L ∧ x.1 w (τ t) 0 ≤ R ∧
              1 ≤ t * (-ν w (τ t)) ∧ t * Real.exp (4 * τ t) ≤ 1 ∧
              (∀ v ≤ τ t, |ν w v| ≤ N * Real.exp (4 * v)) ∧
              (∀ v ≤ τ t, |x.2.1 w v 1| ≤ E * Real.exp (-3 * v)) ∧
              (∀ v ∈ Icc (τ t) b, |x.2.1 w v 1| ≤ He * Real.exp (-3 * v)) ∧
              (∀ v ∈ Icc (τ t) b, 1 / 2 ≤ -Real.exp (x.1 w v 2) / (4 * ν w v)) ∧
              (∀ v ∈ Icc (τ t) b, |K w v + 4| ≤ 1) ∧
              (∀ v ∈ Icc (τ t) b, |x.2.1 w v 2 - 2 * K w v| ≤ 1)) →
          Real.exp (3 * b) * |x.1 z b 0 * x.2.1 z b 1| ≤ H →
            Real.exp (3 * b) * |x.2.1 u b 1| < He := by
  have hsmall' : Real.exp 1 * L ^ 2 / (ρ ^ 2 * (2 * (4 - 1) - 1 - 3) * (2 * (1 / 2) * (4 - 1) + 3)) ≤ 1 / 4 := by
    have he : ρ ^ 2 * (2 * (4 - 1) - 1 - 3) * (2 * (1 / 2) * (4 - 1) + 3) = 12 * ρ ^ 2 := by ring
    rwa [he]
  obtain ⟨He, T₀, hHe, hEHe, hT, hbound⟩ := exists_early_scalar_improvement
    (a := 4) (c := 3) (k := 4) (ε := 1) (d := 1) (κ₀ := 1 / 2) (n := 1) (D := 1) (β := 1 / 16) (R := R)
    hc hi hrc hr0 hrinit hφ hrd (p := 4) le_rfl (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hρ (by norm_num) hN hE (by norm_num) hA hH hL hl
    (by norm_num) (by norm_num) hsmall'
  refine ⟨He, T₀, hHe, hEHe.le, hT, ?_⟩
  intro U V hU hV hUR f hf x hx hpoint z u hz hzu b T
  dsimp only
  intro hτ hder hr hhist hθ
  exact (hbound U V hU hV hUR f hf x hx (by simpa only [ENNReal.toReal_ofNat] using hpoint)
    z u hz hzu b T hτ hder hr hhist hθ).trans_lt (half_lt_self hHe)

end EarlyScalarClosure

section EarlyGeometryClosure

-- The geometric margin allows the perturbed radius to cross below the background root.
example (B : Background) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ 3 * B.inner / 4 ≤ B.inner - δ / 2 ∧
      |horizonK (B.inner - δ / 2) (B.mass + δ / 2) B.charge B.cosmological + B.innerRate| < ε := by
  obtain ⟨δ, hδ, _hr, _he, hbound⟩ := B.exists_inner_K_margin hε
  have h₁ : |B.inner - δ / 2 - B.inner| ≤ δ := by
    rw [show B.inner - δ / 2 - B.inner = -(δ / 2) by ring, abs_neg,
      abs_of_nonneg (half_pos hδ).le]
    exact half_le_self hδ.le
  have h₂ : |B.mass + δ / 2 - B.mass| ≤ δ := by
    rw [show B.mass + δ / 2 - B.mass = δ / 2 by ring, abs_of_nonneg (half_pos hδ).le]
    exact half_le_self hδ.le
  have hh := hbound _ _ h₁ h₂
  exact ⟨δ, hδ, hh.1, hh.2.trans_lt (half_lt_self hε)⟩

-- An absolute terminal mass error suffices for the barrier, including p=infinity.
example (B : Background) {U V ρ : ℝ} {h r : ℝ → ℝ}
    (hρ : 0 < ρ) (hF : 0 < B.F ρ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    {f : ℝ → ℝ} (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
      (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
      (incomingWaveVelocity hUR le_top hf) x)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b)
    (ha : x.2.1 u a 0 < 0) (hra : ρ ≤ x.1 u a 0) :
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
    |massField B.charge B.cosmological x.1 x.2.1 ν hx.choose u b - B.mass| ≤ ρ * B.F ρ / 4 →
      ρ < x.1 u b 0 := by
  dsimp only
  intro hm
  apply hx.trapped_radius_barrier B hρ hF hU hV hUR hc hi hrc hr0 hφ hrd le_top hf u a b hab ha hra
  have hh := (abs_le.1 hm).2
  linarith only [hh]

-- At p=4 the joint estimate strictly improves both the radius floor and K margin.
example (B : Background) {ε κ₀ c β : ℝ}
    (hε : 0 < ε) (hk : 0 < κ₀) (hc0 : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H C γ : ℝ, 0 ≤ H → 0 < γ →
      ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ Y : ℝ, B.inner < Y → Y ≤ B.inner + δ / 2 →
        ∀ {U V : ℝ} {h r : ℝ → ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
          (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
          (_hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
          (_hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
            (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
          {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR le_rfl hf) x)
          (u : Icc 0 U) (a b : Icc 0 V), a ≤ b → T₀ ≤ a →
          x.1 u a 0 = Y → x.2.1 u a 0 < 0 →
          (b : ℝ) ≤ (1 + β) * a →
          (∀ v ∈ Icc a b, |x.2.1 u v 1| ≤ H * Real.exp (-c * v)) →
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
          let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
          let K := fun v => horizonK (x.1 u v 0) (m u v) B.charge B.cosmological
          |m u a - B.mass| ≤ C * Real.exp (-γ * a) →
          (∀ v ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
            B.inner / 2 < x.1 u b 0 ∧ |m u b - B.mass| ≤ δ / 2 ∧ |K b + B.innerRate| < ε := by
  obtain ⟨δ, hδ, _hδr, _hδe, _hpot, hbound⟩ := B.exists_early_radius_mass_improvement hε hk hc0
  refine ⟨δ, hδ, ?_⟩
  intro H C γ hH hγ
  obtain ⟨T₀, hT, hb⟩ := hbound H C γ hH hγ
  refine ⟨T₀, hT, ?_⟩
  intro Y hY hYδ U V h r hU hV hUR hc hi hrc hr0 hφ hrd f hf x hx u a b hab hTa
    hra ha hwindow hscalar
  dsimp only
  intro hm hkappa
  have hh := hb Y hY hYδ hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf hx u a b hab hTa
    hra ha hwindow hscalar hm hkappa
  refine ⟨?_, hh.2.1, hh.2.2.2.trans_lt (half_lt_self hε)⟩
  linarith only [hh.2.2.1, B.inner_pos]

end EarlyGeometryClosure

section BandMatching

-- A closed chart also exists for a singleton row; no artificial strict-width premise is needed.
example {ε z V : ℝ} {arrival : ℝ → ℝ} (hz : 0 < z) (hzε : z < ε)
    (hc : ContinuousOn arrival (Ioo 0 ε)) (ha : StrictAntiOn arrival (Ioo 0 ε))
    (hp : ∀ t ∈ Ioo 0 ε, 0 < arrival t) (b : Icc 0 V) (hb : arrival z = b) :
    ∃ T : C(Icc z z, Icc 0 V), T ⟨z, le_rfl, le_rfl⟩ = b := by
  obtain ⟨T, hval, _hrest⟩ := exists_compact_arrival_chart hz hzε le_rfl hc ha hp
    (slope := fun _ => 0) (fun t ht => (not_lt_of_ge ht.1.le ht.2).elim) b hb
  refine ⟨T, Subtype.ext ?_⟩
  exact (hval _).trans hb

variable (B : Background) {s H dH A : ℝ} {h r : ℝ → ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
  (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

-- At p=4, the global matching theorem supplies the exact physical derivative on a closed entered row.
example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ σ K : ℝ, 0 < δ ∧ 0 < σ ∧ 0 < K ∧
      ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ arrival : ℝ → ℝ, ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR le_rfl hfU) x)
          (u : Icc 0 U) (b : Icc 0 V), 0 < (u : ℝ) → (u : ℝ) < σ → K ≤ b → arrival u ≤ b →
            ∃ (z : Icc 0 U) (hzu : z ≤ u) (T : C(Icc (z : ℝ) u, Icc 0 V)),
              0 < (z : ℝ) ∧
              let τ := fun t => T (projIcc (z : ℝ) u hzu t)
              let ν := radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
              τ z = b ∧ (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
                (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) := by
  dsimp only
  let c := min (s / 2) (B.outerRate / 2)
  have hc0 : 0 < c := lt_min (half_pos hs) (half_pos B.outerRate_pos)
  have hca : c < B.outerRate := (min_le_right _ _).trans_lt (half_lt_self B.outerRate_pos)
  have hcs : c ≤ s := (min_le_left _ _).trans (half_le_self hs.le)
  have hcb : c ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    simp only [ENNReal.toReal_ofNat]
    have hh : c ≤ B.outerRate / 2 := min_le_right _ _
    nlinarith only [hh, B.outerRate_pos]
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hsolve⟩ :=
    B.exists_band_row_charts hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨σ, _j, _D, _n, _N, _L, _E, _l, _C, K,
    hσ, _hσδ, _hj, _hD, _hn, _hN, _hL, _hE, _hl, _hC, hK, hglobal⟩ := hsolve R hR.1 le_rfl
  refine ⟨δ, σ, K, hδ, hσ, hK, ?_⟩
  intro f hf hfn
  obtain ⟨arrival, _hac, _haa, _hal, _hscale, _hpre, _hidentify, hrow⟩ := hglobal 4 le_rfl f hf hfn hcb
  refine ⟨arrival, ?_⟩
  intro U V hU hV hUR hfU x hx u b hu huσ hKb hub
  obtain ⟨z, hzu, T, hz, hTb, hdT, _hdata⟩ := hrow hU hV hUR hfU hx u b hu huσ hKb hub
  exact ⟨z, hzu, T, hz, hTb, hdT⟩

-- At p=infinity, the actual left endpoint supplies the theta forcing and its full positive-radius prefix.
example {c : ℝ} (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y σ E K : ℝ, 0 < δ ∧ 0 < Y ∧ 0 < σ ∧ 0 ≤ E ∧ 0 < K ∧
      ∀ f : ℝ → ℝ, MemLp f ∞ (volume.restrict (Icc 0 δ)) →
        (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ arrival : ℝ → ℝ, ∀ {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
          (_hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR le_top hfU) x)
          (u : Icc 0 U) (b : Icc 0 V), 0 < (u : ℝ) → (u : ℝ) < σ → K ≤ b → arrival u ≤ b →
            ∃ z : Icc 0 U, 0 < (z : ℝ) ∧ z ≤ u ∧ x.1 z b 0 = Y ∧
              (∀ q ≤ z, ∀ v ≤ b, Y ≤ x.1 q v 0) ∧
              Real.exp (c * b) * |x.1 z b 0 * x.2.1 z b 1| ≤ Y * E := by
  dsimp only
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hsolve⟩ :=
    B.exists_band_row_charts hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨σ, _j, _D, _n, _N, _L, E, _l, _C, K,
    hσ, _hσδ, _hj, _hD, _hn, _hN, _hL, hE, _hl, _hC, hK, hglobal⟩ := hsolve R hR.1 le_rfl
  have hR0 := B.inner_pos.trans hR.1
  refine ⟨δ, R, σ, E, K, hδ, hR0, hσ, hE, hK, ?_⟩
  intro f hf hfn
  have hcb : c ≤ B.outerRate * (1 - 1 / (∞ : ℝ≥0∞).toReal) := by simpa using hca.le
  obtain ⟨arrival, _hac, _haa, _hal, _hscale, _hpre, _hidentify, hrow⟩ := hglobal ∞ le_top f hf hfn hcb
  refine ⟨arrival, ?_⟩
  intro U V hU hV hUR hfU x hx u b hu huσ hKb hub
  obtain ⟨z, hzu, T, hz, hTb, _hdT, hdata⟩ := hrow hU hV hUR hfU hx u b hu huσ hKb hub
  have hh := hdata z (left_mem_Icc.2 (show (z : ℝ) ≤ u from hzu))
  simp only [projIcc_of_mem hU z.property, hTb] at hh
  have hpre := hh.2.2.2.2.2.2.2.1
  have hscalar := (hpre z le_rfl b le_rfl).2.2
  refine ⟨z, hz, hzu, hh.2.2.1, fun q hq v hv => (hpre q hq v hv).1, ?_⟩
  rw [hh.2.2.1, abs_mul, abs_of_pos hR0]
  have hm := mul_le_mul_of_nonneg_left hscalar (mul_pos (Real.exp_pos (c * b)) hR0).le
  have hex : Real.exp (c * b) * Real.exp (-c * b) = 1 := by
    rw [← Real.exp_add, show c * b + -c * b = 0 by ring, Real.exp_zero]
  calc
    _ ≤ Real.exp (c * b) * R * (E * Real.exp (-c * b)) := by simpa only [mul_assoc] using hm
    _ = R * E := by calc
      _ = (R * E) * (Real.exp (c * b) * Real.exp (-c * b)) := by ring
      _ = _ := by rw [hex, mul_one]

-- A rectangle ending before matching has the full pre-entry history, including both axes.
example {c : ℝ} (hc0 : 0 < c) (hca : c < B.outerRate) (hcs : c ≤ s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y σ N E : ℝ, 0 < δ ∧ B.inner < Y ∧ 0 < σ ∧
      ∀ f : ℝ → ℝ, MemLp f ∞ (volume.restrict (Icc 0 δ)) →
        (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ arrival : ℝ → ℝ, ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
          (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) {x : WaveState U V}
          (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
            (incomingWaveCurve hU.le hUR le_top hfU (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR le_top hfU) x), U < σ → V ≤ arrival U →
            ∀ q v, Y ≤ x.1 q v 0 ∧
              |radialNuField hV B.charge B.cosmological
                (incomingWaveCurve hU.le hUR le_top hfU (horizonPhi h r 0)) x.1 hx.choose q v| ≤
                  N * Real.exp (B.outerRate * v) ∧ |x.2.1 q v 1| ≤ E * Real.exp (-c * v) := by
  dsimp only
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hsolve⟩ :=
    B.exists_band_row_charts hs hH hdH hdHR hA hc0 hca hcs hc hb hrc hrb hrinit hrd hrdec hOut
  obtain ⟨σ, _j, _D, _n, N, _L, E, _l, _C, _K,
    hσ, _hσδ, _hj, _hD, _hn, _hN, _hL, _hE, _hl, _hC, _hK, hglobal⟩ := hsolve R hR.1 le_rfl
  refine ⟨δ, R, σ, N, E, hδ, hR.1, hσ, ?_⟩
  intro f hf hfn
  have hcb : c ≤ B.outerRate * (1 - 1 / (∞ : ℝ≥0∞).toReal) := by simpa using hca.le
  obtain ⟨arrival, _hac, _haa, _hal, _hscale, hpre, _hidentify, _hrow⟩ := hglobal ∞ le_top f hf hfn hcb
  refine ⟨arrival, ?_⟩
  intro U V hU hV hUR hfU x hx hUσ hVY q v
  exact hpre hU.le hV hUR hfU hx U ⟨hU, hUσ⟩ q q.property.2 v (v.property.2.trans hVY)

end BandMatching

section EarlyJointClosure

-- Zero early-window length retains the matching inverse-coordinate bound.
example {a u T j D N : ℝ} (ha : 0 < a) (hu : 0 < u) (hj : 0 < j)
    (hD : 0 ≤ D) (hN : 0 ≤ N)
    (hlo : j ≤ u * Real.exp (a * T)) (hhi : u * Real.exp (a * T) ≤ D) :
    N * Real.exp (a * T) ≤ N * D * u ^ (-1 : ℝ) := by
  simpa using arrival_decay_power (q := 1) (β := 0) ha hu hj hD hN (by norm_num)
    le_rfl hlo hhi

-- The linked rates preserve the manuscript's positive transverse power and late scalar gap.
example {a k s l : ℝ} (ha : 0 < a) (hk : 0 < k) (hks : k < s) (hl : l < 2 * s + k) :
    ∃ hc c β ε : ℝ, 0 < hc ∧ c = (k + hc) / 2 ∧ c < k ∧ 0 < β ∧ β < 1 / 8 ∧
      0 < ε ∧ (k / a) * β + hc * (1 + β) / a < c / a ∧
      hc < k / (1 + β) ∧ k ≤ 2 * (2 / 3) * (k - ε) := by
  obtain ⟨hc, c, β, ε, hhc, _hhck, _htail, heq, _hc0, hck, _hcs, hβ, hβ8, hlink,
    hε, _hεk, _hεβ, hnu, _hℓ, _hJ, _hQ⟩ := exists_linked_inner_parameters hk hks hl
  refine ⟨hc, c, β, ε, hhc, heq, hck, hβ, hβ8, hε, ?_, ?_, hnu⟩
  · calc
      (k / a) * β + hc * (1 + β) / a = (hc + (k + hc) * β) / a := by ring
      _ < c / a := div_lt_div_of_pos_right hlink ha
  · apply (lt_div_iff₀ (by linarith only [hβ] : 0 < 1 + β)).2
    have hkb := mul_pos hk hβ
    nlinarith only [hlink, hck, hkb]

-- At critical p=4, all five bounds hold without post-entry bootstrap assumptions.
example (B : Background) {s l H dH A Apt : ℝ} {h r : ℝ → ℝ}
    (hcrit : B.innerRate = (3 / 4) * B.outerRate) (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hApt : 0 ≤ Apt)
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ c β ε δ U₀ He : ℝ, 0 < c ∧ c < B.innerRate ∧ 0 < β ∧ 0 < ε ∧ 0 < δ ∧ 0 < U₀ ∧ 0 < He ∧
      ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        (∀ᵐ t ∂volume.restrict (Icc 0 δ), |f t| ≤ Apt * t ^ (-1 / 4 : ℝ)) →
        ∃ arrival : ℝ → ℝ,
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
            (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR le_rfl hfU) x), U ≤ U₀ → arrival U ≤ V → V ≤ (1 + β) * arrival U →
            let u : Icc 0 U := ⟨U, hU.le, le_rfl⟩
            let v : Icc 0 V := ⟨V, hV, le_rfl⟩
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
            let K := fun w t => horizonK (x.1 w t 0)
              (massField B.charge B.cosmological x.1 x.2.1 ν hx.choose w t) B.charge B.cosmological
            B.inner / 2 < x.1 u v 0 ∧ Real.exp (c * V) * |x.2.1 u v 1| < He ∧
              2 / 3 < -Real.exp (x.1 u v 2) / (4 * ν u v) ∧
              |K u v + B.innerRate| < ε ∧ |x.2.1 u v 2 - 2 * K u v| < ε := by
  dsimp only
  obtain ⟨_hc, c, β, ε, _hhc, _hhck, _htail, _heq, hc0, hck, hcs, hβ, _hβ8, _hlink,
    hε, hε8, _hεβ, _hnu, hℓ, hJ, hQ⟩ := exists_linked_inner_parameters B.innerRate_pos hks hl
  have hεk : ε < B.innerRate := by linarith only [hε8, B.innerRate_pos]
  have hca : c < B.outerRate := by linarith only [hck, hcrit, B.outerRate_pos]
  have hcb : c ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    simp only [ENNReal.toReal_ofNat]
    linarith only [hck, hcrit]
  obtain ⟨δ, _Δ, _Y, U₀, He, _C, _η, _qR, _Lk, _LF, _j, _D, _Olo, _Ohi, _Ly,
    hδ, _hδr, _hΔ, _hΔr, _hpot, _hY, _hYΔ, _hYcap, _hYclose, hU₀, _hUδ,
    hHe, _hC, _hη, _hqR, _hLk, _hLF, _hj, _hD, _hOlo, _hOhi, _hLy, _hLycap, hsolve⟩ :=
    B.exists_early_bounds (B.innerRate_pos.trans hks) hH hdH hdHR hA hApt hc0 hca hcs.le
      hε hεk hε hβ.le hℓ hJ hQ le_rfl hcb hc hb hrc hrb hrinit hrd hrdec hOut B.event B.inner_lt_event
  refine ⟨c, β, ε, δ, U₀, He, hc0, hck, hβ, hε, hδ, hU₀, hHe, ?_⟩
  intro f hf hfn hpoint
  obtain ⟨arrival, _hac, _haa, _hal, _hpos, _hscale, _hmatch, _hpre, _hchart, _hhistory, hbound⟩ :=
    hsolve f hf hfn (by simpa only [ENNReal.toReal_ofNat] using hpoint)
  refine ⟨arrival, ?_⟩
  intro U V hU hV hUR hfU x hx hUU hentry hwindow
  have hh := hbound U V hU hV hUR hfU hx hUU hentry hwindow
  refine ⟨?_, hh.1.trans_lt (half_lt_self hHe), ?_,
    hh.2.2.2.2.1.trans_lt (half_lt_self hε), hh.2.2.2.2.2.2.1.trans_lt (half_lt_self hε)⟩
  · linarith only [hh.2.2.2.1, B.inner_pos]
  · exact lt_of_lt_of_le (by norm_num : (2 / 3 : ℝ) < 3 / 4) hh.2.2.2.2.2.1

-- Critical p=4 solutions extend past gamma and carry its scalar trace on that actual extension.
example (B : Background) {s l H dH A Apt : ℝ} {h r : ℝ → ℝ}
    (hcrit : B.innerRate = (3 / 4) * B.outerRate) (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hApt : 0 ≤ Apt)
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ c β δ Δ U₀ C S η aJ Y qR Lk LF : ℝ, 0 < c ∧ c < B.innerRate ∧
      0 < β ∧ 0 < δ ∧ 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < C ∧ 0 < S ∧ 0 < η ∧ 0 < aJ ∧
      B.inner < Y ∧ 0 < qR ∧ 0 < Lk ∧ 0 < LF ∧ 0 < (B.innerRate / B.outerRate) * β ∧
      0 < Δ ∧ Δ ≤ B.inner / 4 ∧
      (∀ R ∈ Icc (B.inner - Δ) (B.inner + Δ),
        B.innerRate / 4 ≤ radialPotential R B.charge B.cosmological) ∧
      ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        (∀ᵐ t ∂volume.restrict (Icc 0 δ), |f t| ≤ Apt * t ^ (-1 / 4 : ℝ)) →
        ∃ arrival : ℝ → ℝ, (∀ u ∈ Ioc 0 U₀, 0 < arrival u) ∧
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f 4 (volume.restrict (Icc 0 U))), U ≤ U₀ → V ≤ (1 + β) * arrival U →
            ∃! x : WaveState U V,
              ∃ hx : IsWaveIntegral hU.le hV B.charge B.cosmological
                (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR le_rfl hfU) x,
                (∀ q v, 3 * B.inner / 4 ≤ x.1 q v 0) ∧
                (V = (1 + β) * arrival U →
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose;
                  -ν ⟨U, hU.le, le_rfl⟩ ⟨V, hV, le_rfl⟩ ≤
                    C * U ^ (-1 + (B.innerRate / B.outerRate) * β)) ∧
                (arrival U ≤ V → ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V,
                  0 < t → arrival t ≤ b →
                    |x.2.2 t b 1| ≤ S * |f t| + S * t ^ (-1 + c / B.outerRate)) ∧
                (arrival U ≤ V →
                  |x.1 ⟨U, hU.le, le_rfl⟩ ⟨V, hV, le_rfl⟩ 0 - B.inner| ≤ Δ / 2) ∧
                (arrival U ≤ V →
                  let u : Icc 0 U := ⟨U, hU.le, le_rfl⟩
                  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
                  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
                  let K := horizonK (x.1 u v 0) (m u v) B.charge B.cosmological
                  |(-Real.exp (x.1 u v 2) / (4 * ν u v)) - 1| + |x.2.1 u v 2 - 2 * K| ≤
                    S * Real.exp (-η * V) ∧
                  |m u v - B.mass| ≤ S * (1 + β * arrival U) * Real.exp (-η * arrival U) ∧
                  let J := ∫ t in arrival U..V, intervalExtension hV (x.1 u) t 0 *
                    (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)
                  0 ≤ J ∧ J ≤ S * β * arrival U * Real.exp (-aJ * arrival U) ∧
                  |x.1 u v 0 - B.inner| ≤ (Y - B.inner) * Real.exp (-qR * (V - arrival U)) +
                    ((4 / B.inner) * (S * (1 + β * arrival U) * Real.exp (-η * arrival U))) / qR ∧
                  (∫ t in arrival U..V, |intervalExtension hV (x.1 u) t 0 - B.inner|) ≤
                    ((Y - B.inner) + (4 / B.inner) * (β * arrival U) *
                      (S * (1 + β * arrival U) * Real.exp (-η * arrival U))) / qR ∧
                  |K + B.innerRate| ≤ Lk * ((Y - B.inner) * Real.exp (-qR * (V - arrival U)) +
                    (1 + 4 / B.inner / qR) * (S * (1 + β * arrival U) * Real.exp (-η * arrival U))) ∧
                  (∫ t in arrival U..V, |horizonK (intervalExtension hV (x.1 u) t 0)
                    (intervalExtension hV (m u) t) B.charge B.cosmological + B.innerRate|) ≤
                    Lk * ((Y - B.inner) / qR + (1 + 4 / B.inner / qR) * (β * arrival U) *
                      (S * (1 + β * arrival U) * Real.exp (-η * arrival U))) ∧
                  let R := x.1 u v 2 - x.1 u (projIcc 0 V hV (arrival U)) 2 +
                    2 * B.innerRate * (V - arrival U)
                  |R| ≤ S / η * Real.exp (-η * arrival U) +
                    2 * (Lk * ((Y - B.inner) / qR + (1 + 4 / B.inner / qR) * (β * arrival U) *
                      (S * (1 + β * arrival U) * Real.exp (-η * arrival U)))) ∧
                  Real.exp (x.1 u v 2) = Real.exp (x.1 u (projIcc 0 V hV (arrival U)) 2) *
                    Real.exp (-2 * B.innerRate * (V - arrival U) + R) ∧
                  (0 < β → V = (1 + β) * arrival U →
                    let ηg := min (η / 2) (qR * β) / (1 + β)
                    0 < ηg ∧ |x.2.1 u v 2 + 2 * B.innerRate| ≤
                      (S + 2 * Lk * ((Y - B.inner) +
                        (1 + 4 / B.inner / qR) * (S * (1 + 2 * β / η)))) * Real.exp (-ηg * V) ∧
                      |x.2.1 u v 0| ≤ (LF * ((Y - B.inner) +
                        (1 + 4 / B.inner / qR) * (S * (1 + 2 * β / η)))) * Real.exp (-ηg * V))) ∧
                (V = (1 + β) * arrival U → ∃ W : ℝ, ∃ hW : 0 ≤ W,
                  (1 + β) * arrival U < W ∧ ∃ y : WaveState U W,
                    IsWaveIntegral hU.le hW B.charge B.cosmological
                      (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0))
                      (horizonWaveVelocity B.mass B.charge B.cosmological W hc hi hrc hr0)
                      (incomingWaveVelocity hUR le_rfl hfU) y ∧
                    (∀ q v, 3 * B.inner / 8 ≤ y.1 q v 0) ∧
                    ∃ z ∈ Ioo 0 U, (∀ t ∈ Icc z U, (1 + β) * arrival t ∈ Icc 0 W) ∧
                      ∀ᵐ t ∂volume.restrict (Icc z U),
                        |y.2.2 t (projIcc 0 W hW ((1 + β) * arrival t)) 1| ≤
                          S * |f t| + S * t ^ (-1 + c / B.outerRate)) := by
  dsimp only
  obtain ⟨_hc, c, β, ε, _hhc, _hhck, _htail, _heq, hc0, hck, hcs, hβ, _hβ8, _hlink,
    hε, hε8, _hεβ, hnu, hℓ, hJ, hQ⟩ := exists_linked_inner_parameters B.innerRate_pos hks hl
  have hεk : ε < B.innerRate := by linarith only [hε8, B.innerRate_pos]
  have hca : c < B.outerRate := by linarith only [hck, hcrit, B.outerRate_pos]
  have hcb : c ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    simp only [ENNReal.toReal_ofNat]
    linarith only [hck, hcrit]
  obtain ⟨δ, Δ, Y, U₀, He, S, η, qR, Lk, LF, _j, _D, _Olo, _Ohi,
    hδ, _hδr, hΔ, hΔr, hpot, hY, _hYΔ, hU₀, hUδ, hU1,
    hHe, hS, hη, hqR, hLk, hLF, _hj, _hD, _hOlo, _hOhi, hsolve⟩ :=
    B.exists_early_wave (B.innerRate_pos.trans hks) hH hdH hdHR hA hApt hc0 hca hcs.le
      hε hεk hε hβ.le hℓ hJ hQ le_rfl hcb hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨c, β, δ, Δ, U₀, He, S, η, 2 * c - max 0 (2 * (B.innerRate + ε) + ε - 2 * c) * β,
    Y, qR, Lk, LF, hc0, hck, hβ, hδ, hU₀, hUδ, hHe, hS, hη, hJ, hY, hqR, hLk, hLF,
    mul_pos (div_pos B.innerRate_pos B.outerRate_pos) hβ, hΔ, hΔr, hpot, ?_⟩
  intro f hf hfn hpoint
  obtain ⟨arrival, hac, haa, _hal, hpos, _hscale, _hmatch, _hpre, hhistory, _hfloor, hex⟩ :=
    hsolve f hf hfn (by simpa only [ENNReal.toReal_ofNat] using hpoint)
  refine ⟨arrival, hpos, ?_⟩
  intro U V hU hV hUR hfU hUU hwindow
  obtain ⟨x, ⟨hx, hfloor, hearly, hmore⟩, _huniq⟩ := hex U V hU hV hUR hfU hUU hwindow
  refine ⟨x, ⟨hx, hfloor, ?_, (fun he => (hearly he).2.2.2.2.2.2.2.2.1),
    (fun he => (hearly he).2.1),
    (fun he => (hearly he).2.2.2.2.2.2.2.2.2), ?_⟩,
    fun y hy => hy.choose.incoming_unique hU.le hV hUR le_rfl hfU hx⟩
  · intro hgamma
    have hentry : arrival U ≤ V := by
      have hT := hpos U ⟨hU, hUU⟩
      rw [hgamma]
      nlinarith only [hβ, hT]
    have hg := (hearly hentry).2.2.2.2.2.2.2.1 hgamma
    have hexp : -1 + (B.innerRate / B.outerRate) * β ≤
        -1 + (2 * (2 / 3) * (B.innerRate - ε) / B.outerRate) * β :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hnu B.outerRate_pos.le) hβ.le)
    exact hg.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hU (hUU.trans hU1) hexp) hHe.le)
  · intro hgamma
    obtain ⟨H, hH, y, hy, _hmatch, hyr⟩ := hmore
    have hW := add_nonneg hV hH.le
    have hgap : (1 + β) * arrival U < V + H := by
      rw [← hgamma]
      linarith only [hH]
    have hgc : ContinuousWithinAt (fun t => (1 + β) * arrival t) (Ioo 0 U) U :=
      ((hac U ⟨hU, hUU⟩).mono (fun _ ht => ⟨ht.1, ht.2.le.trans hUU⟩)).const_mul (1 + β)
    have : NeBot (𝓝[Ioo 0 U] U) := right_nhdsWithin_Ioo_neBot hU
    obtain ⟨z, hz, hzW⟩ := ((show ∀ᶠ t in 𝓝[Ioo 0 U] U, t ∈ Ioo 0 U from
      self_mem_nhdsWithin).and (hgc.eventually_lt_const hgap)).exists
    have hcover (t : ℝ) (ht : t ∈ Icc z U) : (1 + β) * arrival t ∈ Icc 0 (V + H) := by
      have ht0 := hz.1.trans_le ht.1
      have hα : 0 ≤ 1 + β := by linarith only [hβ]
      exact ⟨mul_nonneg hα (hpos t ⟨ht0, ht.2.trans hUU⟩).le,
        (mul_le_mul_of_nonneg_left (haa.antitoneOn ⟨hz.1, hz.2.le.trans hUU⟩
          ⟨ht0, ht.2.trans hUU⟩ ht.1) hα).trans hzW.le⟩
    refine ⟨V + H, hW, hgap, y, hy, hyr, z, hz, hcover, ?_⟩
    filter_upwards [ae_mono (Measure.restrict_mono (Icc_subset_Icc hz.1.le le_rfl) le_rfl)
      (hhistory U (V + H) hU hW hUR hfU hy hUU), ae_restrict_mem measurableSet_Icc] with t ht htm
    have ht0 := hz.1.trans_le htm.1
    have hT := hpos t ⟨ht0, htm.2.trans hUU⟩
    have hentry : arrival t ≤ (1 + β) * arrival t := by nlinarith only [hβ, hT]
    have hh := ht ⟨(1 + β) * arrival t, hcover t htm⟩ ht0 hentry le_rfl
    simpa only [projIcc_of_mem hW (hcover t htm)] using hh

end EarlyJointClosure

section EnteredBootstrap

-- Different entry times are permitted, with no condition before a member enters.
example {V : ℝ} {f : ℝ × Fin 2 → ℝ} (hf : Continuous f)
    (hstart : ∀ k : Fin 2, (k.val : ℝ) ≤ V → f (k.val, k) < 0)
    (hstep : ∀ t ∈ Icc (0 : ℝ) V,
      (∀ q ∈ Icc (0 : ℝ) t, ∀ k : Fin 2, (k.val : ℝ) ≤ q → f (q, k) ≤ 0) →
      ∀ k : Fin 2, (k.val : ℝ) ≤ t → f (t, k) < 0) :
    ∀ t ∈ Icc (0 : ℝ) V, ∀ k : Fin 2, (k.val : ℝ) ≤ t → f (t, k) < 0 := by
  exact continuous_entered_bootstrap hf (continuous_of_discreteTopology)
    (fun k => Nat.cast_nonneg k.val) hstart hstep

-- An empty entered region at V=0 needs no fictitious initial condition at time zero.
example : ∀ t ∈ Icc (0 : ℝ) 0, ∀ _k : Fin 2, (1 : ℝ) ≤ t → (1 : ℝ) < 0 := by
  apply continuous_entered_bootstrap (f := fun _ : ℝ × Fin 2 => (1 : ℝ))
    (entry := fun _ => (1 : ℝ)) continuous_const continuous_const (fun _ => by norm_num)
  · intro k hk
    norm_num at hk
  · intro t ht _hpre k hkt
    linarith only [ht.2, hkt]

end EnteredBootstrap

section RadialDamping

-- Equal damping/forcing rates and an actual zero crossing need no exceptional case.
example :
    (∀ t ∈ Icc (0 : ℝ) 2, |(1 - t) * Real.exp (-t)| ≤ Real.exp (-t) * (1 + t)) ∧
    (∫ t in (0 : ℝ)..2, |(1 - t) * Real.exp (-t)|) ≤
      1 + ∫ t in (0 : ℝ)..2, Real.exp (-t) := by
  have hh := damped_scalar_bound (y := fun t => (1 - t) * Real.exp (-t))
    (c := fun _ => 1) (f := fun t => -Real.exp (-t)) (F := fun t => Real.exp (-t))
    (a := 0) (b := 2) (q := 1) (by norm_num) (by norm_num)
    (by fun_prop) continuousOn_const (by fun_prop) (by
      intro t _ht
      apply (((hasDerivAt_id t).const_sub 1).mul (hasDerivAt_id t).neg.exp).congr_deriv
      simp only [Pi.neg_apply, id_eq]
      ring)
    (fun _ _ => le_rfl) (fun t _ => by rw [abs_neg, abs_of_pos (Real.exp_pos _)])
  have hkernel : (fun s : ℝ => Real.exp s * Real.exp (-s)) = fun _ => 1 := by
    funext s
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simpa only [one_mul, sub_zero, neg_mul, neg_zero, Real.exp_zero,
    abs_one, mul_one, hkernel, intervalIntegral.integral_const, smul_eq_mul, div_one] using hh

-- The critical p=4 scalar estimate supplies the mass envelope through the actual flux law.
set_option maxHeartbeats 600000 in
example (B : Background) {κ₀ : ℝ} (hk : 0 < κ₀) :
    ∃ q : ℝ, 0 < q ∧ ∀ {U V H c : ℝ} {h r : ℝ → ℝ}
      (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
      (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
      (_hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
      (_hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
        (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
      {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
      (hx : IsWaveIntegral hU hV B.charge B.cosmological
        (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR le_rfl hf) x)
      (u : Icc 0 U) (a b : Icc 0 V), a ≤ b → 0 ≤ H → 0 ≤ c →
      x.2.1 u a 0 < 0 →
      (∀ v ∈ Icc a b, x.1 u v 0 ∈ Icc (B.inner / 2) ((B.inner + B.event) / 2)) →
      (∀ v ∈ Icc a b, |x.2.1 u v 1| ≤ H * Real.exp (-c * v)) →
      let ν := radialNuField hV B.charge B.cosmological
        (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
      let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
      let P := ((B.inner + B.event) / 2) ^ 2 * H ^ 2 / (2 * κ₀)
      (∀ v ∈ Icc a b, κ₀ ≤ -Real.exp (x.1 u v 2) / (4 * ν u v)) →
        (∫ t in (a : ℝ)..b, |intervalExtension hV (x.1 u) t 0 - B.inner|) ≤
          (|x.1 u a 0 - B.inner| + (4 / B.inner) * ((b : ℝ) - a) *
            (|m u a - B.mass| + P * ((b : ℝ) - a) * Real.exp (-(2 * c) * a))) / q := by
  obtain ⟨q, hq, hbound⟩ := B.exists_inner_radius_damping hk
  refine ⟨q, hq, ?_⟩
  intro U V H c h r hU hV hUR hc hi hrc hr0 hφ hrd f hf x hx u a b hab hH hc0 ha hrad hscalar
  dsimp only
  intro hkappa
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
  let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
  let P := ((B.inner + B.event) / 2) ^ 2 * H ^ 2 / (2 * κ₀)
  let E := |m u a - B.mass| + P * ((b : ℝ) - a) * Real.exp (-(2 * c) * a)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hm (v : Icc 0 V) (hv : v ∈ Icc a b) : |m u v - B.mass| ≤ E := by
    have hi := hx.trapped_mass_increment_bound hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
      hk hH hc0 u a v hv.1 ha (hrad a (left_mem_Icc.2 hab)).2
      (fun w hw => hscalar w ⟨hw.1, hw.2.trans hv.2⟩)
      (fun w hw => hkappa w ⟨hw.1, hw.2.trans hv.2⟩)
    have hinc : m u v - m u a ≤ P * ((b : ℝ) - a) * Real.exp (-(2 * c) * a) :=
      hi.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_le_sub_right (show (v : ℝ) ≤ b from hv.2) (a : ℝ)) hP)
        (Real.exp_pos _).le)
    calc
      _ = |(m u a - B.mass) + (m u v - m u a)| := by congr 1; ring
      _ ≤ |m u a - B.mass| + |m u v - m u a| := abs_add_le _ _
      _ ≤ E := by rw [abs_of_nonneg hi.1]; exact add_le_add le_rfl hinc
  have hh := (hbound hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf hx u a b hab hrad
    (fun _ => E) continuousOn_const hkappa hm).2
  simpa only [intervalIntegral.integral_const, smul_eq_mul, E, mul_assoc] using hh

end RadialDamping

-- Equal restoring and reduced source rates require no separate resonance argument.
example {T C D L Z ℓ K k : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hL : 0 ≤ L) (hZ : 0 ≤ Z)
    (hp : |ℓ - 2 * K| ≤ C * Real.exp (-2 * (2 * T)))
    (hk : |K + k| ≤ L * (Z * Real.exp (-T) + D * (C * (1 + T) * Real.exp (-2 * T)))) :
    |ℓ + 2 * k| ≤ (C + 2 * L * (Z + D * (C * 2))) * Real.exp (-T) := by
  have hh := gamma_conformal_bound (β := 1) (η := 2) (q := 1)
    (by norm_num) (by norm_num) (by norm_num) hC hD hL hZ hT
    (by simpa only [one_add_one_eq_two] using hp)
    (by simpa only [one_mul, neg_one_mul] using hk)
  have hb := hh.2
  norm_num at hb
  convert hb using 1
  congr 2
  ring

-- The actual p=4 outgoing constraint retains the linear factor when damping and forcing rates agree.
example {M e Λ U V c H R : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (hc0 : 0 < c) (hH : 0 ≤ H) (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b)
    (hR : ∀ w ∈ Icc a b, x.1 u w 0 ≤ R)
    (hscalar : ∀ w ∈ Icc a b, |x.2.1 u w 1| ≤ H * Real.exp (-c * w))
    (hell : ∀ w ∈ Icc a b, x.2.1 u w 2 ≤ -(2 * c)) :
    |x.2.1 u b 0| ≤ Real.exp (-(2 * c) * ((b : ℝ) - a)) *
      (|x.2.1 u a 0| + ((b : ℝ) - a) * (R * H ^ 2 * Real.exp (-(2 * c) * a))) := by
  have hh := (hx.lambda_damping hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
    (by positivity : 0 < 2 * c) hc0 hH u a b hab hR hscalar hell).1 b (right_mem_Icc.2 hab)
  have hkernel (t : ℝ) : Real.exp ((2 * c) * (t - a)) * (R * H ^ 2 * Real.exp (-(2 * c) * t)) =
      R * H ^ 2 * Real.exp (-(2 * c) * a) := by
    calc
      _ = R * H ^ 2 * Real.exp ((2 * c) * (t - a) + (-(2 * c) * t)) := by
        rw [Real.exp_add]
        ring
      _ = _ := by congr 2; ring
  simp_rw [hkernel] at hh
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh

-- A p=4 actual solution transfers the gamma power to a late row and strictly improves its radius floor.
example (B : Background) {U V R φ₀ Δ N β : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut (incomingWaveVelocity hUR le_rfl hf) x)
    (hΔ : 0 < Δ) (hΔr : Δ ≤ B.inner / 4) (hN : 0 ≤ N) (hβ : 0 < β)
    (hpot : ∀ r ∈ Icc (B.inner - Δ) (B.inner + Δ),
      B.innerRate / 4 ≤ radialPotential r B.charge B.cosmological)
    (z u : Icc 0 U) (v : Icc 0 V) (hz : 0 < (z : ℝ)) (hzu : z ≤ u)
    (γ : Icc 0 U → Icc 0 V) (hγ : ∀ w ∈ Icc z u, γ w ≤ v)
    (hleft : |x.1 z v 0 - B.inner| ≤ Δ / 2)
    (hrγ : ∀ w ∈ Icc z u, |x.1 w (γ w) 0 - B.inner| ≤ Δ / 2)
    (hnγ : ∀ w ∈ Icc z u,
      -radialNuField hV B.charge B.cosmological (incomingWaveCurve hU hUR le_rfl hf φ₀)
        x.1 hx.choose w (γ w) ≤ N * (w : ℝ) ^ (-1 + (B.innerRate / B.outerRate) * β))
    (hstrip : ∀ w ∈ Icc z u, ∀ t ∈ Icc (γ w) v,
      x.1 w t 0 ∈ Icc (B.inner - Δ) (B.inner + Δ))
    (hsmall : 2 * N * (u : ℝ) ^ ((B.innerRate / B.outerRate) * β) /
      ((B.innerRate / B.outerRate) * β) < Δ / 2) :
    (∀ w ∈ Icc z u,
      -radialNuField hV B.charge B.cosmological (incomingWaveCurve hU hUR le_rfl hf φ₀)
        x.1 hx.choose w v ≤ 2 * N * (w : ℝ) ^ (-1 + (B.innerRate / B.outerRate) * β)) ∧
      B.inner - Δ < x.1 u v 0 := by
  have hh := hx.late_radius_bound B hU hV hUR le_rfl hf hΔ hΔr hN
    (mul_pos (div_pos B.innerRate_pos B.outerRate_pos) hβ) hpot z u v hz hzu hleft
    (fun w hw => ⟨γ w, hγ w hw, hrγ w hw, hnγ w hw, hstrip w hw⟩)
  exact ⟨hh.1, hh.2.2 hsmall⟩

-- The p=4 endpoint keeps early energy and late estimates on the same physical family.
set_option maxRecDepth 4096 in
example (B : Background) {s l H Hlo dH A Apt Ebudget : ℝ} {h r : ℝ → ℝ}
    (hcrit : B.innerRate = (3 / 4) * B.outerRate)
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
      ∀ f : ℕ → ℝ → ℝ, ∀ hf : ∀ n, MemLp (f n) 4 (volume.restrict (Icc 0 δ)),
        (∀ n, (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A) →
        (∀ n, ∀ᵐ t ∂volume.restrict (Icc 0 δ), |f n t| ≤ Apt * t ^ (-1 / (4 : ℝ))) →
        let hfU := fun n => (hf n).mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl hUδ) le_rfl)
        ∃ arrival : ℕ → ℝ → ℝ, ∃ X : (n : ℕ) → (T : Ici (0 : ℝ)) → WaveState U T,
          (∀ n, ContinuousOn (arrival n) (Ioc 0 U) ∧ StrictAntiOn (arrival n) (Ioc 0 U) ∧
            Tendsto (arrival n) (𝓝[>] (0 : ℝ)) atTop ∧ ∀ u ∈ Ioc 0 U, 0 < arrival n u) ∧
          (∀ n u, u ∈ Ioc 0 U → j ≤ u * Real.exp (B.outerRate * arrival n u) ∧
            u * Real.exp (B.outerRate * arrival n u) ≤ D) ∧
          (∀ n (T : Ici (0 : ℝ)), IsWaveIntegral hU.le T.property B.charge B.cosmological
            (incomingWaveCurve hU.le hUR le_rfl (hfU n) (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological T hc hi hrc hr0)
            (incomingWaveVelocity hUR le_rfl (hfU n)) (X n T)) ∧
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
                    (incomingWaveCurve hU.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n V).1 hr
                  let v := projIcc 0 (V : ℝ) V.property (ψ t)
                  Real.exp (-1) * (-B.F Y') / B.outerRate ≤ (u : ℝ) * (-ν u v) ∧
                  (u : ℝ) * (-ν u v) ≤ Real.exp 1 * (-B.F Y') / B.outerRate ∧
                  0 < -(X n V).2.1 u v 0 ∧ -(X n V).2.1 u v 0 ≤ Laux * ((Y' : ℝ) - B.inner)) ∧
          (∀ (ℓ : ℕ → ℝ) (P : ℕ → ℝ →ᵇ ℝ),
            (∀ n, f n = logarithmicIncoming (1 - 1 / (4 : ℝ)) (ℓ n) (P n)) →
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
                    (incomingWaveCurve hU.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n V).1 hr)
                  (g n) Tr β Y' Laux (Saux Y')) ∧
              (∀ (m : ℕ → ℝ) (Q : ℕ → ℝ →ᵇ ℝ), P 0 = 0 →
                (∀ n t, HasDerivAt (P n) (Q n t) t) → (∀ n, Integrable (fun t => Q n t ^ 2)) →
                Tendsto (fun n => ∫ t, Q n t ^ 2) atTop (𝓝 0) →
                Tendsto (fun n => m n - ℓ n) atTop atTop → (∀ n t, t ≤ m n → P n t = 0) →
                Tendsto (fun n => (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
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
                            (incomingWaveCurve hU.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n V).1 hr
                          ζ n t = Real.exp (B.innerRate * t) * gY n t *
                            ((r 0 - gY n t) * f n (gY n t) +
                              scalarTransportCorrection V.property ν (X n V).2.1 u v) / B.criticalWeight Y') ∧
                    (∀ n,
                      let A := fun t => B.criticalWeight Y' /
                        (Real.exp (-1) * (-B.F Y') / B.outerRate) * |ζ n t|
                      ContinuousOn A (Ici lY) ∧ MemLp A 2 (volume.restrict (Ici lY)) ∧
                        (∀ (V : Ici (0 : ℝ)) (hr : ∀ q v, (X n V).1 q v 0 ≠ 0),
                          let ν := radialNuField V.property B.charge B.cosmological
                            (incomingWaveCurve hU.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n V).1 hr
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
                      (incomingWaveCurve hU.le hUR (p := 4) le_rfl (hfU n) (horizonPhi h r 0)) (X n V).1 (hr n V)
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
                        (incomingWaveCurve hU.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n V).1 hr
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
                    (incomingWaveCurve hU.le hUR (by norm_num : (4 : ℝ≥0∞) ≤ 4) (hfU n)
                      (horizonPhi h r 0)) (X n V).1 (hr n V)
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
                (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
                  Tendsto Z atTop (𝓝 (Z 0)) ∧
                  TendstoUniformlyOn (fun n => renormalizedWaveRow hε.le B.innerRate (X n))
                    (renormalizedWaveRow hε.le B.innerRate (X 0)) atTop (Ici 0) ∧
                  Tendsto (fun n => waveAmplitude (Z n)) atTop (𝓝 (waveAmplitude (Z 0))) ∧
                  TendstoUniformlyOn (fun n t => waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X n) t))
                    (fun t => waveAmplitude (renormalizedWaveRow hε.le B.innerRate (X 0) t)) atTop (Ici 0))) ∧
          (∃ hr : ∀ n (T : Ici (0 : ℝ)) u v, (X n T).1 u v 0 ≠ 0,
            let ν := fun n (T : Ici (0 : ℝ)) => radialNuField T.property B.charge B.cosmological
              (incomingWaveCurve hU.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n T).1 (hr n T)
            let W := fun n (T : Ici (0 : ℝ)) => radialProductField T.property B.charge B.cosmological
              (incomingWaveCurve hU.le hUR le_rfl (hfU n) (horizonPhi h r 0)) (X n T).1 (hr n T)
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
                  (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
                    Tendsto Zw atTop (𝓝 (Zw 0)) ∧
                    TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (W n))
                      (scalarBoundaryRow hε.le (W 0)) atTop (Ici 0) ∧
                    Tendsto Zν atTop (𝓝 (Zν 0)) ∧
                    TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (ν n))
                      (scalarBoundaryRow hε.le (ν 0)) atTop (Ici 0)) ∧
                  (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
                    MassCoefficientControl (fun n => massCoefficientRow hε.le B.innerRate (X n) (ν n)))) ∧
            (∀ ε (hε : 0 < ε), ε ≤ U →
              ∃ T₀ Cζ : ℝ, 0 ≤ T₀ ∧ 0 ≤ Cζ ∧ ∃ Zζ : ℕ → C(Icc ε U, ℝ),
                (∀ n, Tendsto (scalarBoundaryRow hε.le (ζ n)) atTop (𝓝 (Zζ n))) ∧
                (∀ n t, T₀ ≤ t → ‖scalarBoundaryRow hε.le (ζ n) t - Zζ n‖ ≤
                  Cζ * Real.exp (-cL * t)) ∧
                (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
                  Tendsto Zζ atTop (𝓝 (Zζ 0)) ∧
                  TendstoUniformlyOn (fun n => scalarBoundaryRow hε.le (ζ n))
                    (scalarBoundaryRow hε.le (ζ 0)) atTop (Ici 0))) ∧
            (f 0 = 0 → ∀ ε (hε : 0 < ε) (hεU : ε ≤ U),
              TransverseBoundaryGeometry hε.le hεU B.innerRate (X 0) (ν 0))) ∧
          (∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T),
            waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
              le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X n T) = X n S) ∧
          (f 0 = 0 → Tendsto (fun n => (eLpNorm (f n) 4 (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) →
            ∀ T : Ici (0 : ℝ), Tendsto (fun n => X n T) atTop (𝓝 (X 0 T))) := by
  have hh := B.exists_critical_late_wave (p := 4) le_rfl (by norm_num) (by norm_num; exact hcrit)
    hks hl hH hHlo hdH hdHR hA hApt hEbudget hc hb hlo hrc hrb hrinit hrd hrdec hOut Ucap hUcap
  rw [ENNReal.toReal_ofNat] at hh
  exact hh

-- A moving entry time may depend on the incoming coordinate without changing the transport null set.
example {U V R₀ φ₀ e Λ ρ c H : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R₀)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) (hρ : 0 < ρ) (hc : 0 < c) (hH : 0 ≤ H)
    (γ : ℝ → Icc 0 V) :
    ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ b : Icc 0 V, γ t ≤ b → ∀ N : ℝ, 0 ≤ N →
      let u := projIcc 0 U hU t
      let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) x.1 hx.choose
      ρ ≤ x.1 u b 0 → x.1 u (γ t) 0 ≤ 2 * ρ →
      (∀ v ∈ Icc (γ t) b, |ν u v| ≤ N) →
      (∀ v ∈ Icc (γ t) b, |x.2.1 u v 1| ≤ H * Real.exp (-c * v)) →
        |x.2.2 t b 1| ≤ 2 * |x.2.2 t (γ t) 1| + N * H / (ρ * c) * Real.exp (-c * (γ t)) := by
  filter_upwards [hx.scalar_segment_bound hU hV hUR le_rfl hf (R := 2 * ρ) hρ hc hH] with t ht
  intro b htb N hN
  simpa only [mul_div_cancel_right₀ _ hρ.ne'] using ht (γ t) b htb N hN

-- At the critical exponent, the normalized kernel retains the exact incoming 3/4 power.
example {U z u : ℝ} {f : ℝ → ℝ} (hz : 0 < z) (hzu : z ≤ u) (huU : u ≤ U)
    (hf : MemLp f 4 (volume.restrict (Icc 0 U))) :
    (∫ t in z..u, (z ^ (3 / 2 : ℝ) * t ^ (-(3 / 2) : ℝ)) * |f t|) ≤
      (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal * z ^ (3 / 4 : ℝ) := by
  have hh := power_kernel_holder (p := 4) (q := 4 / 3) (σ := 3 / 2) hz hzu huU
    (by rw [Real.holderConjugate_iff]; norm_num) (by norm_num) (f := f)
  norm_num at hh
  exact hh hf

-- Arrival scaling removes the time weight and leaves a coefficient vanishing with the width.
example {z U ω v σ s δ L G ρ D : ℝ} (hz : 0 < z) (hU : 0 ≤ U) (hs : 0 < s)
    (hsσ : s < σ) (hδ : 0 < δ) (hL : 0 ≤ L) (hG : 0 ≤ G) (hρ : 0 < ρ)
    (hscale : z * Real.exp (ω * v) ≤ D) :
    Real.exp ((ω * s) * v) * (L / ρ * (G * U ^ δ * z ^ s / (σ - s))) ≤
      (L * G * D ^ s / (ρ * (σ - s))) * U ^ δ ∧
    Tendsto (fun u : ℝ => (L * G * D ^ s / (ρ * (σ - s))) * u ^ δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hw := Real.rpow_le_rpow (mul_nonneg hz.le (Real.exp_pos _).le) hscale hs.le
  rw [Real.mul_rpow hz.le (Real.exp_pos _).le, ← Real.exp_mul,
    show ω * v * s = (ω * s) * v by ring] at hw
  constructor
  · have hh := mul_le_mul_of_nonneg_left hw
      (show 0 ≤ L * G * U ^ δ / (ρ * (σ - s)) by positivity)
    calc
      _ = (L * G * U ^ δ / (ρ * (σ - s))) * (z ^ s * Real.exp ((ω * s) * v)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (L * G * U ^ δ / (ρ * (σ - s))) * D ^ s := hh
      _ = _ := by ring
  · have hc := ((Real.continuous_rpow_const hδ.le).const_mul
      (L * G * D ^ s / (ρ * (σ - s)))).continuousAt (x := (0 : ℝ)) |>.tendsto
    simpa only [Real.zero_rpow hδ.ne', mul_zero] using hc.mono_left nhdsWithin_le_nhds

-- The polynomial-exponential remainder is bounded uniformly over the whole time axis.
example {t : ℝ} (ht : 0 ≤ t) : t * ((1 + t) * Real.exp (-2 * t)) ≤ 2 := by
  have hh := quadratic_mul_exp_bound (η := 2) (β := 1) (by norm_num) (by norm_num) ht
  norm_num at hh ⊢
  exact hh

example {η t : ℝ} (hη : 0 < η) (ht : 0 ≤ t) :
    (η / 2 * t) * ((1 + η / 2 * t) * Real.exp (-η * t)) ≤ 2 := by
  have hh := quadratic_mul_exp_bound (β := η / 2) hη (by positivity) ht
  have he : 2 * (η / 2) / η = 1 := by field_simp
  rw [he] at hh
  norm_num at hh
  simpa only [neg_mul] using hh

-- Critical k/a=3/4 yields the exact incoming corner power -5/2.
example {u s v ellY ellV R j D Olo Ohi : ℝ}
    (hu : 0 < u) (hj : 0 < j) (hOhi : 0 ≤ Ohi)
    (hscale : j ≤ u * Real.exp (4 * s) ∧ u * Real.exp (4 * s) ≤ D)
    (hmatch : Olo ≤ u * Real.exp ellY ∧ u * Real.exp ellY ≤ Ohi)
    (hrem : |ellV - ellY + 6 * (v - s)| ≤ R) :
    (Real.exp (-R) * Olo * j ^ (3 / 2 : ℝ)) *
        (u ^ (-5 / 2 : ℝ) * Real.exp (-6 * v)) ≤ Real.exp ellV ∧
      Real.exp ellV ≤ (Real.exp R * Ohi * D ^ (3 / 2 : ℝ)) *
        (u ^ (-5 / 2 : ℝ) * Real.exp (-6 * v)) := by
  have hh := corner_lapse_bounds (a := 4) (k := 3) hu (by norm_num) (by norm_num)
    hj hOhi hscale hmatch (by norm_num; exact hrem)
  norm_num at hh ⊢
  exact hh

-- A zero finite-tail bound gives a literal constant limit, not only a subsequential limit.
example {f : ℝ → ℝ}
    (h : ∀ s ≥ (0 : ℝ), ∀ t ≥ s, |f s - f t| ≤ 0) :
    ∃ z : ℝ, Tendsto f atTop (𝓝 z) ∧ ∀ s ≥ (0 : ℝ), f s = z := by
  obtain ⟨z, hz, hb⟩ := exists_limit_of_tail_bound
    (show Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0) from tendsto_const_nhds)
    (T := 0) (f := f) (fun s hs t ht => by simpa only [Real.dist_eq] using h s hs t ht)
  exact ⟨z, hz, fun s hs => dist_le_zero.1 (hb s hs)⟩

-- Vanishing radial flux preserves r*nu on every finite segment.
example {U V e Λ : ℝ} (hV : 0 ≤ V)
    (zIn : C(Icc 0 U, WaveVector)) (z : WaveRectangle U V) (hr : ∀ u v, z u v 0 ≠ 0)
    (u : Icc 0 U) (a b : Icc 0 V) (hab : a ≤ b)
    (hzero : ∀ t ∈ Icc a b, radialFluxField e Λ z hr u t = 0) :
    radialProductField hV e Λ zIn z hr u b = radialProductField hV e Λ zIn z hr u a := by
  have hh := radialProductField_tail_bound (e := e) (Λ := Λ) (hV := hV) zIn z hr u a b hab
    (C := 0) (η := 1) (by norm_num) (by norm_num) (fun t ht => by simp only [hzero t ht, abs_zero, zero_mul, le_refl])
  exact sub_eq_zero.1 (abs_nonpos_iff.1 (by simpa only [zero_div, zero_mul] using hh))

-- The normalization contributes exactly exp(2*k*t) to the conformal amplitude.
example {U ε k t : ℝ} (hε : 0 ≤ ε) (u : Icc ε U) :
    waveAmplitude (renormalizedWaveRow hε k (fun T => (0 : WaveState U T)) t) u = Real.exp (2 * k * t) := by
  change Real.exp (0 + if (2 : Fin 3) = 2 then 2 * k * t else 0) = _
  simp only [ite_true, zero_add]

-- Concatenation changes the measure interval and is bounded in the L2 norm.
example (f : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 2)))
    (g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 3))) :
    ‖intervalJoinLp (by norm_num : (0 : ℝ) ≤ 3) f g‖ ≤ ‖f‖ + ‖g‖ :=
  intervalJoinLp_norm_le (by norm_num) f g

-- A zero-width first piece does not lose the transverse L2 class on reassembly.
example (x : WaveState (0 + 2) 3) :
    waveJoin (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2)
      (waveTranslate (a := 0) (U := 0) (b := 0) (V := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x)
      (waveTranslate (a := 0) (U := 2) (b := 0) (V := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x) = x :=
  waveJoin_reassemble (by norm_num) (by norm_num) x

-- A zero-time first piece retains both characteristic derivatives.
example (x : WaveState 2 (0 + 3)) :
    waveSplice (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 3)
      (waveTranslate (a := 0) (U := 2) (b := 0) (V := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x)
      (waveTranslate (a := 0) (U := 2) (b := 0) (V := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) x) = x :=
  waveSplice_reassemble (by norm_num) (by norm_num) x

-- The finite theorem admits widths larger than one, with no local smallness premise.
example {e Λ ρ M : ℝ}
    {z : ℕ → C(Icc (0 : ℝ) 4, WaveVector)} {z' : C(Icc (0 : ℝ) 4, WaveVector)}
    {v : ℕ → C(Icc (0 : ℝ) 2, WaveVector)} {v' : C(Icc (0 : ℝ) 2, WaveVector)}
    {u : ℕ → Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 4))}
    {u' : Lp WaveVector 2 (volume.restrict (Icc (0 : ℝ) 4))} {x : ℕ → WaveState 4 2} {y : WaveState 4 2}
    (hx : ∀ n, IsWaveIntegral (by norm_num) (by norm_num) e Λ (z n) (v n) (u n) (x n))
    (hy : IsWaveIntegral (by norm_num) (by norm_num) e Λ z' v' u' y) (hρ : 0 < ρ)
    (hxr : ∀ n s t, ρ ≤ (x n).1 s t 0) (hyr : ∀ s t, ρ ≤ y.1 s t 0)
    (hxn : ∀ n, ‖x n‖ ≤ M) (hyn : ‖y‖ ≤ M)
    (hz : Tendsto z atTop (𝓝 z')) (hv : Tendsto v atTop (𝓝 v')) (hu : Tendsto u atTop (𝓝 u')) :
    Tendsto x atTop (𝓝 y) :=
  IsWaveIntegral.tendsto_of_bounds hx hy hρ hxr hyr hxn hyn hz hv hu

-- At p=4 the physical convergence theorem derives the full-state bound internally.
example {M e Λ U V : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hU1 : U ≤ 1) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {ρ : ℝ} (hρ : 0 < ρ) {f : ℕ → ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 4 (volume.restrict (Icc 0 U)))
    (hfn : ∀ n, (eLpNorm (f n) 4 (volume.restrict (Icc 0 U))).toReal ≤ 3)
    (hlim : Tendsto (fun n => (eLpNorm (f n) 4 (volume.restrict (Icc 0 U))).toReal) atTop (𝓝 0))
    {x : ℕ → WaveState U V} {y : WaveState U V}
    (hx : ∀ n, IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl (hf n) (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl (hf n)) (x n))
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR (p := 4) le_rfl (f := 0) MemLp.zero (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR (p := 4) le_rfl (f := 0) MemLp.zero) y)
    (hxr : ∀ n s t, ρ ≤ (x n).1 s t 0) (hyr : ∀ s t, ρ ≤ y.1 s t 0) :
    Tendsto x atTop (𝓝 y) :=
  IsWaveIntegral.horizon_tendsto_zero_incoming hU hU1 hV hUR hc hi hrc hr0 hφ hrd hρ
    (by norm_num) le_rfl hf hfn hlim hx hy hxr hyr

-- The common-tail theorem derives convergence of the endpoint traces as well.
example {F : ℕ → ℝ → C(Icc (1 : ℝ) 2, ℝ)} {f : ℝ → C(Icc (1 : ℝ) 2, ℝ)}
    {Z : ℕ → C(Icc (1 : ℝ) 2, ℝ)} {z : C(Icc (1 : ℝ) 2, ℝ)}
    (hF : ∀ n t, 0 ≤ t → ‖F n t - Z n‖ ≤ Real.exp (-t))
    (hf : ∀ t, 0 ≤ t → ‖f t - z‖ ≤ Real.exp (-t))
    (hfinite : ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn F f atTop (Icc 0 T)) :
    Tendsto Z atTop (𝓝 z) ∧ TendstoUniformlyOn F f atTop (Ici 0) := by
  apply uniform_convergence_of_common_tail (b := fun t => Real.exp (-t))
  · exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  · simpa only [dist_eq_norm] using hF
  · simpa only [dist_eq_norm] using hf
  · exact hfinite

-- Prepending the zero reference preserves every incoming hypothesis at the same width.
example {p : ℝ≥0∞} {δ A Apt : ℝ} (hA : 0 ≤ A) (hApt : 0 ≤ Apt) {f : ℕ → ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) p (volume.restrict (Icc 0 δ)))
    (hfn : ∀ n, (eLpNorm (f n) p (volume.restrict (Icc 0 δ))).toReal ≤ A)
    (hpt : ∀ n, ∀ᵐ u ∂volume.restrict (Icc 0 δ), |f n u| ≤ Apt * u ^ (-1 / p.toReal))
    (hlim : Tendsto (fun n => (eLpNorm (f n) p
      (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0)) :
    let g : ℕ → ℝ → ℝ := fun n => Nat.casesOn n 0 f
    g 0 = 0 ∧
      (∀ n, MemLp (g n) p (volume.restrict (Icc 0 δ))) ∧
      (∀ n, (eLpNorm (g n) p (volume.restrict (Icc 0 δ))).toReal ≤ A) ∧
      (∀ n, ∀ᵐ u ∂volume.restrict (Icc 0 δ), |g n u| ≤ Apt * u ^ (-1 / p.toReal)) ∧
      Tendsto (fun n => (eLpNorm (g n) p
        (volume.restrict (Icc 0 δ))).toReal) atTop (𝓝 0) := by
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact MemLp.zero
    | succ n => exact hf n
  · intro n
    cases n with
    | zero =>
      change (eLpNorm (0 : ℝ → ℝ) p (volume.restrict (Icc 0 δ))).toReal ≤ A
      simpa only [eLpNorm_zero, ENNReal.toReal_zero] using hA
    | succ n => exact hfn n
  · intro n
    cases n with
    | zero =>
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      change |(0 : ℝ)| ≤ Apt * u ^ (-1 / p.toReal)
      simpa only [abs_zero] using mul_nonneg hApt (Real.rpow_nonneg hu.1 (-1 / p.toReal))
    | succ n => exact hpt n
  · exact (tendsto_add_atTop_iff_nat 1).1 hlim

-- Removing that first entry retains uniform convergence over the full half-line.
example {E : Type*} [PseudoMetricSpace E] {F : ℕ → ℝ → E} {Z : ℕ → E}
    (hZ : Tendsto Z atTop (𝓝 (Z 0)))
    (hF : TendstoUniformlyOn F (F 0) atTop (Ici (0 : ℝ))) :
    Tendsto (fun n => Z (n + 1)) atTop (𝓝 (Z 0)) ∧
      TendstoUniformlyOn (fun n t => F (n + 1) t) (F 0) atTop (Ici (0 : ℝ)) := by
  refine ⟨hZ.comp (tendsto_add_atTop_nat 1), ?_⟩
  intro u hu
  exact (tendsto_add_atTop_nat 1).eventually (hF u hu)

-- Continuous-field convergence alone controls both radial flux representatives.
example {U V e Λ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {z : ℕ → C(Icc 0 U, WaveVector)} {v : ℕ → C(Icc 0 V, WaveVector)}
    {u : ℕ → Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : ℕ → WaveState U V}
    (hx : ∀ n, IsWaveIntegral hU hV e Λ (z n) (v n) (u n) (x n))
    (hlim : Tendsto (fun n => (x n).1) atTop (𝓝 (x 0).1)) :
    Tendsto (fun n => radialNuField hV e Λ (z n) (x n).1 (hx n).choose) atTop
        (𝓝 (radialNuField hV e Λ (z 0) (x 0).1 (hx 0).choose)) ∧
      Tendsto (fun n => radialProductField hV e Λ (z n) (x n).1 (hx n).choose) atTop
        (𝓝 (radialProductField hV e Λ (z 0) (x 0).1 (hx 0).choose)) :=
  IsWaveIntegral.radial_tendsto hx (hx 0) (fun n => (hx n).choose) (hx 0).choose hlim

-- The boundary-row transfer includes singleton incoming and zero-time intervals.
example (X : ℕ → (T : Ici (0 : ℝ)) → C(Icc (0 : ℝ) 1, C(Icc 0 (T : ℝ), ℝ)))
    (hX : ∀ n (S T : Ici (0 : ℝ)) (hST : S ≤ T) u v,
      X n S u v = X n T u ⟨v, v.property.1, v.property.2.trans hST⟩)
    (hlim : Tendsto (fun n => X n ⟨0, by norm_num⟩) atTop (𝓝 (X 0 ⟨0, by norm_num⟩))) :
    TendstoUniformlyOn (fun n => scalarBoundaryRow (U := 1) (ε := 1) (by norm_num) (X n))
      (scalarBoundaryRow (by norm_num) (X 0)) atTop (Icc (0 : ℝ) 0) :=
  scalarBoundaryRow_tendstoUniformlyOn (by norm_num) X (X 0) hX (hX 0) ⟨0, by norm_num⟩ hlim


-- The causal kernel has the sharp terminal-time-independent row mass.
example {V d : ℝ} (hV : 0 ≤ V) (hd : 0 < d) (v : Icc 0 V) :
    causalExpIntegral hV d (ContinuousMap.const _ 1) v ≤ 1 / d := by
  rw [causalExpIntegral_one hV hd.ne']
  apply div_le_div_of_nonneg_right _ hd.le
  linarith only [Real.exp_pos (-d * (v : ℝ))]

-- A zero-length history remains zero at every rate.
example {V d : ℝ} (hV : 0 ≤ V) (M : C(Icc 0 V, ℝ)) :
    causalExpIntegral hV d M ⟨0, le_rfl, hV⟩ = 0 := by
  simp only [causalExpIntegral, intervalIntegral.integral_same]

-- At critical p=4, the physical outer feedback retains the exact a-k=a/4 rate.
example {m e Λ a k ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (ha : 0 < a) (hcrit : k = (3 / 4) * a) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (k * t) * |h t| ≤ H)
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass m h t) e Λ| ≤ W) :
    ∃ δ L N : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧ 0 ≤ L ∧ 0 < N ∧
      L * N * δ / (ρ ^ 2 * (a - k)) ≤ 1 / 4 ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
        U * Real.exp (a * V) ≤ δ →
        ∀ M : C(Icc 0 V, ℝ),
          (∀ (u : Icc 0 U) (v : Icc 0 V), Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v) →
          let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
          (∀ (u : Icc 0 U) (v : Icc 0 V),
            (u : ℝ) * Real.exp (k * v) * |scalarTransportCorrection hV ν x.2.1 u v| ≤
              (N * δ / ρ) * causalExpIntegral hV (a - k) M v) ∧
            ∀ (u : Icc 0 U) (v : Icc 0 V),
              Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤
                Real.exp (k * v) * |h v| + (L * r 0 / ρ) * Real.exp (k * v) *
                  (∫ t in (0 : ℝ)..u, |f t|) +
                (L * N * δ / ρ ^ 2) * causalExpIntegral hV (a - k) M v := by
  have hk : 0 ≤ k := by rw [hcrit]; positivity
  have hka : k < a := by rw [hcrit]; linarith only [ha]
  obtain ⟨δ, L, N, hδ, hδ1, hδr, hL, hN, hsmall, hb⟩ :=
    exists_horizon_outer_radiation_kernel hc hi hrc hr0 hφ hrd hk hka hρ
      hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, L, N, hδ, hδ1, hδr, hL, hN, hsmall, ?_⟩
  intro U V hU hV hUR f hf x hx hfn hwidth
  apply hb U V hU hV hUR 4 le_rfl f hf x hx hfn _ hwidth
  norm_num
  nlinarith only [hcrit]


-- The actual supremum, including the moving edge, is bounded by its continuous envelope.
example {U V δ a k : ℝ} (hU : 0 ≤ U) (hδ : 0 ≤ δ) (x : WaveState U V)
    (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ≤ min U (δ * Real.exp (-a * v))) :
    Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ outerRadiationEnvelope hδ a k x v :=
  (outerRadiationEnvelope_le_iff hU hδ x v).1 le_rfl u (hu.trans (min_le_right _ _))

-- Clamping avoids division by the moving width and also handles a singleton row.
example {V δ a k : ℝ} (hδ : 0 ≤ δ) (x : WaveState 0 V) (v : Icc 0 V) :
    outerRadiationEnvelope hδ a k x v =
      Real.exp (k * v) * |x.1 ⟨0, le_rfl, le_rfl⟩ v 0 * x.2.1 ⟨0, le_rfl, le_rfl⟩ v 1| := by
  apply le_antisymm
  · apply (outerRadiationEnvelope_le_iff le_rfl hδ x v).2
    intro u _
    have hu : u = ⟨0, le_rfl, le_rfl⟩ := Subtype.ext (le_antisymm u.property.2 u.property.1)
    rw [hu]
  · exact (outerRadiationEnvelope_le_iff le_rfl hδ x v).1 le_rfl _
      (mul_nonneg hδ (Real.exp_pos _).le)

-- A late outer ray stays in the outer region at every earlier time.
example {U δ a s t u : ℝ} (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hst : s ≤ t)
    (hu : u ≤ min U (δ * Real.exp (-a * t))) :
    u ≤ min U (δ * Real.exp (-a * s)) := by
  apply le_min (hu.trans (min_le_left _ _))
  exact (hu.trans (min_le_right _ _)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hst (neg_nonpos.2 ha))) hδ)

-- The physical p=4 moving estimate imposes no thinness on the full rectangle.
example {m e Λ a k ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (ha : 0 < a) (hcrit : k = (3 / 4) * a) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (k * t) * |h t| ≤ H)
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass m h t) e Λ| ≤ W) :
    ∃ (δ L N : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧ 0 ≤ L ∧ 0 < N ∧
      L * N * δ / (ρ ^ 2 * (a - k)) ≤ 1 / 4 ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
        let M := outerRadiationEnvelope hδ.le a k x
        ∀ v : Icc 0 V, M v ≤ Real.exp (k * v) * |h v| +
          (L * r 0 / ρ) * Real.exp (k * v) *
            (∫ t in (0 : ℝ)..min U (δ * Real.exp (-a * v)), |f t|) +
          (L * N * δ / ρ ^ 2) * causalExpIntegral hV (a - k) M v := by
  have hk : 0 ≤ k := by rw [hcrit]; positivity
  have hka : k < a := by rw [hcrit]; linarith only [ha]
  obtain ⟨δ, L, N, hδ, hδ1, hδr, hL, hN, hsmall, hb⟩ :=
    exists_horizon_moving_outer_radiation hc hi hrc hr0 hφ hrd hk hka hρ
      hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, L, N, hδ, hδ1, hδr, hL, hN, hsmall, ?_⟩
  intro U V hU hV hUR f hf x hx hfn
  have hkp : k ≤ a * (1 - 1 / (4 : ℝ≥0∞).toReal) := by norm_num; nlinarith only [hcrit]
  exact fun v => (hb U V hU hV hUR 4 le_rfl f hf x hx hfn hkp v).1

-- The kernel estimate applies to signed input, without an absolute-value premise.
example {V : ℝ} (hV : 0 ≤ V) :
    4 * (∫ t in (0 : ℝ)..V,
      (causalExpIntegral hV 2 (ContinuousMap.const _ (-1)) (projIcc 0 V hV t)) ^ 2) ≤ V := by
  have hh := (causalExpIntegral_energy hV (by norm_num : (0 : ℝ) < 2)
    (ContinuousMap.const _ (-1))).2
  norm_num at hh
  exact hh

-- A zero time interval is included in the derivative-based energy proof.
example {d : ℝ} (hd : 0 < d) (M : C(Icc (0 : ℝ) 0, ℝ)) :
    Continuous (causalExpIntegral le_rfl d M) ∧
      d ^ 2 * (∫ t in (0 : ℝ)..0, (causalExpIntegral le_rfl d M (projIcc 0 0 le_rfl t)) ^ 2) ≤
        ∫ t in (0 : ℝ)..0, (M (projIcc 0 0 le_rfl t)) ^ 2 :=
  causalExpIntegral_energy le_rfl hd M

-- At half the kernel damping rate, zero forcing still forces zero radiation energy.
example {V d : ℝ} (hV : 0 ≤ V) (hd : 0 < d) (M : C(Icc 0 V, ℝ))
    (hM : ∀ v, 0 ≤ M v)
    (hb : ∀ v : Icc 0 V, M v ≤ (d / 2) * causalExpIntegral hV d M v) :
    (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) = 0 := by
  apply le_antisymm
  · have hh := causalExpIntegral_absorb_sq hV hd (by positivity : 0 ≤ d / 2) le_rfl M hM
      (F := fun _ => 0) (by simp) (fun v => by simpa using hb v)
    simpa using hh
  · exact intervalIntegral.integral_nonneg hV (fun t _ => sq_nonneg _)

-- Critical p=4 absorption keeps the physical profile and no terminal-time factor.
example {m e Λ a k ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (ha : 0 < a) (hcrit : k = (3 / 4) * a) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (k * t) * |h t| ≤ H)
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass m h t) e Λ| ≤ W) :
    ∃ (δ C : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧ 0 ≤ C ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
        let M := outerRadiationEnvelope hδ.le a k x
        (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
          4 * ∫ t in (0 : ℝ)..V, (Real.exp (k * t) * |h t| +
            C * Real.exp (k * t) * (∫ s in (0 : ℝ)..min U (δ * Real.exp (-a * t)), |f s|)) ^ 2 := by
  have hk : 0 ≤ k := by rw [hcrit]; positivity
  have hka : k < a := by rw [hcrit]; linarith only [ha]
  obtain ⟨δ, C, _D, hδ, hδ1, hδr, hC, _hD, hb⟩ :=
    exists_horizon_outer_radiation_energy hc hi hrc hr0 hφ hrd hk hka hρ
      hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, C, hδ, hδ1, hδr, hC, ?_⟩
  intro U V hU hV hUR f hf x hx hfn
  have hkp : k ≤ a * (1 - 1 / (4 : ℝ≥0∞).toReal) := by norm_num; nlinarith only [hcrit]
  exact (hb U V hU hV hUR 4 le_rfl f hf x hx hfn hkp).1

-- A signed constant profile checks the indispensable normalizing factor b.
example {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u) (ℓ c : ℝ) :
    (∫ x in (0 : ℝ)..u, logarithmicIncoming b ℓ (BoundedContinuousFunction.const ℝ c) x) =
      c * u ^ b := by
  rw [(logarithmicIncoming_primitive hb hu ℓ (BoundedContinuousFunction.const ℝ c)).2,
    terminalGreen_const]
  field_simp

-- The logarithmic origin agrees with the manuscript's log(u_*/u).
example {b u ustar : ℝ} (hb : 0 < b) (hu : 0 < u) (hstar : 0 < ustar)
    (B : ℝ →ᵇ ℝ) :
    (∫ x in (0 : ℝ)..u, logarithmicIncoming b (Real.log ustar) B x) =
      b * u ^ b * terminalGreen hb B (Real.log (ustar / u)) := by
  rw [Real.log_div hstar.ne' hu.ne']
  exact (logarithmicIncoming_primitive hb hu.le (Real.log ustar) B).2

-- The translated exponential kernel has the same exact normalization.
example {b : ℝ} (hb : 0 < b) (c t : ℝ) :
    b * (∫ z in Ioi (0 : ℝ), Real.exp (-b * z) * c) = c := by
  have hh := terminalGreen_eq_shifted_integral hb (BoundedContinuousFunction.const ℝ c) t
  rw [terminalGreen_const] at hh
  change c / b = ∫ z in Ioi (0 : ℝ), Real.exp (-b * z) * c at hh
  rw [← hh]
  field_simp

-- The same bound covers the initially saturated whole incoming interval.
example {U δ a b k v : ℝ} (hU : 0 ≤ U) (hδ : 0 < δ) (hb : 0 < b)
    (hcrit : k = a * b) (hsat : U ≤ δ * Real.exp (-a * v)) (ℓ : ℝ) (B : ℝ →ᵇ ℝ) :
    Real.exp (k * v) * (∫ u in (0 : ℝ)..U, |logarithmicIncoming b ℓ B u|) ≤
      δ ^ b * (b * terminalGreen hb |B| (ℓ - Real.log δ + a * v)) := by
  simpa only [min_eq_left hsat] using logarithmicIncoming_outer_source hU hδ hb hcrit ℓ B v

-- Critical p=4 has the precise delta^(3/2)/a energy prefactor.
example {U V δ a : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hδ : 0 < δ) (ha : 0 < a)
    (ℓ : ℝ) (B : ℝ →ᵇ ℝ) :
    (∫ v in (0 : ℝ)..V, (Real.exp (((3 / 4) * a) * v) *
      (∫ u in (0 : ℝ)..min U (δ * Real.exp (-a * v)), |logarithmicIncoming (3 / 4) ℓ B u|)) ^ 2) ≤
      δ ^ (3 / 2 : ℝ) / a * ∫ t in (ℓ - Real.log δ)..(ℓ - Real.log δ + a * V),
        ((3 / 4) * terminalGreen (by norm_num : (0 : ℝ) < 3 / 4) |B| t) ^ 2 := by
  have hh := logarithmicIncoming_outer_energy hU hV hδ ha (by norm_num : (0 : ℝ) < 3 / 4)
    (mul_comm (3 / 4 : ℝ) a) ℓ B
  norm_num at hh
  simpa only [neg_mul] using hh

-- The whole-line contraction retains signed, non-compactly-supported input.
example {b : ℝ} (hb : 0 < b) (B : ℝ →ᵇ ℝ) (hB : Integrable (fun t => B t ^ 2)) :
    (∫ t, (b * terminalGreen hb (-B) t) ^ 2) ≤ ∫ t, B t ^ 2 := by
  simpa using (terminalGreen_l2_contraction hb (-B) (by simpa using hB)).2

-- The critical incoming energy loses neither b nor the time Jacobian.
example {U V δ a : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hδ : 0 < δ) (ha : 0 < a)
    (ℓ : ℝ) (B : ℝ →ᵇ ℝ) (hB : Integrable (fun t => B t ^ 2)) :
    (∫ v in (0 : ℝ)..V, (Real.exp (((3 / 4) * a) * v) *
      (∫ u in (0 : ℝ)..min U (δ * Real.exp (-a * v)), |logarithmicIncoming (3 / 4) ℓ B u|)) ^ 2) ≤
      δ ^ (3 / 2 : ℝ) / a * ∫ t, B t ^ 2 := by
  have hh := logarithmicIncoming_outer_energy_bound hU hV hδ ha
    (by norm_num : (0 : ℝ) < 3 / 4) (mul_comm (3 / 4 : ℝ) a) ℓ B hB
  norm_num at hh
  simpa only [neg_mul] using hh

-- An exact exponential checks the outgoing energy's factor 2 and rate gap.
example {V k s : ℝ} (hV : 0 ≤ V) (hks : k < s) :
    (∫ t in (0 : ℝ)..V, (Real.exp (k * t) * Real.exp (-s * t)) ^ 2) ≤ 1 / (2 * (s - k)) := by
  simpa using weighted_exponential_energy hV hks (by norm_num : (0 : ℝ) ≤ 1)
    (show Continuous (fun t => Real.exp (-s * t)) by fun_prop)
    (fun t _ => by simp)

-- The actual critical p=4 energy is uniform in time and logarithmic translations.
set_option maxHeartbeats 600000 in
example {m e Λ ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (hρ : 0 < ρ) (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (4 * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ≤ NH * Real.exp (4 * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), |h t| ≤ H * Real.exp (-4 * t))
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass m h t) e Λ| ≤ W) :
    ∃ (δ C : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧ δ ≤ r 0 / 4 ∧ 0 ≤ C ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (ℓ : ℝ) (B : ℝ →ᵇ ℝ) (hB : Integrable (fun t => B t ^ 2))
        (hf : MemLp (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
        let M := outerRadiationEnvelope hδ.le 4 3 x
        (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
          4 * H ^ 2 + 2 * C ^ 2 * δ ^ (3 / 2 : ℝ) * ∫ t, B t ^ 2 := by
  obtain ⟨δ, C, _D, hδ, hδ1, hδr, hC, _hD, hb⟩ := exists_horizon_outer_energy_bound
    (b := 3 / 4) (k := 3) (s := 4) hc hi hrc hr0 hφ hrd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hρ
    hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, C, hδ, hδ1, hδr, hC, ?_⟩
  intro U V hU hV hUR ℓ B hB hf x hx hfn
  have hh := (hb U V hU hV hUR 4 le_rfl ℓ B hB hf x hx hfn (by norm_num)).1
  norm_num at hh
  exact hh.trans_eq (by ring)


-- A translated affine clock retains the exact Jacobian, also for signed input.
example {l r η : ℝ} (hlr : l ≤ r) (hη : 0 < η) (ℓ : ℝ)
    (B : ℝ →ᵇ ℝ) (hB : Integrable (fun t => B t ^ 2)) :
    (∫ t in l..r, B (ℓ + η * t) ^ 2) ≤ (∫ t, B t ^ 2) / η := by
  apply timeChange_l2_bound hlr hη (by fun_prop)
    (fun t _ => by simpa using ((hasDerivAt_id t).const_mul η).const_add ℓ)
    (fun _ _ => le_rfl) B.continuous hB

-- The direct critical trace includes the initial radius factor and b^2 = 9/16.
example {V : ℝ} (hV : 0 ≤ V) (ℓ : ℝ) (B : ℝ →ᵇ ℝ)
    (hB : Integrable (fun t => B t ^ 2)) :
    (∫ t in (0 : ℝ)..V, (Real.exp (-t) * Real.exp ((3 / 4) * t) *
      (1 - Real.exp (-t)) * logarithmicIncoming (3 / 4) ℓ B (Real.exp (-t))) ^ 2) ≤
        (9 / 16 : ℝ) * ∫ t, B t ^ 2 := by
  have hd (t : ℝ) : HasDerivAt (fun w => Real.exp (-w)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := logarithmicIncoming_trace_energy (r₀ := 1) (a := 1) (b := 3 / 4) (k := 3 / 4)
    (D := 1) (η := 1) (ℓ := ℓ) hV (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (show ContinuousOn (fun t => Real.exp (-t)) (Icc 0 V) by fun_prop)
    (fun t _ => (hd t).differentiableAt) (fun t _ => Real.exp_pos _)
    (fun t ht => Real.exp_le_one_iff.2 (neg_nonpos.2 ht.1))
    (fun t _ => by simp [← Real.exp_add])
    (fun t _ => by rw [(hd t).deriv]; simp) B hB
  norm_num at hh
  exact hh

-- One physical p=4 construction works for every translated signed profile.
set_option maxHeartbeats 600000 in
example (G : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event)
    (hA : 0 ≤ A) (hks : (3 / 4) * G.outerRate ≤ s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) :
    ∃ δ T C : ℝ, 0 < δ ∧ 0 ≤ T ∧ 0 ≤ C ∧
      ∀ (ℓ : ℝ) (B : ℝ →ᵇ ℝ), Integrable (fun t => B t ^ 2) →
        MemLp (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ g : ℝ → ℝ, ContinuousOn g (Ioi T) ∧
          ∀ l w : ℝ, T < l → l ≤ w →
            (∫ t in l..w, (g t * Real.exp (((3 / 4) * G.outerRate) * t) * (r 0 - g t) *
              logarithmicIncoming (3 / 4) ℓ B (g t)) ^ 2) ≤ C * ∫ t, B t ^ 2 := by
  obtain ⟨δ, Y, T, J, η, C, hδ, _hδr, _hY, hT, _hJ, _hJδ, _hη, hC, hb⟩ :=
    G.exists_outer_profile_trace_energy (b := 3 / 4) (k := (3 / 4) * G.outerRate)
      hs hH hdH hdHR hA (by norm_num) (by norm_num) (by ring) hks
      hc hout hrc hrb hrd hrdec hOut
  refine ⟨δ, T, C, hδ, hT, hC, ?_⟩
  intro ℓ B hB hf hfn
  obtain ⟨g, hgc, _hga, _hgl, he, _hp⟩ := hb 4 le_rfl ℓ B hB hf hfn (by norm_num; linarith)
  exact ⟨g, hgc, he⟩


-- A terminal width bound controls an entire earlier vertical history.
example {U V δ a k l w u : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (hl : 0 ≤ l) (hlw : l ≤ w) (hw : w ≤ V) (hu : u ∈ Icc 0 U)
    (huw : u ≤ δ * Real.exp (-a * w)) (x : WaveState U V) :
    (∫ t in l..w, (Real.exp (k * t) *
      (intervalExtension hV (intervalExtension hU x.1 u) t 0 *
        intervalExtension hV (intervalExtension hU x.2.1 u) t 1)) ^ 2) ≤
      ∫ t in (0 : ℝ)..V, (outerRadiationEnvelope hδ a k x (projIcc 0 V hV t)) ^ 2 := by
  apply outerRadiationEnvelope_curve_energy hU hV hδ hl hlw hw x
    continuous_const.continuousOn (fun _ _ => hu)
  intro t ht
  exact huw.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left ht.2 (neg_nonpos.2 ha))) hδ)

-- Both actual p=4 scalar derivatives have trace energy on one radius and width.
set_option maxHeartbeats 1000000 in
example (G : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event)
    (hA : 0 ≤ A) (hks : (3 / 4) * G.outerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) (cap : ℝ) (hcap : 0 < cap) :
    let hi := horizon_mass_integrable hs hH hc hout
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ Y T E₀ E₁ E₂ E₃ : ℝ, 0 < δ ∧ δ ≤ cap ∧ Y ∈ Ioo G.inner G.event ∧
      0 ≤ T ∧ 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ 0 ≤ E₂ ∧ 0 ≤ E₃ ∧
      ∀ (ℓ : ℝ) (B : ℝ →ᵇ ℝ), Integrable (fun t => B t ^ 2) →
        MemLp (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        ∃ g : ℝ → ℝ, ContinuousOn g (Ioi T) ∧
          ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0) (_hUδ : U ≤ δ)
            (hfU : MemLp (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 U)))
            (x : WaveState U V)
            (hx : IsWaveIntegral hU hV G.charge G.cosmological
              (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
              (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR le_rfl hfU) x)
            (l w : ℝ), T < l → l ≤ w → w ≤ V → g l ≤ U →
            let C := scalarTransportCorrection hV (radialNuField hV G.charge G.cosmological
              (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose) x.2.1
            (∀ t ∈ Icc l w, intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 = Y) ∧
              ((∫ t in l..w, (Real.exp (((3 / 4) * G.outerRate) * t) *
                (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                  intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1)) ^ 2) ≤
                    E₀ + E₁ * ∫ t, B t ^ 2) ∧
              ((∫ t in l..w, (g t * Real.exp (((3 / 4) * G.outerRate) * t) *
                intervalExtension hV (intervalExtension hU C (g t)) t) ^ 2) ≤
                  E₃ * (E₀ + E₁ * ∫ t, B t ^ 2)) ∧
              (∫ t in l..w, (g t * Real.exp (((3 / 4) * G.outerRate) * t) *
                (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                  derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                    (Icc 0 U) (g t))) ^ 2) ≤
                      2 * E₃ * E₀ + 2 * (E₂ + E₃ * E₁) * ∫ t, B t ^ 2 := by
  dsimp only
  obtain ⟨δ, Y, T, η, E₀, E₁, E₂, E₃, hδ, hδcap, _hδr, hY, hT, _hη, hE₀, hE₁, hE₂, hE₃, hb⟩ :=
    G.exists_outer_trace_energy (b := 3 / 4) (k := (3 / 4) * G.outerRate)
      hs hH hdH hdHR hA (by norm_num) (by norm_num) (by ring) hks
      hc hout hrc hrb hrd hrdec hOut cap hcap
  refine ⟨δ, Y, T, E₀, E₁, E₂, E₃, hδ, hδcap, hY, hT, hE₀, hE₁, hE₂, hE₃, ?_⟩
  intro ℓ B hB hf hfn
  obtain ⟨g, hgc, _hga, _hgl, _hp, _hdirect, htrace⟩ := hb 4 le_rfl ℓ B hB hf hfn
    (by norm_num; linarith)
  exact ⟨g, hgc, htrace⟩

-- The squared damping denominator is retained on an arbitrary subinterval.
example {V l w : ℝ} (hV : 0 ≤ V) (hl : 0 ≤ l) (hlw : l ≤ w) (hw : w ≤ V)
    (M : C(Icc 0 V, ℝ)) {F : ℝ → ℝ} (hc : ContinuousOn F (Icc l w))
    (hb : ∀ t ∈ Icc l w, |F t| ≤ 3 * causalExpIntegral hV 2 M (projIcc 0 V hV t)) :
    (∫ t in l..w, F t ^ 2) ≤ (9 / 4 : ℝ) * ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  have hh := causalExpIntegral_dominated_energy hV (by norm_num : (0 : ℝ) < 2) hl hlw hw M hc hb
  norm_num at hh
  exact hh

-- Domination also works with a negative source and coefficient; no hidden positivity is used.
example {V l w : ℝ} (hV : 0 ≤ V) (hl : 0 ≤ l) (hlw : l ≤ w) (hw : w ≤ V)
    {F : ℝ → ℝ} (hc : ContinuousOn F (Icc l w))
    (hb : ∀ t ∈ Icc l w, |F t| ≤ (-3) *
      causalExpIntegral hV 2 (ContinuousMap.const _ (-1)) (projIcc 0 V hV t)) :
    (∫ t in l..w, F t ^ 2) ≤ (9 / 4 : ℝ) * V := by
  have hh := causalExpIntegral_dominated_energy hV (by norm_num : (0 : ℝ) < 2) hl hlw hw
    (ContinuousMap.const _ (-1)) hc hb
  norm_num at hh
  exact hh

-- At the incoming right endpoint the actual derivative is one-sided, not the derivative of a clamp.
example {U V e Λ : ℝ} (hU : 0 < U) (hV : 0 ≤ V)
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU.le hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU.le uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t) (v : Icc 0 V) :
    derivWithin (fun t => intervalExtension hU.le x.1 t v 1) (Icc 0 U) U =
      (zIn ⟨U, hU.le, le_rfl⟩ 0 * f U +
        scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hx.choose)
          x.2.1 ⟨U, hU.le, le_rfl⟩ v) / x.1 ⟨U, hU.le, le_rfl⟩ v 0 := by
  exact (hx.scalar_hasDerivWithinAt_of_continuous hzin hinu hc hif ⟨hU, le_rfl⟩ v).derivWithin
    (uniqueDiffOn_Icc hU U ⟨hU.le, le_rfl⟩)

-- Inside the rectangle the same reconstruction is the ordinary partial derivative.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
    {u : ℝ} (hu : u ∈ Ioo 0 U) (v : Icc 0 V) :
    deriv (fun t => intervalExtension hU x.1 t v 1) u =
      (zIn ⟨u, hu.1.le, hu.2.le⟩ 0 * f u +
        scalarTransportCorrection hV (radialNuField hV e Λ zIn x.1 hx.choose)
          x.2.1 ⟨u, hu.1.le, hu.2.le⟩ v) / x.1 ⟨u, hu.1.le, hu.2.le⟩ v 0 := by
  exact ((hx.scalar_hasDerivWithinAt_of_continuous hzin hinu hc hif ⟨hu.1, hu.2.le⟩ v).hasDerivAt
    (Icc_mem_nhds hu.1 hu.2)).deriv

-- Spatial weighting makes the feedback small for arbitrary nonnegative band constants.
example {L N ρ d : ℝ} (hL : 0 ≤ L) (hN : 0 ≤ N) (hρ : 0 < ρ) (hd : 0 < d) :
    let σ := 1 + 4 * L * N / (ρ ^ 2 * d)
    0 < σ ∧ L * N / (σ * ρ ^ 2) ≤ d / 4 := by
  dsimp only
  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hσ : 0 < 1 + 4 * L * N / (ρ ^ 2 * d) := by positivity
  refine ⟨hσ, (div_le_iff₀ (mul_pos hσ hρ2)).2 ?_⟩
  have he : d / 4 * ((1 + 4 * L * N / (ρ ^ 2 * d)) * ρ ^ 2) =
      d * ρ ^ 2 / 4 + L * N := by
    field_simp
  rw [he]
  linarith [show 0 ≤ d * ρ ^ 2 / 4 by positivity]

-- The weight and its inverse have time-independent bounds on a bounded exponential width.
example {σ u v a D : ℝ} (hσ : 0 ≤ σ) (hu : 0 ≤ u)
    (hwidth : u * Real.exp (a * v) ≤ D) :
    Real.exp (-(σ * D)) ≤ Real.exp (-(σ * u * Real.exp (a * v))) ∧
      Real.exp (-(σ * u * Real.exp (a * v))) ≤ 1 ∧
      Real.exp (σ * u * Real.exp (a * v)) ≤ Real.exp (σ * D) := by
  have hh := mul_le_mul_of_nonneg_left hwidth hσ
  have h0 : 0 ≤ σ * u * Real.exp (a * v) := by positivity
  constructor
  · apply Real.exp_le_exp.2
    nlinarith only [hh]
  constructor
  · exact Real.exp_le_one_iff.2 (neg_nonpos.2 h0)
  · apply Real.exp_le_exp.2
    nlinarith only [hh]

-- An actual critical p=4 rectangle needs no small-width premise for weighted energy.
example {U V e Λ R : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hlo : ∀ u v, 1 ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hx.choose u v| ≤ Real.exp (4 * v))
    (hlam : ∀ u v, |x.2.1 u v 0| ≤ 1) :
    (∫ t in (0 : ℝ)..V, (spatialRadiationEnvelope 4 3 4 x (projIcc 0 V hV t)) ^ 2) ≤
      4 * ∫ t in (0 : ℝ)..V,
        (Real.exp (3 * t) * |x.1 ⟨0, le_rfl, hU⟩ (projIcc 0 V hV t) 0 *
          vOut (projIcc 0 V hV t) 1| +
          R * Real.exp (3 * t) * (∫ s in (0 : ℝ)..U, |uIn s 1|)) ^ 2 := by
  have hh := hx.spatial_radiation_energy (a := 4) (k := 3) (ρ := 1) (N := 1) (L := 1)
    (σ := 4) hx.choose hzin hinu (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlo hin
    (fun u v => by simpa using hν u v) hlam
  simpa only [one_mul, div_one] using hh

-- Capping the actual inverse arrival at a common late time preserves the needed domain properties.
example {a D t₀ T : ℝ} (ha : 0 ≤ a) (hT : t₀ < T) {g : ℝ → ℝ}
    (hc : ContinuousOn g (Ioi t₀)) (hanti : AntitoneOn g (Ioi t₀))
    (hg : ∀ t ∈ Ioi t₀, 0 ≤ g t)
    (hscale : ∀ t ∈ Ioi t₀, g t * Real.exp (a * t) ≤ D) :
    Continuous (fun t => g (max T t)) ∧ Antitone (fun t => g (max T t)) ∧
      ∀ t, 0 ≤ g (max T t) ∧ g (max T t) * Real.exp (a * t) ≤ D := by
  have hmem (t : ℝ) : max T t ∈ Ioi t₀ := hT.trans_le (le_max_left _ _)
  refine ⟨hc.comp_continuous (by fun_prop) hmem, ?_, ?_⟩
  · intro t s hts
    exact hanti (hmem t) (hmem s) (max_le_max_left T hts)
  · intro t
    refine ⟨hg _ (hmem t), ?_⟩
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_max_right T t) ha))
      (hg _ (hmem t))).trans (hscale _ (hmem t))

-- A zero moving width evaluates only the physical axis, including a degenerate rectangle.
example {U V a k σ : ℝ} (hU : 0 ≤ U) (x : WaveState U V) (v : Icc 0 V) :
    movingSpatialRadiationEnvelope (ContinuousMap.const _ 0) (fun _ => le_rfl) a k σ x v =
      Real.exp (k * v) * |x.1 ⟨0, le_rfl, hU⟩ v 0 * x.2.1 ⟨0, le_rfl, hU⟩ v 1| := by
  apply le_antisymm
  · apply (movingSpatialRadiationEnvelope_le_iff hU (ContinuousMap.const _ 0) _ x v).2
    intro u hu
    have he : u = (⟨0, le_rfl, hU⟩ : Icc 0 U) := Subtype.ext (le_antisymm hu u.property.1)
    subst u
    simp
  · have hh := (movingSpatialRadiationEnvelope_le_iff (a := a) (k := k) (σ := σ)
      hU (ContinuousMap.const _ 0) (fun _ => le_rfl) x v).1 le_rfl ⟨0, le_rfl, hU⟩ le_rfl
    simpa using hh

-- At p=4, width scale one has unsmall unweighted feedback, but sigma=4 closes the moving energy.
set_option maxHeartbeats 600000 in
example {U V m e Λ H : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun t => h t ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun t => h t / r t) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (hH : 0 ≤ H) (hout : ∀ t ∈ Ici (0 : ℝ), |h t| ≤ H * Real.exp (-4 * t))
    (w : C(Icc 0 V, ℝ)) (hw0 : ∀ v, 0 ≤ w v) (hw : Antitone w)
    (hwidth : ∀ v, w v ≤ Real.exp (-4 * v))
    (ℓ : ℝ) (B : ℝ →ᵇ ℝ) (hB : Integrable (fun t => B t ^ 2))
    (hf : MemLp (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 U)))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (hlo : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ w v → 1 ≤ x.1 u v 0)
    (hν : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ w v →
      |radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
        x.1 hx.choose u v| ≤ Real.exp (4 * v))
    (hlam : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ w v → |x.2.1 u v 0| ≤ 1) :
    let M := movingSpatialRadiationEnvelope w hw0 4 3 4 x
    let E := 4 * H ^ 2 + 2 * r 0 ^ 2 * ∫ t, B t ^ 2
    ((∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤ E) ∧
      ((∫ t in (0 : ℝ)..V,
        (movingSpatialRadiationEnvelope w hw0 4 3 0 x (projIcc 0 V hV t)) ^ 2) ≤
          Real.exp 4 ^ 2 * E) ∧
      ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) ≤ w v →
        (u : ℝ) * Real.exp (3 * v) * |scalarTransportCorrection hV
          (radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
            x.1 hx.choose) x.2.1 u v| ≤ Real.exp 4 * causalExpIntegral hV 1 M v := by
  have hh := hx.horizon_moving_spatial_energy (a := 4) (b := 3 / 4) (k := 3) (s := 4)
    (ρ := 1) (N := 1) (L := 1) (σ := 4) (D := 1)
    hU hV hUR hc hi hrc hr0 hφ hrd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hH
    (by norm_num) hout w hw0 hw (fun v => by simpa using hwidth v) le_rfl ℓ B hB hf hlo
    (fun u v hu => by simpa using hν u v hu) hlam
  norm_num at hh ⊢
  rw [show 8 * r 0 ^ 2 / 4 = 2 * r 0 ^ 2 by ring] at hh
  exact hh

-- The same critical p=4 profile family has both actual traces at every eligible inner radius.
set_option maxHeartbeats 1200000 in
example (G : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event)
    (hA : 0 ≤ A) (hks : (3 / 4) * G.outerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t) (hrinit : G.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hout
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo G.inner G.event ∧
      ∀ Y : ℝ, G.inner < Y → Y ≤ R → ∃ U₀ T E₀ E₁ E₂ E₃ : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧
        ∀ (ℓ : ℝ) (B : ℝ →ᵇ ℝ), Integrable (fun t => B t ^ 2) →
          MemLp (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 δ)) →
          (eLpNorm (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 U)))
                (x : WaveState U V)
                (hx : IsWaveIntegral hU hV G.charge G.cosmological
                  (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
                  (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_rfl hfU) x)
                (l q : ℝ), T ≤ l → l ≤ q → q ≤ V → g l ≤ U →
                  (∀ t ∈ Icc l q, intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 = Y) ∧
                    ((∫ t in l..q, (Real.exp (((3 / 4) * G.outerRate) * t) *
                      (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                        intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1)) ^ 2) ≤
                          E₀ + E₁ * ∫ t, B t ^ 2) ∧
                    (∫ t in l..q, (g t * Real.exp (((3 / 4) * G.outerRate) * t) *
                      (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
                        derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                          (Icc 0 U) (g t))) ^ 2) ≤
                            2 * E₃ * E₀ + 2 * (E₂ + E₃ * E₁) * ∫ t, B t ^ 2 := by
  dsimp only
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hsolve⟩ := G.exists_band_trace_energy
    (b := 3 / 4) (k := (3 / 4) * G.outerRate) hs hH hdH hdHR hA
    (by norm_num) (by norm_num) (by ring) hks hc hout hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨U₀, T, _j, _D, _η, _C, E₀, E₁, E₂, E₃, hU₀, hU₀δ, hT,
    _hj, _hD, _hη, _hC, _hE₀, _hE₁, _hE₂, _hE₃, hb⟩ := hsolve Y hY hYR
  refine ⟨U₀, T, E₀, E₁, E₂, E₃, hU₀, hU₀δ, hT, ?_⟩
  intro ℓ B hB hf hfn
  obtain ⟨g, hgc, _hga, _hgl, _hdc, _hstart, _hpoint, he⟩ := hb 4 le_rfl ℓ B hB hf hfn (by norm_num; linarith)
  refine ⟨g, hgc, ?_⟩
  intro U V hU hV hUR hUU hfU x hx l q hl hlq hqV hglU
  obtain ⟨_w, _hw0, _hw, _henergy, _hidentify, _hnuY, htraces⟩ := he U V hU hV hUR hUU hfU x hx
  have ht := htraces l q hl hlq hqV hglU
  exact ⟨ht.1, ht.2.1, ht.2.2.2⟩

-- The matching radius remains selectable within every positive gap above the inner horizon.
example (G : Background) {R ε : ℝ} (hR : G.inner < R) (hε : 0 < ε) :
    ∃ Y : ℝ, G.inner < Y ∧ Y ≤ R ∧ Y - G.inner < ε := by
  refine ⟨G.inner + min (R - G.inner) ε / 2, ?_, ?_, ?_⟩
  · have hp : 0 < min (R - G.inner) ε := lt_min (sub_pos.2 hR) hε
    linarith only [hp]
  · have hh := min_le_left (R - G.inner) ε
    linarith only [hh, hR]
  · have hh := min_le_right (R - G.inner) ε
    linarith only [hh, hε]

-- The two actual transports retain the signed increment and critical k and 3*k kernels at p=4.
example {U V R e Λ φ₀ k Lᵧ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R) (hLᵧ : 0 ≤ Lᵧ)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x)
    (A M : C(Icc 0 V, ℝ)) (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (T : C(Icc (z : ℝ) u, Icc 0 V)) :
    let τ := fun t => T (projIcc (z : ℝ) u hzu t)
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) x.1 hx.choose
    τ z = b → (∀ t ∈ Icc (z : ℝ) u, τ t ≤ b) →
    (∀ t ∈ Icc (z : ℝ) u, ν (projIcc 0 U hU t) (τ t) < 0) →
    (∀ t ∈ Icc (z : ℝ) u, -Lᵧ ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧
      x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0) →
    (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
      (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b, 1 ≤ x.1 (projIcc 0 U hU t) v 0) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b,
      |ν (projIcc 0 U hU t) v| ≤ 2 * (-ν (projIcc 0 U hU t) (τ t)) *
        Real.exp (-(2 * k) * ((v : ℝ) - τ t))) →
    (∀ t ∈ Icc (z : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
      2 * Lᵧ * Real.exp (-(2 * k) * ((b : ℝ) - τ t))) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b,
      Real.exp (k * v) * |x.1 (projIcc 0 U hU t) v 0 * x.2.1 (projIcc 0 U hU t) v 1| ≤ M v) →
    (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      Real.exp (k * τ t) * |x.1 (projIcc 0 U hU t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
        (-ν (projIcc 0 U hU t) (τ t)) * A (τ t)) →
      Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1 - x.1 z b 0 * x.2.1 z b 1| ≤
          2 * Lᵧ ^ 2 * ∫ t in (τ u : ℝ)..b, Real.exp (-k * ((b : ℝ) - t)) *
            (A (projIcc 0 V hV t) + 2 * ∫ w in t..b,
              Real.exp (-(3 * k) * (w - t)) * M (projIcc 0 V hV w)) := by
  dsimp only
  intro hτz hτb hn hentry hder hr hν hlam hM hA
  have hh := hx.early_radiation_feedback hU hV hUR le_rfl hf
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 2)
    (mul_nonneg (by norm_num) hLᵧ) A M z u hzu b T
    hτz hτb hn hentry hder hr hν hlam hM hA
  simpa only [div_one, pow_two, mul_assoc] using hh

-- Matching-speed smallness does not involve the size of the finite-band forcing.
example (k ρ κ Lᵧ : ℝ) :
    ((Real.exp 2 * Lᵧ) * Lᵧ / ρ) * ((Real.exp 2 / κ) / ρ) / (4 * k ^ 2) =
      Real.exp 4 / (4 * κ * ρ ^ 2 * k ^ 2) * Lᵧ ^ 2 := by
  have he : Real.exp 2 * Real.exp 2 = Real.exp 4 := by
    rw [← Real.exp_add]
    norm_num
  calc
    _ = (Real.exp 2 * Real.exp 2) / (4 * κ * ρ ^ 2 * k ^ 2) * Lᵧ ^ 2 := by ring
    _ = _ := by rw [he]

-- The finite lower endpoint survives the double-kernel calculation.
example {k l v : ℝ} (hk : 0 < k) (hlv : l ≤ v) :
    (4 * k) * (∫ t in l..v, Real.exp (-k * (v - t)) *
      ∫ w in t..v, Real.exp (-(3 * k) * (w - t))) =
        (∫ t in l..v, Real.exp (-k * (v - t))) -
          Real.exp (-k * (v - l)) * ∫ w in l..v, Real.exp (-(3 * k) * (w - l)) := by
  simpa only [mul_one] using
    (early_double_kernel_bound hk hlv (M := fun _ => 1) continuous_const (by intros; norm_num)).2.1

-- The closed, zero-length entry interval is included.
example {k v : ℝ} (hk : 0 < k) {M : ℝ → ℝ} (hc : Continuous M) (hM : 0 ≤ M v) :
    (∫ t in v..v, Real.exp (-k * (v - t)) *
      ∫ w in t..v, Real.exp (-(3 * k) * (w - t)) * M w) ≤ 0 := by
  have hh := (early_double_kernel_bound hk le_rfl hc (fun t ht => by
    have he : t = v := le_antisymm ht.2 ht.1
    simpa only [he] using hM)).2.2
  simpa only [intervalIntegral.integral_same, mul_zero] using hh

-- The actual p=4 estimate has the quadratic matching-speed coefficient.
example {U V R e Λ φ₀ k Lᵧ : ℝ}
    (hk : 0 < k) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R) (hLᵧ : 0 ≤ Lᵧ)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x)
    (A M : C(Icc 0 V, ℝ)) (hA0 : ∀ v, 0 ≤ A v) (hM0 : ∀ v, 0 ≤ M v) (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (T : C(Icc (z : ℝ) u, Icc 0 V)) :
    let τ := fun t => T (projIcc (z : ℝ) u hzu t)
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) x.1 hx.choose
    τ z = b → (∀ t ∈ Icc (z : ℝ) u, τ t ≤ b) →
    (∀ t ∈ Icc (z : ℝ) u, ν (projIcc 0 U hU t) (τ t) < 0) →
    (∀ t ∈ Icc (z : ℝ) u, -Lᵧ ≤ x.2.1 (projIcc 0 U hU t) (τ t) 0 ∧
      x.2.1 (projIcc 0 U hU t) (τ t) 0 < 0) →
    (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ))
      (-ν (projIcc 0 U hU t) (τ t) / x.2.1 (projIcc 0 U hU t) (τ t) 0) t) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b, 1 ≤ x.1 (projIcc 0 U hU t) v 0) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b,
      |ν (projIcc 0 U hU t) v| ≤ 2 * (-ν (projIcc 0 U hU t) (τ t)) *
        Real.exp (-(2 * k) * ((v : ℝ) - τ t))) →
    (∀ t ∈ Icc (z : ℝ) u, |x.2.1 (projIcc 0 U hU t) b 0| ≤
      2 * Lᵧ * Real.exp (-(2 * k) * ((b : ℝ) - τ t))) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b,
      Real.exp (k * v) * |x.1 (projIcc 0 U hU t) v 0 * x.2.1 (projIcc 0 U hU t) v 1| ≤ M v) →
    (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      Real.exp (k * τ t) * |x.1 (projIcc 0 U hU t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
        (-ν (projIcc 0 U hU t) (τ t)) * A (τ t)) →
      Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1 - x.1 z b 0 * x.2.1 z b 1| ≤
          2 * Lᵧ ^ 2 * causalExpIntegral hV k A b +
          Lᵧ ^ 2 / k * causalExpIntegral hV k M b := by
  dsimp only
  intro hτz hτb hn hentry hder hr hν hlam hM hA
  have hh := hx.early_radiation_causal hU hV hUR le_rfl hf hk
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 2)
    (mul_nonneg (by norm_num) hLᵧ) A M hA0 hM0 ⟨0, le_rfl, hV⟩ z u hzu b T
    (T _).property.1 hτz hτb hn hentry hder hr hν hlam hM hA
  convert hh using 1
  simp only [causalExpIntegral, causalExpIntegralFrom]
  ring

-- Absorption controls both independent forcing energies without a terminal-time factor.
example {V : ℝ} (hV : 0 ≤ V) (H A M : C(Icc 0 V, ℝ)) (hM : ∀ v, 0 ≤ M v)
    (hb : ∀ v, M v ≤ H v + causalExpIntegral hV 1 A v + (1 / 4) * causalExpIntegral hV 1 M v) :
    (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
      8 * (∫ t in (0 : ℝ)..V, (H (projIcc 0 V hV t)) ^ 2) +
        8 * ∫ t in (0 : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2 := by
  have hh := early_radiation_energy (k := 1) (ρ := 1) (N := 1) (L := 1) (Lᵧ := 1)
    hV (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ⟨0, le_rfl, hV⟩ H A M hM (fun v _ => by
      simpa only [one_mul, one_pow, mul_one, div_one, causalExpIntegral, causalExpIntegralFrom] using hb v)
  simpa only [one_mul, one_pow, div_one, mul_one] using hh

-- Matching, exact decay, and small optical flux hold on the same closed segment.
example (B : Background) {s l H dH A Apt Ycap : ℝ} {h r : ℝ → ℝ}
    (hcrit : B.innerRate = (3 / 4) * B.outerRate) (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hApt : 0 ≤ Apt)
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (hcap : B.inner < Ycap) :
    let hi := horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ β δ Y U₀ Ly : ℝ, 0 < β ∧ 0 < δ ∧ B.inner < Y ∧ Y ≤ Ycap ∧
      0 < U₀ ∧ U₀ ≤ δ ∧ 0 < Ly ∧
      ((Real.exp 2 * Ly) * Ly * (2 * Real.exp 1)) / (4 * B.innerRate ^ 2 * (B.inner / 2) ^ 2) < 1 / 4 ∧
      ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        (∀ᵐ t ∂volume.restrict (Icc 0 δ), |f t| ≤ Apt * t ^ (-1 / 4 : ℝ)) →
        ∃ arrival : ℝ → ℝ, ContinuousOn arrival (Ioc 0 U₀) ∧
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V},
            IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR le_rfl hfU) x → U ≤ U₀ →
              ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ a : Icc 0 V, (a : ℝ) = arrival u →
                x.1 u a 0 = Y ∧ ∀ v : Icc 0 V, a ≤ v → (v : ℝ) ≤ (1 + β) * arrival u →
                  |x.2.1 u v 0| ≤ (Real.exp 2 * Ly) * Real.exp (-2 * B.innerRate * ((v : ℝ) - a)) ∧
                  (∫ t in (a : ℝ)..(v : ℝ), intervalExtension hV (x.1 u) t 0 *
                    (intervalExtension hV (x.2.1 u) t 1) ^ 2 /
                      (-intervalExtension hV (x.2.1 u) t 0)) ≤ 1 / 16 ∧
                  ∀ a' : Icc 0 V, a ≤ a' → a' ≤ v →
                    |x.2.1 u v 0| ≤ (Real.exp (2 + 1 / 16) * (-x.2.1 u a' 0)) *
                      Real.exp (-2 * B.innerRate * ((v : ℝ) - a')) := by
  dsimp only
  obtain ⟨_hc, c, β, ε, _hhc, _hhck, _htail, _heq, hc0, hck, hcs, hβ, _hβ8, _hlink,
    hε, hε8, _hεβ, _hnu, hℓ, hJ, hQ⟩ := exists_linked_inner_parameters B.innerRate_pos hks hl
  have hεk : ε < B.innerRate := by linarith only [hε8, B.innerRate_pos]
  have hca : c < B.outerRate := by linarith only [hck, hcrit, B.outerRate_pos]
  have hcb : c ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    simp only [ENNReal.toReal_ofNat]
    linarith only [hck, hcrit]
  obtain ⟨δ, Y, U₀, Ly, _j, _D, _Olo, _Ohi, hδ, _hδr, hY, hYcap, hU₀, hUδ,
    hLy, _hj, _hD, _hOlo, _hOhi, hfeedback, hsolve⟩ :=
    B.exists_early_exact_geometry (B.innerRate_pos.trans hks) hH hdH hdHR hA hApt hc0 hca hcs.le
      hε hεk hε hβ.le hℓ hJ hQ le_rfl hcb hc hb hrc hrb hrinit hrd hrdec hOut Ycap hcap
  refine ⟨β, δ, Y, U₀, Ly, hβ, hδ, hY, hYcap, hU₀, hUδ, hLy, ?_, ?_⟩
  · apply (div_lt_iff₀ (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4)
      (sq_pos_of_pos B.innerRate_pos)) (sq_pos_of_pos (half_pos B.inner_pos)))).2
    exact hfeedback.trans_eq (by ring)
  · intro f hf hfn hpoint
    obtain ⟨arrival, hac, _haa, _hal, _hpos, _hscale, hmatch, _hpre, _hchart, hgeom⟩ :=
      hsolve f hf hfn (by simpa only [ENNReal.toReal_ofNat] using hpoint)
    refine ⟨arrival, hac, ?_⟩
    intro U V hU hV hUR hfU x hx hUU u hu a ha
    refine ⟨(hmatch U V hU hV hUR hfU hx hUU u hu a ha).2.2.2.2.1, ?_⟩
    intro v hav hv
    have hh := ((hgeom U V hU hV hUR hfU hx hUU u hu v hv).2 (ha.ge.trans hav)).2
    refine ⟨by simpa only [← ha] using hh.1, by simpa only [← ha] using hh.2.1, ?_⟩
    intro a' haa' ha'v
    exact (hh.2.2 a' (ha.ge.trans haa') ha'v).2

-- Exact transport includes the matching endpoint, without a positive-length assumption.
example {M e Λ U V k : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (u : Icc 0 U) (a : Icc 0 V) (ha : x.2.1 u a 0 < 0) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    3 / 4 ≤ -Real.exp (x.1 u a 2) / (4 * ν u a) →
      |ν u a| ≤ (2 * Real.exp 1) * (-ν u a) ∧ |x.2.1 u a 0| ≤ Real.exp 2 * (-x.2.1 u a 0) := by
  dsimp only
  intro hκ
  simpa only [sub_self, mul_zero, Real.exp_zero, mul_one] using
    hx.inner_exact_transport (k := k) hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u a a le_rfl ha hκ
      (by simp) (by simp)

-- With alpha=1 the mixed region is the finite band, at any chosen entry time.
example {U V R e Λ φ₀ k : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x) (hk : 0 < k)
    (w : C(Icc 0 V, ℝ)) (hw0 : ∀ v, 0 ≤ w v) (hw : Antitone w) (l : Icc 0 V) :
    let M := movingSpatialRadiationEnvelope w hw0 0 k 0 x
    (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
      8 * ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  let A : C(Icc 0 V, ℝ) := 0
  have hh := hx.early_moving_radiation_energy (ρ := 1) (N := 0) (L := 0) (Lᵧ := 0) (α := 1)
    hU hV hUR le_rfl hf hk (by norm_num) le_rfl le_rfl le_rfl (by nlinarith only [sq_nonneg k])
    le_rfl l w hw0 hw A (by intro v; exact le_rfl) (by
      intro u b hu hb
      simp only [div_one, projIcc_of_mem hV b.property, ContinuousMap.coe_mk] at hb
      exact (not_lt_of_ge hb hu).elim)
  have he : (⟨fun v : Icc 0 V => w (projIcc 0 V hV ((v : ℝ) / 1)), by fun_prop⟩ : C(Icc 0 V, ℝ)) = w := by
    ext v
    simp only [ContinuousMap.coe_mk, div_one, projIcc_of_mem hV v.property]
  simpa only [he, zero_mul, mul_zero, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using hh.2.2.2

-- The physical matching normalization supplies the source bound with one common null set.
example {M e Λ U V k Olo : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (hfc : ContinuousOn f (Ioi 0))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (hOlo : 0 < Olo) (g : C(Icc 0 V, Icc 0 U)) (hg : ∀ v, 0 < (g v : ℝ)) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let Z := fun v : Icc 0 V => (g v : ℝ) * Real.exp (k * v) *
      (x.1 (g v) v 0 * derivWithin (fun u => intervalExtension hU x.1 u v 1) (Icc 0 U) (g v))
    ∃ A : C(Icc 0 V, ℝ), (∀ v, 0 ≤ A v) ∧
      (∀ l w : ℝ, (∫ t in l..w, (A (projIcc 0 V hV t)) ^ 2) =
        (4 / Olo) ^ 2 * ∫ t in l..w, (Z (projIcc 0 V hV t)) ^ 2) ∧
      ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, (g v : ℝ) = t →
        Olo ≤ t * Real.exp (x.1 (projIcc 0 U hU t) v 2) →
        Real.exp (k * v) * |x.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1| ≤
          (-ν (projIcc 0 U hU t) v) * A v := by
  have hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR le_rfl hf t 1 = f t := by
    filter_upwards [incomingWaveVelocity_ae hUR le_rfl hf] with t ht
    rw [ht]
    rfl
  obtain ⟨A, hA0, _hAz, hAE, hsource⟩ := hx.exists_matching_radiation_source (k := k) rfl
    (incomingWave_constraint_data hU hUR le_rfl hf (horizonPhi h r 0)).1 hfc hif
    (show 0 < Olo / 4 by positivity) g hg
  refine ⟨A, hA0, ?_, ?_⟩
  · intro l w
    convert hAE l w using 1
    congr 1
    ring
  · filter_upwards [hsource, ae_restrict_mem measurableSet_Icc] with t ht htu
    intro v hgt hnorm
    apply ht v hgt
    have hgauge := hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf (projIcc 0 U hU t) v
    have he := (div_le_iff_of_neg (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hgauge.2.2.1)).1
      hgauge.2.2.2.2
    have hE : Real.exp (x.1 (projIcc 0 U hU t) v 2) ≤
        4 * (-radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          x.1 hx.choose (projIcc 0 U hU t) v) := by linarith only [he]
    have hh := mul_le_mul_of_nonneg_left hE htu.1
    linarith only [hnorm, hh]

-- A nonzero source before entry contributes nothing to the restarted kernel.
example {V : ℝ} (hV : 3 ≤ V) :
    let hV0 : 0 ≤ V := (by norm_num : (0 : ℝ) ≤ 3).trans hV
    let M : C(Icc 0 V, ℝ) := ContinuousMap.const _ 1
    let l : Icc 0 V := ⟨1, by norm_num, (by norm_num : (1 : ℝ) ≤ 3).trans hV⟩
    causalExpIntegralFrom hV0 1 2 M l = 0 ∧
      4 * (∫ t in (1 : ℝ)..3, (causalExpIntegralFrom hV0 1 2 M (projIcc 0 V hV0 t)) ^ 2) ≤ 2 := by
  dsimp only
  refine ⟨by simp [causalExpIntegralFrom], ?_⟩
  have hh := (causalExpIntegralFrom_energy ((by norm_num : (0 : ℝ) ≤ 3).trans hV)
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 3) hV (ContinuousMap.const _ 1)).2
  norm_num at hh ⊢
  exact hh

-- Absorption needs the feedback inequality only on the chosen closed subinterval.
example {V d l w : ℝ} (hV : 0 ≤ V) (hd : 0 < d)
    (hl : 0 ≤ l) (hlw : l ≤ w) (hw : w ≤ V)
    (M : C(Icc 0 V, ℝ)) (hM : ∀ v, 0 ≤ M v) {F : ℝ → ℝ}
    (hF : IntervalIntegrable (fun t => F t ^ 2) volume l w)
    (hb : ∀ v : Icc 0 V, (v : ℝ) ∈ Icc l w →
      M v ≤ F v + (d / 2) * causalExpIntegralFrom hV l d M v) :
    (∫ t in l..w, (M (projIcc 0 V hV t)) ^ 2) ≤ 4 * ∫ t in l..w, F t ^ 2 :=
  causalExpIntegralFrom_absorb_sq hV hd hl hlw hw (by positivity) le_rfl M hM hF hb

-- The two forcing terms are integrated only after entry, including l=V.
example {V : ℝ} (hV : 0 ≤ V) (l : Icc 0 V)
    (H A M : C(Icc 0 V, ℝ)) (hM : ∀ v, 0 ≤ M v)
    (hb : ∀ v, l ≤ v → M v ≤ H v + causalExpIntegralFrom hV l 1 A v +
      (1 / 4) * causalExpIntegralFrom hV l 1 M v) :
    (∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
      8 * (∫ t in (l : ℝ)..V, (H (projIcc 0 V hV t)) ^ 2) +
        8 * ∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2 := by
  have hh := early_radiation_energy (k := 1) (ρ := 1) (N := 1) (L := 1) (Lᵧ := 1)
    hV (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) l H A M hM (by simpa only [one_mul, one_pow, mul_one, div_one] using hb)
  simpa only [one_mul, one_pow, div_one, mul_one] using hh

-- The p=4 source has a profile-energy bound starting at an actual r=Y point on u=U.
set_option maxHeartbeats 1200000 in
example (G : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event)
    (hA : 0 ≤ A) (hcrit : G.innerRate = (3 / 4) * G.outerRate) (hks : G.innerRate < s)
    {h r : ℝ → ℝ} (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t) (hrinit : G.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hout
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo G.inner G.event ∧
      ∀ Y : ℝ, G.inner < Y → Y ≤ R → ∃ U₀ T E₀ E₁ : ℝ,
        0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ 0 ≤ E₀ ∧ 0 ≤ E₁ ∧
        ∀ Olo : ℝ, 0 < Olo → ∀ (ℓ : ℝ) (B : ℝ →ᵇ ℝ), Integrable (fun t => B t ^ 2) →
          MemLp (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 δ)) →
          (eLpNorm (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
            ∀ (hfU : MemLp (logarithmicIncoming (3 / 4) ℓ B) 4 (volume.restrict (Icc 0 U)))
              (x : WaveState U V)
              (hx : IsWaveIntegral hU.le hV G.charge G.cosmological
                (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0))
                (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR le_rfl hfU) x),
              ∃ S : C(Icc 0 V, ℝ), (∀ v, 0 ≤ S v) ∧
                (∀ l : Icc 0 V, T ≤ l →
                  x.1 ⟨U, hU.le, le_rfl⟩ l 0 = Y → x.2.1 ⟨U, hU.le, le_rfl⟩ l 0 < 0 →
                  (∫ t in (l : ℝ)..V, (S (projIcc 0 V hV t)) ^ 2) ≤
                    (4 / Olo) ^ 2 * (E₀ + E₁ * ∫ t, B t ^ 2)) ∧
                let ν := radialNuField hV G.charge G.cosmological
                  (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
                ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, T ≤ v → 0 < t →
                  x.1 (projIcc 0 U hU.le t) v 0 = Y → x.2.1 (projIcc 0 U hU.le t) v 0 < 0 →
                  Olo ≤ t * Real.exp (x.1 (projIcc 0 U hU.le t) v 2) →
                    Real.exp (G.innerRate * v) * |x.1 (projIcc 0 U hU.le t) v 0 * x.2.2 t v 1| ≤
                      (-ν (projIcc 0 U hU.le t) v) * S v := by
  dsimp only
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hsolve⟩ := G.exists_band_source_energy
    (b := 3 / 4) (k := G.innerRate) hs hH hdH hdHR hA (by norm_num) (by norm_num)
    (by simpa only [mul_comm] using hcrit) hks hc hout hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨U₀, T, _j, _D, _η, _C, _E₀, _E₁, F₀, F₁, hU₀, hU₀δ, hT,
    _hj, _hD, _hη, _hC, _hE₀, _hE₁, hF₀, hF₁, hb⟩ :=
    hsolve Y hY hYR
  refine ⟨U₀, T, F₀, F₁, hU₀, hU₀δ, hT, hF₀, hF₁, ?_⟩
  intro Olo hOlo ℓ B hB hf hfn
  obtain ⟨g, _hgc, _hga, _hgl, _hdc, _hstart, _hpoint, hphysical⟩ := hb Olo hOlo 4 le_rfl ℓ B hB hf hfn
    (by norm_num; linarith only [hcrit])
  intro U V hU hV hUR hUU hfU x hx
  obtain ⟨_w, _hw0, S, _hw, _hwa, hS0, _henergy, _hlevel, hidentify, _hnuY, _htraceE, hSE, hsource⟩ :=
    hphysical U V hU hV hUR hUU hfU x hx
  refine ⟨S, hS0, ?_, hsource⟩
  intro l hTl hrad hlam
  have he := hidentify ⟨U, hU.le, le_rfl⟩ l hU hrad hlam
  exact hSE l V hTl l.property.2 le_rfl he.le

-- At p=4 the actual compact chart supplies every geometric premise of the difference kernel.
example (B : Background) {s l H dH A Apt Ycap : ℝ} {h r : ℝ → ℝ}
    (hcrit : B.innerRate = (3 / 4) * B.outerRate) (hks : B.innerRate < s) (hl : l < 2 * s + B.innerRate)
    (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hApt : 0 ≤ Apt)
    (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) (hcap : B.inner < Ycap) :
    let hi := horizon_mass_integrable (B.innerRate_pos.trans hks) hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ β δ Y U₀ Ly Olo : ℝ, 0 < β ∧ 0 < δ ∧ B.inner < Y ∧ Y ≤ Ycap ∧
      0 < U₀ ∧ U₀ ≤ δ ∧ 0 < Ly ∧ 0 < Olo ∧
      ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        (∀ᵐ t ∂volume.restrict (Icc 0 δ), |f t| ≤ Apt * t ^ (-1 / 4 : ℝ)) →
        ∃ arrival : ℝ → ℝ, (∀ u ∈ Ioc 0 U₀, 0 < arrival u) ∧
          ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
            (hx : IsWaveIntegral hU.le hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR le_rfl hfU) x), U ≤ U₀ →
            arrival U ≤ V → V ≤ (1 + β) * arrival U →
            let u : Icc 0 U := ⟨U, hU.le, le_rfl⟩
            let v : Icc 0 V := ⟨V, hV, le_rfl⟩
            let ν := radialNuField hV B.charge B.cosmological
              (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
            ∀ S M : C(Icc 0 V, ℝ), (∀ v, 0 ≤ S v) → (∀ v, 0 ≤ M v) →
              (∀ (q : Icc 0 U) (v : Icc 0 V),
                Real.exp (B.innerRate * v) * |x.1 q v 0 * x.2.1 q v 1| ≤ M v) →
              (∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, arrival U ≤ (v : ℝ) → 0 < t →
                x.1 (projIcc 0 U hU.le t) v 0 = Y → x.2.1 (projIcc 0 U hU.le t) v 0 < 0 →
                Olo ≤ t * Real.exp (x.1 (projIcc 0 U hU.le t) v 2) →
                Real.exp (B.innerRate * v) * |x.1 (projIcc 0 U hU.le t) v 0 * x.2.2 t v 1| ≤
                  (-ν (projIcc 0 U hU.le t) v) * S v) →
              ∃ z : Icc 0 U, 0 < (z : ℝ) ∧ x.1 z v 0 = Y ∧
                Real.exp (B.innerRate * V) * |x.1 u v 0 * x.2.1 u v 1 - x.1 z v 0 * x.2.1 z v 1| ≤
                    (Real.exp 2 * Ly) * Ly / (B.inner / 2) *
                      causalExpIntegralFrom hV (arrival U) B.innerRate S v +
                    (Real.exp 2 * Ly) * Ly * (2 * Real.exp 1) / (4 * B.innerRate * (B.inner / 2) ^ 2) *
                      causalExpIntegralFrom hV (arrival U) B.innerRate M v := by
  dsimp only
  obtain ⟨_hc, c, β, ε, _hhc, _hhck, _htail, _heq, hc0, hck, hcs, hβ, _hβ8, _hlink,
    hε, hε8, _hεβ, _hnu, hℓ, hJ, hQ⟩ := exists_linked_inner_parameters B.innerRate_pos hks hl
  have hεk : ε < B.innerRate := by linarith only [hε8, B.innerRate_pos]
  have hca : c < B.outerRate := by linarith only [hck, hcrit, B.outerRate_pos]
  have hcb : c ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    simp only [ENNReal.toReal_ofNat]
    linarith only [hck, hcrit]
  obtain ⟨δ, Y, U₀, Ly, _j, _D, Olo, _Ohi, hδ, _hδr, hY, hYcap, hU₀, hUδ,
    hLy, _hj, _hD, hOlo, _hOhi, _hfeedback, hsolve⟩ :=
    B.exists_early_exact_geometry (B.innerRate_pos.trans hks) hH hdH hdHR hA hApt hc0 hca hcs.le
      hε hεk hε hβ.le hℓ hJ hQ le_rfl hcb hc hb hrc hrb hrinit hrd hrdec hOut Ycap hcap
  refine ⟨β, δ, Y, U₀, Ly, Olo, hβ, hδ, hY, hYcap, hU₀, hUδ, hLy, hOlo, ?_⟩
  intro f hf hfn hpoint
  obtain ⟨arrival, _hac, _haa, _hal, hpos, _hscale, _hmatch, _hpre, hchart, _hgeom⟩ :=
    hsolve f hf hfn (by simpa only [ENNReal.toReal_ofNat] using hpoint)
  refine ⟨arrival, hpos, ?_⟩
  intro U V hU hV hUR hfU x hx hUU hentry hwindow S M hS0 hM0 hM hS
  let u : Icc 0 U := ⟨U, hU.le, le_rfl⟩
  let v : Icc 0 V := ⟨V, hV, le_rfl⟩
  let l₀ : Icc 0 V := ⟨arrival U, (hpos U ⟨hU, hUU⟩).le, hentry⟩
  obtain ⟨z, hzu, T, hz, hTz, hder, hdata⟩ := hchart hU hV hUR hfU hx hUU u v hU hentry hwindow
  have hzY := (hdata z (left_mem_Icc.2 (show (z : ℝ) ≤ u from hzu))).2.2.1
  simp only [projIcc_of_mem hU.le z.property, hTz] at hzY
  refine ⟨z, hz, hzY, ?_⟩
  apply hx.early_radiation_causal hU.le hV hUR le_rfl hfU B.innerRate_pos (half_pos B.inner_pos)
    (by positivity : 0 ≤ 2 * Real.exp 1) (by positivity : 0 ≤ Real.exp 2 * Ly)
    S M hS0 hM0 l₀ z u hzu v T
    ((hdata u (right_mem_Icc.2 (show (z : ℝ) ≤ u from hzu))).2.2.2.2.2.2.2.1) hTz
    (fun t ht => (hdata t ht).2.1) (fun t ht => (hdata t ht).2.2.2.1)
    (fun t ht => ⟨(hdata t ht).2.2.2.2.1, (hdata t ht).2.2.2.2.2.1⟩) hder
    (fun t ht v hv => ((hdata t ht).2.2.2.2.2.2.2.2 v hv).1)
    (fun t ht v hv => by simpa only [neg_mul] using ((hdata t ht).2.2.2.2.2.2.2.2 v hv).2.1)
    (fun t ht => by simpa only [neg_mul] using
      ((hdata t ht).2.2.2.2.2.2.2.2 v (right_mem_Icc.2 (hdata t ht).2.1)).2.2)
    (fun _ _ v _ => hM _ v)
  filter_upwards [hS] with t ht
  intro htz
  obtain ⟨_heq, _htb, hrY, _hn, _hlamlo, hlam, hO, hlate, _hhist⟩ := hdata t htz
  exact ht _ hlate (hz.trans_le htz.1) hrY hlam hO

-- Critical early energy and actual gamma transport use the same matching curve and envelope.
example (G : Background) {s l H dH A Apt : ℝ} {h r : ℝ → ℝ}
    (hcrit : G.innerRate = (3 / 4) * G.outerRate) (hks : G.innerRate < s) (hl : l < 2 * s + G.innerRate)
    (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < G.event) (hA : 0 ≤ A) (hApt : 0 ≤ Apt)
    (hc : Continuous h) (hout : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, G.event - dH ≤ r t) (hrinit : G.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass G.mass h t) G.charge G.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - G.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : G.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable (G.innerRate_pos.trans hks) hH hc hout
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ β δ Y U₀ T D E₀ E₁ F₀ F₁ Dlo Dhi : ℝ, 0 < β ∧ 0 < δ ∧ Y ∈ Ioo G.inner G.event ∧
      0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ 0 < D ∧ 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ 0 ≤ F₀ ∧ 0 ≤ F₁ ∧
      0 < Dlo ∧ 0 < Dhi ∧
      ∀ (ℓ : ℝ) (P : ℝ →ᵇ ℝ), Integrable (fun t => P t ^ 2) →
        MemLp (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 δ)) →
        (eLpNorm (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
        (∀ᵐ t ∂volume.restrict (Icc 0 δ),
          |logarithmicIncoming (3 / 4) ℓ P t| ≤ Apt * t ^ (-1 / 4 : ℝ)) →
        ∃ g : ℝ → ℝ, ∀ (U V : ℝ) (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
          ∀ (hfU : MemLp (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U)))
            (x : WaveState U V),
            IsWaveIntegral hU.le hV G.charge G.cosmological
              (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0))
              (horizonWaveVelocity G.mass G.charge G.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR le_rfl hfU) x →
            ∃ (w : C(Icc 0 V, ℝ)) (hw0 : ∀ v, 0 ≤ w v),
              (∀ v, w v = g (max T (v : ℝ))) ∧ (∀ v : Icc 0 V, (v : ℝ) ≤ T → U ≤ w v) ∧
              (∀ v : Icc 0 V, T ≤ v → g v ≤ U → x.1 (projIcc 0 U hU.le (g v)) v 0 = Y) ∧
              (∀ t : ℝ, T ≤ t → g t ≤ U → (1 + β) * t ≤ V →
                let u := projIcc 0 U hU.le (g t)
                let a := projIcc 0 V hV t
                Dlo * g t ≤ -x.2.1 u a 0 / Real.exp (x.1 u a 2) ∧
                -x.2.1 u a 0 / Real.exp (x.1 u a 2) ≤ Dhi * g t ∧
                (∫ v in t..(1 + β) * t, intervalExtension hV (x.1 u) v 0 *
                  (intervalExtension hV (x.2.1 u) v 1) ^ 2 /
                    (-intervalExtension hV (x.2.1 u) v 0)) ≤ 1 / 16 ∧
                ∀ hr : ∀ q v, x.1 q v 0 ≠ 0,
                  let ν := radialNuField hV G.charge G.cosmological
                    (incomingWaveCurve hU.le hUR le_rfl hfU (horizonPhi h r 0)) x.1 hr
                  ∀ a' b' : Icc 0 V, t ≤ a' → a' ≤ b' → (b' : ℝ) ≤ (1 + β) * t →
                    G.inner / 2 ≤ x.1 u b' 0 ∧
                    |ν u b'| ≤ (2 * Real.exp 2) * (-ν u a') * Real.exp (-2 * G.innerRate * ((b' : ℝ) - a')) ∧
                    |x.2.1 u b' 0| ≤ (Real.exp (2 + 1 / 16) * (-x.2.1 u a' 0)) *
                      Real.exp (-2 * G.innerRate * ((b' : ℝ) - a'))) ∧
              let W : C(Icc 0 V, ℝ) := ⟨fun v => w (projIcc 0 V hV ((v : ℝ) / (1 + β))), by fun_prop⟩
              let hW0 := fun v : Icc 0 V => hw0 (projIcc 0 V hV ((v : ℝ) / (1 + β)))
              let M := movingSpatialRadiationEnvelope W hW0 0 G.innerRate 0 x
              let Z := fun t v : ℝ => g t * Real.exp (G.innerRate * t) *
                (intervalExtension hV (intervalExtension hU.le x.1 (g t)) v 0 *
                  derivWithin (fun u => intervalExtension hV (intervalExtension hU.le x.1 u) v 1)
                    (Icc 0 U) (g t))
              (∫ t in (0 : ℝ)..V,
                (M (projIcc 0 V hV t)) ^ 2) ≤ E₀ + E₁ * ∫ t, P t ^ 2 ∧
              (∀ l q : ℝ, T ≤ l → l ≤ q → q ≤ V → g l ≤ U →
                (∫ t in l..q, (Z t t) ^ 2) ≤ F₀ + F₁ * ∫ t, P t ^ 2) ∧
              (∀ t : ℝ, T ≤ t → g t ≤ U → (1 + β) * t ≤ V →
                |Z t ((1 + β) * t)| ≤ |Z t t| + (2 * Real.exp 1) * D / (G.inner / 2) *
                  ∫ v in t..(1 + β) * t, Real.exp (-(3 * G.innerRate) * (v - t)) *
                    M (projIcc 0 V hV v)) ∧
              ∀ l q : ℝ, T ≤ l → l ≤ q → (1 + β) * q ≤ V → g l ≤ U →
                (∫ t in l..q, (Z t ((1 + β) * t)) ^ 2) ≤
                  2 * (F₀ + F₁ * ∫ t, P t ^ 2) +
                    2 * ((2 * Real.exp 1) * D / (G.inner / 2) / (3 * G.innerRate)) ^ 2 *
                      (E₀ + E₁ * ∫ t, P t ^ 2) := by
  dsimp only
  obtain ⟨_hc, c, β, ε, _hhc, _hhck, _htail, _heq, hc0, hck, hcs, hβ, _hβ8, _hlink,
    hε, hε8, _hεβ, _hnu, hℓ, hJ, hQ⟩ := exists_linked_inner_parameters G.innerRate_pos hks hl
  have hεk : ε < G.innerRate := by linarith only [hε8, G.innerRate_pos]
  have hca : c < G.outerRate := by linarith only [hck, hcrit, G.outerRate_pos]
  have hcb : c ≤ G.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    simp only [ENNReal.toReal_ofNat]
    linarith only [hck, hcrit]
  obtain ⟨δ, Y, U₀, T, _jr, D, _η, _C, E₀, E₁, F₀, F₁, Dlo, Dhi, hδ, _hδr, hY, _hYcap,
    hU₀, hUδ, hT, _hjr, hD, _hη, _hC, hE₀, hE₁, hF₀, hF₁, hDlo, hDhi, hsolve⟩ :=
    G.exists_early_radiation_energy (G.innerRate_pos.trans hks) hH hdH hdHR hA hApt hc0 hca hcs.le
      hε hεk hε hβ.le hℓ hJ hQ (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
      (by simpa only [mul_comm] using hcrit) hks le_rfl hcb (by norm_num; linarith only [hcrit])
      hc hout hrc hrb hrinit hrd hrdec hOut G.event G.inner_lt_event
  refine ⟨β, δ, Y, U₀, T, D, E₀, E₁, F₀, F₁, Dlo, Dhi, hβ, hδ, hY, hU₀, hUδ, hT, hD,
    hE₀, hE₁, hF₀, hF₁, hDlo, hDhi, ?_⟩
  intro ℓ P hP hf hfn hpoint
  obtain ⟨g, _hgc, _hga, _hgl, _hdc, hstart, _hgp, hphysical⟩ :=
    hsolve ℓ P hP hf hfn (by simpa only [ENNReal.toReal_ofNat] using hpoint)
  refine ⟨g, ?_⟩
  intro U V hU hV hUR hUU hfU x hx
  obtain ⟨w, hw0, hw, _hwa, hlevel, hoptical, henergy⟩ := hphysical U V hU hV hUR hUU hfU x hx
  refine ⟨w, hw0, hw, ?_, hlevel, fun t hTt hgtU hγV => hoptical t hTt hgtU hβ hγV, henergy⟩
  intro v hv
  rw [hw, max_eq_left hv]
  exact (hUU.trans_lt hstart).le

-- The actual derivative estimate includes the one-sided right spatial boundary.
example {U V e Λ k ρ N : ℝ} (hU : 0 < U) (hV : 0 ≤ V)
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU.le hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hz : zIn = ContinuousMap.const _ c + horizontalPrimitive hU.le uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hf : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 1 = f u)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (M : C(Icc 0 V, ℝ)) (T b : Icc 0 V) (hTb : T ≤ b) :
    let u : Icc 0 U := ⟨U, hU.le, le_rfl⟩
    let ν := radialNuField hV e Λ zIn x.1 hx.choose
    let Z := fun v => x.1 u v 0 *
      derivWithin (fun t => intervalExtension hU.le x.1 t v 1) (Icc 0 U) U
    ν u T < 0 → (∀ v ∈ Icc T b, ρ ≤ x.1 u v 0) →
    (∀ v ∈ Icc T b, |ν u v| ≤ N * (-ν u T) * Real.exp (-(2 * k) * ((v : ℝ) - T))) →
    (∀ v ∈ Icc T b, Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v) →
      Real.exp (k * T) * |Z b| ≤ Real.exp (k * T) * |Z T| +
        N * (-ν u T) / ρ * ∫ w in (T : ℝ)..b,
          Real.exp (-(3 * k) * (w - T)) * M (projIcc 0 V hV w) := by
  intro u ν Z hn hr hν hM
  simpa only [show 2 * k + k = 3 * k by ring] using
    hx.transverse_radiation_majorant (k := k) (q := 2 * k) hz hinu hc hf hρ hN M
      u hU T b hTb hn hr hν hM

-- Terminal energy does not require a nonnegative forcing or a positive terminal time.
example {V d : ℝ} (hV : 0 ≤ V) (hd : 0 < d) (M : C(Icc 0 V, ℝ))
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 V))
    (hb : ∀ t ∈ Icc 0 V, |F t| ≤
      ∫ v in t..V, Real.exp (-d * (v - t)) * M (projIcc 0 V hV v)) :
    (∫ t in (0 : ℝ)..V, F t ^ 2) ≤
      2 * (1 / d) ^ 2 * ∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), intervalIntegral.integral_zero,
    mul_zero, zero_add] using
    terminalExpIntegral_add_energy (C := 1) (G := fun _ => 0) hV hd le_rfl hV le_rfl
      M hF continuousOn_const (fun t ht => by simpa only [abs_zero, one_mul, zero_add] using hb t ht)

-- Actual transverse radiation remains continuous up to the right spatial boundary.
example {U V e Λ : ℝ} (hU : 0 < U) (hV : 0 ≤ V)
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU.le hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hz : zIn = ContinuousMap.const _ c + horizontalPrimitive hU.le uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
    (hf : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 1 = f u) :
    ContinuousOn (fun t => intervalExtension hV (intervalExtension hU.le x.1 U) t 0 *
      derivWithin (fun u => intervalExtension hV (intervalExtension hU.le x.1 u) t 1)
        (Icc 0 U) U) (Icc 0 V) :=
  hx.scalar_curve_continuous hz hinu hc hf continuousOn_const continuousOn_id
    (fun _ _ => ⟨hU, le_rfl⟩)

-- The primitive identity allows an inner kernel that grows with its time difference.
example {l v : ℝ} (hlv : l ≤ v) {M : ℝ → ℝ} (hc : Continuous M)
    (hM : ∀ t ∈ Icc l v, 0 ≤ M t) :
    (∫ t in l..v, Real.exp (-(v - t)) *
      ∫ w in t..v, Real.exp ((1 / 2 : ℝ) * (w - t)) * M w) ≤
        2 * ∫ t in l..v, Real.exp (-(v - t)) * M t := by
  have hh := (exponential_double_kernel_bound (k := 1) (q := -(1 / 2))
    (by norm_num) hlv hc hM).2.2
  norm_num at hh ⊢
  exact hh

-- The late kernel retains its decaying weight, including a degenerate interval.
example {l v : ℝ} (hlv : l ≤ v) {M : ℝ → ℝ} (hc : Continuous M)
    (hM : ∀ t ∈ Icc l v, 0 ≤ M t) :
    Real.exp (-v) * (∫ t in l..v, Real.exp ((7 / 5 : ℝ) * t) *
      ∫ w in t..v, Real.exp (-w) * M w) ≤
        (5 / 7 : ℝ) * ∫ t in l..v,
          Real.exp (-(v - t)) * Real.exp (-(3 / 5 : ℝ) * t) * M t := by
  have hh := late_double_kernel_bound (k := 1) (χ := 3 / 5) (by norm_num) hlv hc hM
  norm_num at hh ⊢
  exact hh

-- Actual p=4 scalar transport gives both late causal sources with the full entry trace.
example {U V R e Λ φ₀ k ξ χ ρ C D : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U)))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x)
    (hρ : 0 < ρ) (hD : 0 ≤ D) (hgap : 0 < 2 * k - χ)
    (A M : C(Icc 0 V, ℝ)) (hM0 : ∀ v, 0 ≤ M v)
    (z u : Icc 0 U) (hzu : z ≤ u) (b : Icc 0 V)
    (T : C(Icc (z : ℝ) u, Icc 0 V)) (J : C(Icc (z : ℝ) u, ℝ)) (N : ℝ → ℝ) :
    let τ := fun t => T (projIcc (z : ℝ) u hzu t)
    let j := fun t => J (projIcc (z : ℝ) u hzu t)
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) x.1 hx.choose
    τ z = b → (∀ t ∈ Icc (z : ℝ) u, τ t ≤ b) →
    (∀ t ∈ Ioo (z : ℝ) u, HasDerivAt (fun t => (τ t : ℝ)) (-j t) t) →
    (∀ t ∈ Icc (z : ℝ) u, 0 ≤ N t) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b, ρ ≤ x.1 (projIcc 0 U hU t) v 0) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b, |ν (projIcc 0 U hU t) v| ≤ N t) →
    (∀ t ∈ Icc (z : ℝ) u,
      |x.2.1 (projIcc 0 U hU t) b 0| * N t ≤
        D * j t * Real.exp (-(2 * k) * b + (2 * k - χ) * τ t)) →
    (∀ t ∈ Icc (z : ℝ) u, ∀ v ∈ Icc (τ t) b,
      Real.exp (k * v) * |x.1 (projIcc 0 U hU t) v 0 * x.2.1 (projIcc 0 U hU t) v 1| ≤ M v) →
    (∀ᵐ t ∂volume.restrict (Icc 0 U), t ∈ Icc (z : ℝ) u →
      |x.2.1 (projIcc 0 U hU t) b 0| *
        |x.1 (projIcc 0 U hU t) (τ t) 0 * x.2.2 t (τ t) 1| ≤
          C * j t * Real.exp (-(2 * k) * b + (k - ξ) * τ t) * A (τ t)) →
      Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1| ≤
        Real.exp (k * b) * |x.1 z b 0 * x.2.1 z b 1| +
          C / ρ * (∫ t in (τ u : ℝ)..b,
            Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-ξ * t) * A (projIcc 0 V hV t)) +
          D / (ρ ^ 2 * (2 * k - χ)) * ∫ t in (τ u : ℝ)..b,
            Real.exp (-k * ((b : ℝ) - t)) * Real.exp (-χ * t) * M (projIcc 0 V hV t) := by
  dsimp only
  intro hz hb hd hN hr hν hfeedback hM hfree
  exact (hx.late_radiation_causal hU hV hUR le_rfl hf hρ hD hgap A M hM0 z u hzu b T J N
    hz hb hd hN hr hν hfeedback hM hfree).2

-- The same inverse curve supplies the Jacobian that absorbs a singular incoming power.
example {g v : ℝ → ℝ} {u j a q α η C : ℝ}
    (hu : 0 < u) (hj : 0 < j) (hq : 0 ≤ q) (hα : 0 < α) (hη : 0 < η) (hC : 0 < C)
    (hg : g (v u) = u) (hd : HasDerivAt v (deriv g (v u))⁻¹ u)
    (hlo : η ≤ -deriv g (v u) / g (v u)) (hhi : -deriv g (v u) / g (v u) ≤ C)
    (hscale : j ≤ g (v u) * Real.exp (a * v u)) :
    u ^ (-1 - q) ≤ (C / α) * (-deriv (fun x => α * v x) u) *
      j ^ (-q) * Real.exp (a * q * v u) := by
  have hJ := arrival_inverse_jacobian_bounds hu hα.le hη hg hd hlo hhi
  exact arrival_jacobian_power_bound hu hj hq hα hC (by simpa only [hg] using hscale) hJ.1

-- At p=4 the feedback exponent is 2k-3xi and the free source exponent is k-xi.
example {u j k t β C J : ℝ} (hu : 0 < u) (hj : 0 < j)
    (hβ : 0 ≤ β) (hβ8 : β < 1 / 8) (hC : 0 < C)
    (hscale : j ≤ u * Real.exp ((4 * k / 3) * t))
    (hJac : (1 + β) / (C * u) ≤ J) :
    u ^ (-1 - (3 / 2 - 3 * β / 4)) ≤
      (C / (1 + β)) * J * j ^ (-(3 / 2 - 3 * β / 4)) *
        Real.exp ((2 * k - 3 * (k * β / (1 + β))) * ((1 + β) * t)) ∧
    u ^ (-1 - (3 / 2 : ℝ)) * Real.exp (-k * t) ≤
      (C / (1 + β)) * J * j ^ (-(3 / 2 : ℝ)) *
        Real.exp ((k - k * β / (1 + β)) * ((1 + β) * t)) := by
  have hα : 0 < 1 + β := by linarith only [hβ]
  constructor
  · have hh := arrival_jacobian_power_bound hu hj
      (by linarith only [hβ8] : 0 ≤ 3 / 2 - 3 * β / 4) hα hC hscale hJac
    have he : (4 * k / 3) * (3 / 2 - 3 * β / 4) * t =
        (2 * k - 3 * (k * β / (1 + β))) * ((1 + β) * t) := by
      field_simp
      ring
    rwa [he] at hh
  · have hh := mul_le_mul_of_nonneg_right
      (arrival_jacobian_power_bound hu hj (by norm_num : (0 : ℝ) ≤ 3 / 2) hα hC hscale hJac)
      (Real.exp_pos (-k * t)).le
    rw [mul_assoc, ← Real.exp_add] at hh
    have he : (4 * k / 3) * (3 / 2) * t + -k * t =
        (k - k * β / (1 + β)) * ((1 + β) * t) := by
      field_simp
      ring
    rwa [he] at hh

-- The inverse Jacobian bounds include the zero-dilation endpoint.
example {g v : ℝ → ℝ} {u η C : ℝ}
    (hu : 0 < u) (hη : 0 < η) (hg : g (v u) = u)
    (hd : HasDerivAt v (deriv g (v u))⁻¹ u)
    (hlo : η ≤ -deriv g (v u) / g (v u)) (hhi : -deriv g (v u) / g (v u) ≤ C) :
    (0 : ℝ) / (C * u) ≤ -deriv (fun x => (0 : ℝ) * v x) u ∧
      -deriv (fun x => (0 : ℝ) * v x) u ≤ (0 : ℝ) / (η * u) :=
  arrival_inverse_jacobian_bounds hu le_rfl hη hg hd hlo hhi

-- A degenerate entered row still has its physical gamma endpoint and positive Jacobian.
example {U V T α η C Y : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {x : WaveState U V} {g : ℝ → ℝ}
    (hc : RadiationGammaCharts hU hV x g T α η C Y)
    (u : Icc 0 U) (b : Icc 0 V) (hb : T < (b : ℝ) / α)
    (hu : g ((b : ℝ) / α) = u) :
    ∃ (Q : C(Icc (u : ℝ) u, Icc 0 V)) (J : C(Icc (u : ℝ) u, ℝ)),
      Q (projIcc (u : ℝ) u le_rfl u) = b ∧
        0 < J (projIcc (u : ℝ) u le_rfl u) ∧
        α / (C * u) ≤ J (projIcc (u : ℝ) u le_rfl u) ∧
        J (projIcc (u : ℝ) u le_rfl u) ≤ α / (η * u) := by
  obtain ⟨z, hzu, Q, J, hz, _hz0, hQz, _hder, hpoint⟩ := hc u b hb hu.le
  have he : z = u := Subtype.ext (hz.trans hu)
  subst z
  exact ⟨Q, J, hQz, (hpoint u ⟨le_rfl, le_rfl⟩).2.2.2.2⟩

-- The actual chart identity supplies the incoming lower scale for the late negative power.
example {U V T α η C Y j a q : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {x : WaveState U V} {g : ℝ → ℝ}
    (hc : RadiationGammaCharts hU hV x g T α η C Y)
    (hα : 0 < α) (hC : 0 < C) (hj : 0 < j) (hq : 0 ≤ q)
    (hscale : ∀ t ∈ Ici T, j ≤ g t * Real.exp (a * t))
    (u : Icc 0 U) (b : Icc 0 V) (hb : T < (b : ℝ) / α)
    (hu : g ((b : ℝ) / α) ≤ u) :
    ∃ (z : Icc 0 U) (hzu : z ≤ u)
      (Q : C(Icc (z : ℝ) u, Icc 0 V)) (J : C(Icc (z : ℝ) u, ℝ)),
      Q (projIcc (z : ℝ) u hzu z) = b ∧
      ∀ t ∈ Icc (z : ℝ) u,
        t ^ (-1 - q) ≤ (C / α) * J (projIcc (z : ℝ) u hzu t) * j ^ (-q) *
          Real.exp (a * q * ((Q (projIcc (z : ℝ) u hzu t) : ℝ) / α)) := by
  obtain ⟨z, hzu, Q, J, _hz, hz0, hQz, _hder, hpoint⟩ := hc u b hb hu
  refine ⟨z, hzu, Q, J, hQz, ?_⟩
  intro t ht
  have hp := hpoint t ht
  have hs := hscale _ hp.1.le
  rw [hp.2.1] at hs
  exact arrival_jacobian_power_bound (hz0.trans_le ht.1) hj hq hα hC hs hp.2.2.2.2.2.1

-- At p=4 and beta=1/16 the full sources have chi=3/17 and xi=1/17.
example {u j t v C J L N lam ζ A : ℝ}
    (hu : 0 < u) (hj : 0 < j) (hC : 0 < C) (hL : 0 ≤ L) (hN : 0 ≤ N)
    (hscale : j ≤ u * Real.exp ((4 / 3 : ℝ) * t))
    (hJac : (17 / 16 : ℝ) / (C * u) ≤ J)
    (hlam : |lam| ≤ L * u ^ (-(3 / 2 : ℝ)) * Real.exp (-2 * v))
    (hA : A = u * Real.exp t * |ζ|) :
    |lam| * (N * u ^ (-(61 / 64 : ℝ))) ≤
      (L * N * C / (17 / 16 : ℝ) * j ^ (-(93 / 64 : ℝ))) * J *
        Real.exp (-2 * v + (31 / 17 : ℝ) * ((17 / 16 : ℝ) * t)) ∧
    |lam| * |ζ| ≤ (L * C / (17 / 16 : ℝ) * j ^ (-(3 / 2 : ℝ))) * J *
      Real.exp (-2 * v + (16 / 17 : ℝ) * ((17 / 16 : ℝ) * t)) * A := by
  have hh := late_weighted_sources (a := 4 / 3) (k := 1) (β := 1 / 16) (v := v) (lam := lam) hu hj
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hC hL hN hscale
    (by norm_num; exact hJac) (by norm_num; simpa only [neg_mul] using hlam) (by simpa using hA)
  norm_num at hh ⊢
  exact hh

-- One null set identifies the signed actual transverse trace at every gamma time.
example {U V R e Λ φ₀ : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (hfc : ContinuousOn f (Ioi 0))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x)
    (g : C(Icc 0 V, Icc 0 U)) (hg : ∀ v, 0 < (g v : ℝ)) :
    ∃ A : C(Icc 0 V, ℝ), (∀ v, 0 ≤ A v) ∧
      (∀ v, A v = |(g v : ℝ) * Real.exp ((16 / 17 : ℝ) * v) *
        (x.1 (g v) v 0 * derivWithin (fun u => intervalExtension hU x.1 u v 1) (Icc 0 U) (g v))|) ∧
      ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ v : Icc 0 V, (g v : ℝ) = t →
        A v ^ 2 = (t * Real.exp ((16 / 17 : ℝ) * v)) ^ 2 *
          (x.1 (projIcc 0 U hU t) v 0 * x.2.2 t v 1) ^ 2 := by
  have hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), incomingWaveVelocity hUR le_rfl hf t 1 = f t := by
    filter_upwards [incomingWaveVelocity_ae hUR le_rfl hf] with t ht
    rw [ht]
    rfl
  obtain ⟨A, hA0, hA, _hAE, hsource⟩ := hx.exists_curve_radiation_source (k := 16 / 17)
    rfl (incomingWave_constraint_data hU hUR le_rfl hf φ₀).1 hfc hif g hg
  refine ⟨A, hA0, hA, ?_⟩
  filter_upwards [hsource] with t ht
  intro v hv
  rw [ht v hv, mul_pow, sq_abs]

-- The physical gamma theorem has no spurious free or feedback term when L=0.
example {U V R e Λ φ₀ a k β j C N T η Y ρ : ℝ}
    (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < R)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (hfc : ContinuousOn f (Ioi 0))
    {vOut : C(Icc 0 V, WaveVector)} {x : WaveState U V}
    (hx : IsWaveIntegral hU.le hV e Λ (incomingWaveCurve hU.le hUR le_rfl hf φ₀) vOut
      (incomingWaveVelocity hUR le_rfl hf) x)
    (ha : 0 < a) (hk : 0 < k) (hβ : 0 ≤ β) (hβ8 : β < 1 / 8)
    (hj : 0 < j) (hC : 0 < C) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (g : ℝ → ℝ) (hgc : ContinuousOn g (Ici T)) (hga : AntitoneOn g (Ici T))
    (hgp : ∀ t ∈ Ici T, 0 < g t) (hscale : ∀ t ∈ Ici T, j ≤ g t * Real.exp (a * t))
    (hchart : RadiationGammaCharts hU.le hV x g T (1 + β) η C Y)
    (M : C(Icc 0 V, ℝ)) (hM0 : ∀ v, 0 ≤ M v)
    (u : Icc 0 U) (b : Icc 0 V) (hb : T < (b : ℝ) / (1 + β)) (hgu : g ((b : ℝ) / (1 + β)) ≤ u)
    (hlam : ∀ t ∈ Icc (g ((b : ℝ) / (1 + β))) u, x.2.1 (projIcc 0 U hU.le t) b 0 = 0) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU.le hUR le_rfl hf φ₀) x.1 hx.choose
    (∀ t ∈ Icc (g ((b : ℝ) / (1 + β))) u, ∀ w : Icc 0 V,
      T < (w : ℝ) / (1 + β) → g ((w : ℝ) / (1 + β)) ≤ t → w ≤ b →
        ρ ≤ x.1 (projIcc 0 U hU.le t) w 0 ∧
        |ν (projIcc 0 U hU.le t) w| ≤ N * t ^ (k / a * β - 1) ∧
        Real.exp (k * w) * |x.1 (projIcc 0 U hU.le t) w 0 * x.2.1 (projIcc 0 U hU.le t) w 1| ≤ M w) →
      Real.exp (k * b) * |x.1 u b 0 * x.2.1 u b 1| ≤
        Real.exp (k * b) *
          |x.1 (projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))) b 0 *
            x.2.1 (projIcc 0 U hU.le (g ((b : ℝ) / (1 + β)))) b 1| := by
  dsimp only
  intro hhistory
  obtain ⟨A, _hA0, _hA, hlate⟩ := hx.exists_late_gamma_source hU hV hUR le_rfl hf hfc ha hk hβ hβ8
    hj hC (L := 0) le_rfl hN hρ g hgc hga hgp hscale hchart
  obtain ⟨s, _hsT, _hsg, _hsb, _hdiff, hbnd⟩ := hlate M hM0 u b hb hgu
    (fun t ht => by simp only [hlam t ht, abs_zero, zero_mul, le_refl]) hhistory
  simpa only [zero_mul, zero_div, add_zero] using hbnd

-- The physical flux bootstrap retains the exact p=4 corner power and time rate.
example {M e Λ U V Cd Co : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (hCd : 0 ≤ Cd) (hCo : 0 ≤ Co) (u : Icc 0 U) (hu : 0 < (u : ℝ))
    (a b : Icc 0 V) (hab : a ≤ b) (ha : x.2.1 u a 0 < 0)
    (hentry : -x.2.1 u a 0 / Real.exp (x.1 u a 2) ≤ Cd * (u : ℝ))
    (hcorner : Real.exp (x.1 u b 2) ≤ Co * ((u : ℝ) ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * b)))
    (hflux : (∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ 1 / 4) :
    |x.2.1 u b 0| ≤ (Cd * Co * Real.exp (1 / 4)) * (u : ℝ) ^ (-(3 / 2 : ℝ)) * Real.exp (-2 * b) := by
  have hh := hx.lambda_corner_of_optical_flux (k := 1) (σ := 3 / 2)
    hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf hCd hCo u hu a b hab ha hentry
    (by norm_num; simpa only [neg_mul] using hcorner) hflux
  simpa only [mul_one, neg_mul] using hh

-- Before or at first entry the capped late envelope is the actual right-endpoint trace.
example {U V k : ℝ} (hU : 0 ≤ U) (W : C(Icc 0 V, ℝ)) (x : WaveState U V)
    (v : Icc 0 V) (hv : U ≤ W v) :
    lateSpatialRadiationEnvelope W k x v =
      Real.exp (k * v) * |x.1 ⟨U, hU, le_rfl⟩ v 0 * x.2.1 ⟨U, hU, le_rfl⟩ v 1| := by
  apply le_antisymm
  · apply (lateSpatialRadiationEnvelope_le_iff hU W x v).2
    intro u hu
    have he : u = (⟨U, hU, le_rfl⟩ : Icc 0 U) := by
      apply Subtype.ext
      exact le_antisymm u.property.2 (by simpa only [min_eq_left hv] using hu)
    rw [he]
  · exact (lateSpatialRadiationEnvelope_le_iff hU W x v).1 le_rfl ⟨U, hU, le_rfl⟩ (min_le_left _ _)

-- Absorption includes its non-strict threshold and a zero-length final interval.
example {V : ℝ} (hV : 0 ≤ V) (l : Icc 0 V) (H A M : C(Icc 0 V, ℝ))
    (hM : ∀ v, 0 ≤ M v)
    (hb : ∀ v, l ≤ v → M v ≤ H v + 3 * causalExpIntegralFrom hV l 2 A v +
      causalExpIntegralFrom hV l 2 M v) :
    (∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤
      8 * (∫ t in (l : ℝ)..V, (H (projIcc 0 V hV t)) ^ 2) +
        18 * ∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2 := by
  have hh := causalExpIntegralFrom_forcing_energy (k := 2) (C := 3) (ε := 1) hV
    (by norm_num) (by norm_num) (by norm_num) l H A M hM (by simpa only [one_mul] using hb)
  norm_num at hh ⊢
  exact hh

-- Conjugation permits q=d; the remaining source factor is then exactly one.
example {V : ℝ} (hV : 0 ≤ V) (l s b : Icc 0 V) (hls : l ≤ s) (hsb : s ≤ b)
    (A : C(Icc 0 V, ℝ)) (hA : ∀ v, 0 ≤ A v) :
    Real.exp (b : ℝ) *
        (∫ t in (s : ℝ)..b, Real.exp (-2 * ((b : ℝ) - t)) * Real.exp (-t) * A (projIcc 0 V hV t)) ≤
      causalExpIntegralFrom hV l 1 A b := by
  simpa only [one_mul, neg_one_mul, show (2 : ℝ) - 1 = 1 by norm_num] using
    (causalExpIntegralFrom_weighted_le (k := 2) (q := 1) (d := 1) hV le_rfl l s b hls hsb A hA)

-- Two already controlled sources need no new absorption hypothesis.
example {V : ℝ} (hV : 0 ≤ V) (l : Icc 0 V) (A M F : C(Icc 0 V, ℝ))
    (hF : ∀ v, 0 ≤ F v)
    (hb : ∀ v, l ≤ v → F v ≤ 3 * causalExpIntegralFrom hV l 2 A v +
      4 * causalExpIntegralFrom hV l 2 M v) :
    (∫ t in (l : ℝ)..V, (F (projIcc 0 V hV t)) ^ 2) ≤
      (9 / 2 : ℝ) * (∫ t in (l : ℝ)..V, (A (projIcc 0 V hV t)) ^ 2) +
        8 * ∫ t in (l : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2 := by
  have hh := causalExpIntegralFrom_sum_energy hV (by norm_num : (0 : ℝ) < 2) l A M F hF hb
  norm_num at hh
  exact hh

-- The clamped signed difference vanishes before the curve enters the width.
example {U V k : ℝ} (hU : 0 ≤ U) (W : C(Icc 0 V, ℝ)) (x : WaveState U V)
    (v : Icc 0 V) (hv : U ≤ W v) : lateRadiationDifferenceRows hU W k x v = 0 := by
  ext u
  simp only [lateRadiationDifferenceRows, transverseRadiationRows, ContinuousMap.curry_apply,
    ContinuousMap.coe_mk, ContinuousMap.const_apply, projIcc_of_right_le hU hv,
    min_eq_left (show u ≤ ⟨U, hU, le_rfl⟩ from u.property.2),
    max_eq_left (show u ≤ ⟨U, hU, le_rfl⟩ from u.property.2), sub_self, mul_zero,
    ContinuousMap.zero_apply]

-- A fixed p=4 absorption width works for every smaller ray and arrival time.
example {d j Umax : ℝ} (hd : 0 ≤ d) (hj : 0 < j) (hUmax : 0 < Umax) :
    ∃ W : ℝ, 0 < W ∧ W ≤ Umax ∧ ∀ U t : ℝ, 0 < U → U ≤ W →
      j ≤ U * Real.exp ((4 / 3) * t) →
        d * Real.exp (-(3 / 16) * t) ≤ 1 / 2 := by
  obtain ⟨W, hW, hWmax, hb⟩ := exists_radiation_absorption_width
    (a := 4 / 3) (k := 1) (β := 1 / 16) (by norm_num) (by norm_num) (by norm_num) hj hd hUmax
  refine ⟨W, hW, hWmax, ?_⟩
  intro U t hU hUW hscale
  have he := arrival_exp_power (q := 3 / 16) (by norm_num : (0 : ℝ) < 4 / 3)
    hU hj (by norm_num) hscale
  have hh := (mul_le_mul_of_nonneg_left he hd)
  have hsmall := hb U hU.le hUW
  norm_num at hh hsmall
  simpa only [neg_mul] using hh.trans (by simpa only [mul_assoc] using hsmall)

-- The physical p=4 bound uses the full prefix, without an assumed first-entry time.
example
    {M₀ e Λ U V a k β j C Cd Co Jmax N T η Y ρ Ee Eg : ℝ} {h r : ℝ → ℝ}
    (hU : 0 < U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M₀ h t) e Λ) (Ici 0) t)
    {f : ℝ → ℝ}
    (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (hfc : ContinuousOn f (Ioi 0))
    {x : WaveState U V}
    (hx : IsWaveIntegral hU.le hV e Λ (incomingWaveCurve hU.le hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity M₀ e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (ha : 0 < a) (hk : 0 < k) (hβ : 0 ≤ β) (hβ8 : β < 1 / 8)
    (hj : 0 < j) (hC : 0 < C) (hCd : 0 ≤ Cd) (hCo : 0 ≤ Co) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (hT : 0 ≤ T) (hEg : 0 ≤ Eg)
    (g : ℝ → ℝ) (hgc : ContinuousOn g (Ici T)) (hga : StrictAntiOn g (Ici T))
    (hstart : U < g T)
    (hgp : ∀ t ∈ Ici T, 0 < g t) (hscale : ∀ t ∈ Ici T, j ≤ g t * Real.exp (a * t))
    (hchart : RadiationGammaCharts hU.le hV x g T (1 + β) η C Y)
    (W : C(Icc 0 V, ℝ)) (hW0 : ∀ v, 0 ≤ W v)
    (hW : ∀ v, W v = g (max T ((v : ℝ) / (1 + β))))
    (hr : ∀ u v, ρ ≤ x.1 u v 0)
    (entry : Icc 0 U → Icc 0 V)
    (hentry : ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V,
      T < (v : ℝ) / (1 + β) → g ((v : ℝ) / (1 + β)) ≤ u →
        entry u ≤ v ∧ x.2.1 u (entry u) 0 < 0 ∧
          -x.2.1 u (entry u) 0 / Real.exp (x.1 u (entry u) 2) ≤ Cd * (u : ℝ))
    (hcorner : ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V,
      T < (v : ℝ) / (1 + β) → g ((v : ℝ) / (1 + β)) ≤ u →
        Real.exp (x.1 u v 2) ≤ Co * ((u : ℝ) ^ (-1 - 2 * k / a) * Real.exp (-(2 * k) * v)))
    (hflux : ∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V,
      T < (v : ℝ) / (1 + β) → g ((v : ℝ) / (1 + β)) ≤ u →
        (∫ t in (entry u : ℝ)..v, intervalExtension hV (x.1 u) t 0 *
          (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ Jmax) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU.le hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    (∀ u : Icc 0 U, 0 < (u : ℝ) → ∀ v : Icc 0 V,
      T < (v : ℝ) / (1 + β) → g ((v : ℝ) / (1 + β)) ≤ u →
        |ν u v| ≤ N * (u : ℝ) ^ (k / a * β - 1)) →
    let L := Cd * Co * Real.exp Jmax
    let c := (L * C / (1 + β) * j ^ (-(2 * k / a))) / ρ
    let d := (L * N * C / (1 + β) * j ^ (-(2 * k / a - k / a * β))) /
      (ρ ^ 2 * (2 * k - 3 * (k * β / (1 + β))))
    d * j ^ (-(3 * k * β / a)) * U ^ (3 * k * β / a) ≤ k / 2 →
    let H := movingSpatialRadiationEnvelope W hW0 0 k 0 x
    let Z := fun t v : ℝ => g t * Real.exp (k * t) *
      (intervalExtension hV (intervalExtension hU.le x.1 (g t)) v 0 *
        derivWithin (fun u => intervalExtension hV (intervalExtension hU.le x.1 u) v 1)
          (Icc 0 U) (g t))
    (∫ t in (0 : ℝ)..V, (H (projIcc 0 V hV t)) ^ 2) ≤ Ee →
    (∀ s t : ℝ, T ≤ s → s ≤ t → (1 + β) * t ≤ V → g s ≤ U →
      (∫ w in s..t, (Z w ((1 + β) * w)) ^ 2) ≤ Eg) →
    let S := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 V) U) (fun _ => hU.le) 0 k 0 x
    ((∫ t in (0 : ℝ)..V, (S (projIcc 0 V hV t)) ^ 2) ≤
      9 * Ee + 8 * (1 + β) * (c / k) ^ 2 * Eg) ∧
    ∀ q : ℝ, q < k → q ≤ k * β / (1 + β) → q ≤ 3 * (k * β / (1 + β)) →
      (∫ t in (0 : ℝ)..V,
        (Real.exp (q * t) * ‖lateRadiationDifferenceRows hU.le W k x (projIcc 0 V hV t)‖) ^ 2) ≤
      2 * (c / (k - q)) ^ 2 * ((1 + β) * Eg) +
        2 * (d / (k - q)) ^ 2 * (8 * Ee + 8 * (1 + β) * (c / k) ^ 2 * Eg) := by
  exact hx.full_radiation_energy_of_optical_flux hU hV hUR hc hi hrc hr0 hφ hrd
    le_rfl hf hfc ha hk hβ hβ8 hj hC hCd hCo hN hρ hT hEg g hgc hga hstart hgp hscale
    hchart W hW0 hW hr entry hentry hcorner hflux

-- The critical p=4 density has the exact 5/2 incoming power.
example {R ell P S u v Co ρ : ℝ}
    (hu : 0 < u) (hρ : 0 < ρ) (hCo : 0 < Co) (hR : ρ ≤ R)
    (hcorner : Co * (u ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * v)) ≤ Real.exp ell)
    (hS : Real.exp v * |R * P| ≤ S) :
    R * Real.exp (-ell) * P ^ 2 ≤ u ^ (5 / 2 : ℝ) / (ρ * Co) * S ^ 2 := by
  have hh := optical_density_le_of_corner (k := 1) (σ := 3 / 2) (v := v) hu hρ hCo hR
    (by norm_num; simpa only [neg_mul] using hcorner) (by simpa only [one_mul] using hS)
  norm_num at hh
  exact hh

section OpticalFlux

variable {M e Λ U V Cd Co ρ : ℝ} {h r : ℝ → ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
  {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
    (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
  (hCd : 0 < Cd) (hCo : 0 < Co) (hρ : 0 < ρ) (u : Icc 0 U) (hu : 0 < (u : ℝ))

include hφ hrd hx

-- The actual full supremum supplies the majorant, with a strict bootstrap margin.
example {E : ℝ} (a γ b : Icc 0 V) (haγ : a ≤ γ) (hγb : γ ≤ b)
    (hentry : Cd * (u : ℝ) ≤ -x.2.1 u a 0 / Real.exp (x.1 u a 2))
    (hr : ∀ v : Icc 0 V, γ ≤ v → v ≤ b → ρ ≤ x.1 u v 0)
    (hcorner : ∀ v : Icc 0 V, γ ≤ v → v ≤ b →
      Co * ((u : ℝ) ^ (-(5 / 2 : ℝ)) * Real.exp (-2 * v)) ≤ Real.exp (x.1 u v 2))
    (hinitial : (∫ t in (a : ℝ)..γ, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ 1 / 16)
    (hsmall : (u : ℝ) ^ (3 / 2 : ℝ) / (Cd * ρ * Co) * E ≤ Real.exp (1 / 16) - 1) :
    let S := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 V) U) (fun _ => hU) 0 1 0 x
    (∫ t in (0 : ℝ)..V, (S (projIcc 0 V hV t)) ^ 2) ≤ E →
    (-x.2.1 u b 0 / Real.exp (x.1 u b 2)) -
        (-x.2.1 u γ 0 / Real.exp (x.1 u γ 2)) ≤ (u : ℝ) ^ (5 / 2 : ℝ) / (ρ * Co) * E ∧
    (∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤ 1 / 8 := by
  dsimp only
  intro henergy
  let S := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 V) U) (fun _ => hU) 0 1 0 x
  have hS (v : Icc 0 V) : Real.exp (1 * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ S v := by
    simpa only [zero_mul, sub_zero] using
      (movingSpatialRadiationEnvelope_le_iff (a := 0) (k := 1) (σ := 0) hU
        (ContinuousMap.const (Icc 0 V) U) (fun _ => hU) x v).1 le_rfl u u.property.2
  have hh := hx.optical_flux_of_radiation_energy (k := 1) (σ := 3 / 2)
    hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf hCd hCo hρ u hu a γ b haγ hγb hentry hr
    (by intro v hv hb; norm_num; simpa only [neg_mul] using hcorner v hv hb)
    S (fun v _ _ => hS v) henergy hinitial
  norm_num only at hh
  refine ⟨hh.1, ?_⟩
  have hE : 0 ≤ E := (intervalIntegral.integral_nonneg hV (fun t _ => sq_nonneg _)).trans henergy
  have hlog : Real.log (1 + (u : ℝ) ^ (3 / 2 : ℝ) / (Cd * ρ * Co) * E) ≤ 1 / 16 :=
    (Real.log_le_iff_le_exp (by positivity)).2 (by linarith only [hsmall])
  linarith only [hh.2, hlog]

-- Zero energy leaves no additional flux, also when entry, gamma or observation coincide.
example {k σ : ℝ} (a γ b : Icc 0 V) (haγ : a ≤ γ) (hγb : γ ≤ b)
    (hentry : Cd * (u : ℝ) ≤ -x.2.1 u a 0 / Real.exp (x.1 u a 2))
    (hr : ∀ v : Icc 0 V, γ ≤ v → v ≤ b → ρ ≤ x.1 u v 0)
    (hcorner : ∀ v : Icc 0 V, γ ≤ v → v ≤ b →
      Co * ((u : ℝ) ^ (-1 - σ) * Real.exp (-(2 * k) * v)) ≤ Real.exp (x.1 u v 2))
    (S : C(Icc 0 V, ℝ))
    (hS : ∀ v : Icc 0 V, γ ≤ v → v ≤ b → Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ S v)
    (henergy : (∫ t in (0 : ℝ)..V, (S (projIcc 0 V hV t)) ^ 2) ≤ 0) :
    (-x.2.1 u b 0 / Real.exp (x.1 u b 2)) ≤ (-x.2.1 u γ 0 / Real.exp (x.1 u γ 2)) ∧
    (∫ t in (a : ℝ)..b, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) ≤
    (∫ t in (a : ℝ)..γ, intervalExtension hV (x.1 u) t 0 *
      (intervalExtension hV (x.2.1 u) t 1) ^ 2 / (-intervalExtension hV (x.2.1 u) t 0)) := by
  have hh := hx.optical_flux_of_radiation_energy hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf
    hCd hCo hρ u hu a γ b haγ hγb hentry hr hcorner S hS henergy le_rfl
  simpa only [mul_zero, add_zero, Real.log_one, sub_nonpos] using hh

end OpticalFlux

section RadiationHalfline

variable {U k : ℝ} (X : (T : Ici (0 : ℝ)) → WaveState U T)
  (hcompat : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
    waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
      le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)

include hcompat

-- The half-line row is the signed actual radiation in every containing rectangle.
example (T : Ici (0 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 (T : ℝ)) (u : Icc 0 U) :
    radiationRow k X t u = Real.exp (k * t) * ((X T).1 u ⟨t, ht⟩ 0 * (X T).2.1 u ⟨t, ht⟩ 1) := by
  rw [radiationRow_eq X hcompat T ht.2]
  simp only [spatialRadiationRows, ContinuousMap.curry_apply, ContinuousMap.coe_mk,
    projIcc_of_mem T.property ht, zero_mul, sub_zero]

-- The common energy budget may vanish; continuity and L2 membership still hold.
example (hU : 0 ≤ U)
    (henergy : ∀ T : Ici (0 : ℝ),
      let S := movingSpatialRadiationEnvelope (ContinuousMap.const (Icc 0 (T : ℝ)) U)
        (fun _ => hU) 0 k 0 (X T)
      (∫ t in (0 : ℝ)..(T : ℝ), (S (projIcc 0 (T : ℝ) T.property t)) ^ 2) ≤ 0) :
    Continuous (radiationRow k X) ∧ MemLp (radiationRow k X) 2 (volume.restrict (Ici 0)) ∧
      (∫ t in Ici (0 : ℝ), ‖radiationRow k X t‖ ^ 2) = 0 := by
  obtain ⟨hLp, hb⟩ := radiationRow_energy X hcompat hU henergy
  exact ⟨continuous_radiationRow X hcompat, hLp,
    le_antisymm hb (integral_nonneg (fun t => sq_nonneg _))⟩

end RadiationHalfline

-- Zero optical flux needs no sign or lower bound on the transverse derivative.
example {r ν ell e Λ ρ R : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ r) (hR : r ≤ R) (hΛ : 0 ≤ Λ) :
    renormalizedMass r ν 0 ell e Λ ≤ R / 2 + e ^ 2 / (2 * ρ) := by
  simpa only [mul_zero, add_zero] using renormalizedMass_le_of_optical
    (ν := ν) (l := 0) (ell := ell) (e := e) hρ hr hR hΛ (le_refl (0 : ℝ)) (by simp)

-- The algebraic coefficient is attained when the radius bounds coincide and Lambda vanishes.
example (e : ℝ) : renormalizedMass 1 (-1) (-1) 0 e 0 = 5 / 2 + e ^ 2 / 2 := by
  have hb := renormalizedMass_le_of_optical (r := 1) (ν := -1) (l := -1) (ell := 0)
    (e := e) (Λ := 0) (ρ := 1) (R := 1) (Q := 1)
    (by norm_num) le_rfl le_rfl le_rfl (by norm_num) (by norm_num)
  apply le_antisymm
  · nlinarith only [hb]
  · norm_num [renormalizedMass]
    linarith

section ModeInner

-- All three estimates share one constant and use the manuscript's radius variable.
example (B : Background) (hb : B.criticalExponent < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo B.inner B.event,
      |B.transmission hb - extendCurve B.radialLength_pos.le (B.radialMode hb).1
        (B.event - r)| ≤ C * (r - B.inner) ^ (1 / 2 : ℝ) ∧
      |B.criticalWeight r * extendCurve B.radialLength_pos.le (B.radialMode hb).2
        (B.event - r)| ≤ C * (r - B.inner) ^ (-1 / 2 : ℝ) ∧
      |(-B.F r) * (B.criticalWeight r *
        extendCurve B.radialLength_pos.le (B.radialMode hb).2 (B.event - r))| ≤
        C * (r - B.inner) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := B.radialMode_inner_remainders hb
  refine ⟨C, hC, ?_⟩
  intro r hr
  have hx : B.event - r ∈ Icc 0 B.radialLength := by
    dsimp [Background.radialLength]
    constructor <;> linarith [hr.1, hr.2]
  have hd : B.radialLength - (B.event - r) = r - B.inner := by
    dsimp [Background.radialLength]
    ring
  simpa only [extendCurve, projIcc_of_mem _ hx, sub_sub_cancel, hd] using hbound ⟨_, hx⟩

-- The actual charged de Sitter example also satisfies the quantitative terminal estimate.
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Icc 0 sampleBackground.radialLength,
    |sampleBackground.transmission (by rw [sample_critical_exponent]; norm_num) -
      (sampleBackground.radialMode (by rw [sample_critical_exponent]; norm_num)).1 x| ≤
      C * (sampleBackground.radialLength - x) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := sampleBackground.radialMode_inner_remainders
    (by rw [sample_critical_exponent]; norm_num)
  exact ⟨C, hC, fun x => (hbound x).1⟩

-- The inward derivative retains the positive blue-shift coefficient k/(-F0).
example (B : Background) (hb : B.criticalExponent < 1) {x : ℝ}
    (hx : x ∈ Ioo 0 B.radialLength) :
    deriv (fun t => B.criticalWeight (B.event - t) *
      extendCurve B.radialLength_pos.le (B.radialMode hb).2 t) x =
      B.innerRate / (-B.F (B.event - x)) *
        (B.criticalWeight (B.event - x) *
          extendCurve B.radialLength_pos.le (B.radialMode hb).2 x) +
        1 / (B.outerRate * (B.event - x)) *
          extendCurve B.radialLength_pos.le (B.radialMode hb).1 x :=
  (B.radialMode_W_hasDerivAt hb hx).2.deriv

end ModeInner

section ModeOuter

-- The power integral also treats a singular, integrable starting endpoint.
example : (fun x => ∫ t in (0 : ℝ)..x, t ^ (-1 / 2 : ℝ)) =O[𝓝[>] 0]
    (fun x => x ^ (1 / 2 : ℝ)) := by
  have hh := integral_isBigO_rpow (by norm_num : (-1 : ℝ) < -1 / 2)
    (Asymptotics.isBigO_refl (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (𝓝[>] 0))
  norm_num only at hh
  simpa only [neg_div] using hh

-- The two additive remainders give exactly the paper's relative O(x) errors.
example (B : Background) (hb : B.criticalExponent < 1) :
    (fun x => extendCurve B.radialLength_pos.le (B.radialMode hb).1 x /
      (B.innerRate / (B.criticalExponent + 1) * x ^ (B.criticalExponent + 1)) - 1)
      =O[𝓝[>] 0] (fun x => x) ∧
    (fun x => (B.criticalWeight (B.event - x) *
      extendCurve B.radialLength_pos.le (B.radialMode hb).2 x) /
      (B.event * B.criticalExponent * x ^ B.criticalExponent) - 1)
      =O[𝓝[>] 0] (fun x => x) := by
  have normalize (f : ℝ → ℝ) (c s : ℝ) (hc : c ≠ 0)
      (h : (fun x => f x - c * x ^ s) =O[𝓝[>] 0] (fun x => x ^ (s + 1))) :
      (fun x => f x / (c * x ^ s) - 1) =O[𝓝[>] 0] (fun x => x) := by
    have hh : (fun x => f x / (c * x ^ s) - 1) =O[𝓝[>] 0] (fun x => c⁻¹ * x) := by
      apply (h.mul (Asymptotics.isBigO_refl (fun x : ℝ => (c * x ^ s)⁻¹) (𝓝[>] 0))).congr'
      · filter_upwards [self_mem_nhdsWithin] with x hx
        have hp := (Real.rpow_pos_of_pos hx s).ne'
        field_simp
      · filter_upwards [self_mem_nhdsWithin] with x hx
        have hp := (Real.rpow_pos_of_pos hx s).ne'
        rw [Real.rpow_add hx, Real.rpow_one]
        field_simp
    exact hh.of_const_mul_right
  have hh := B.radialMode_outer_expansions hb
  refine ⟨normalize _ _ _ (div_ne_zero B.innerRate_pos.ne' ?_)
    (by simpa only [show B.criticalExponent + 1 + 1 = B.criticalExponent + 2 by ring] using hh.2.1),
    normalize _ _ _ (mul_ne_zero B.event_pos.ne' B.criticalExponent_pos.ne') hh.2.2⟩
  linarith [B.criticalExponent_pos]

-- The actual sample has b=31/40 and the W leading coefficient r+*b=93/100.
example : (fun x => sampleBackground.criticalWeight (sampleBackground.event - x) *
    extendCurve sampleBackground.radialLength_pos.le
      (sampleBackground.radialMode (by rw [sample_critical_exponent]; norm_num)).2 x -
    (93 / 100 : ℝ) * x ^ (31 / 40 : ℝ)) =O[𝓝[>] 0] (fun x => x ^ (71 / 40 : ℝ)) := by
  have hh := (sampleBackground.radialMode_outer_expansions
    (by rw [sample_critical_exponent]; norm_num)).2.2
  apply hh.congr
  · intro x
    congr 1
    norm_num only [sample_critical_exponent, show sampleBackground.event = 6 / 5 by rfl]
  · intro x
    congr 1
    rw [sample_critical_exponent]
    norm_num

end ModeOuter

section BackgroundNormalization

-- The general F' formula retains both horizon rates and the inner factor of two.
example (B : Background) :
    horizonK B.inner B.mass B.charge B.cosmological = -B.innerRate ∧
    horizonK B.event B.mass B.charge B.cosmological = B.outerRate / 2 := by
  have hi := (B.F_hasDerivAt B.inner_pos.ne').unique B.hasDerivAt_F_inner
  have ho := (B.F_hasDerivAt B.event_pos.ne').unique B.hasDerivAt_F_event
  constructor <;> linarith

variable (B : Background) {U V : ℝ} {h r : ℝ → ℝ}
  (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
  (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
  (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
  (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  {f : ℝ → ℝ} (hf : MemLp f 4 (volume.restrict (Icc 0 U))) {x : WaveState U V}
  (hx : IsWaveIntegral hU hV B.charge B.cosmological
    (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
    (incomingWaveVelocity hUR le_rfl hf) x)

include hφ hrd hx

-- The actual p=4 solution supplies the nonzero transverse derivative, even at a time boundary.
example (u : Icc 0 U) (hu : 0 < (u : ℝ)) (v : Icc 0 V)
    (hband : x.1 u v 0 ∈ Ioo B.inner B.event) :
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
    let κ := -Real.exp (x.1 u v 2) / (4 * ν u v)
    HasDerivWithinAt (fun t => Real.log (B.z (intervalExtension hV (x.1 u) t 0)) - B.outerRate * t)
      (B.outerRate * (κ - 1) -
        2 * B.outerRate * κ * (m u v - B.mass) / (x.1 u v 0 * B.F (x.1 u v 0)))
      (Icc 0 V) v :=
  (hx.background_normalization_derivative B hx.choose u hu v
    (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf u v).2.2.1.ne hband).2

-- Zero geometric error gives exact transport on closed segments, including a=b.
example {Y Z : ℝ} (hY : B.inner < Y) (hZ : Z < B.event)
    (u : Icc 0 U) (hu : 0 < (u : ℝ)) (a b : Icc 0 V) (hab : a ≤ b)
    (hband : ∀ v ∈ Icc a b, x.1 u v 0 ∈ Icc Y Z) :
    let ν := radialNuField hV B.charge B.cosmological
      (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    let m := massField B.charge B.cosmological x.1 x.2.1 ν hx.choose
    (∀ v ∈ Icc a b, m u v = B.mass ∧ -Real.exp (x.1 u v 2) / (4 * ν u v) = 1) →
      |Real.log ((u : ℝ) * ν u b / B.F (x.1 u b 0)) -
        Real.log ((u : ℝ) * ν u a / B.F (x.1 u a 0))| +
      |Real.log (B.z (x.1 u b 0)) - Real.log (B.z (x.1 u a 0)) - B.outerRate * ((b : ℝ) - a)| = 0 := by
  dsimp only
  intro herr
  obtain ⟨C, _, hC⟩ := B.exists_band_normalization_control hY hZ
  have hb := hC hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf hx u hu a b hab hband
  dsimp only at hb
  have hzero : (∫ t in (a : ℝ)..b,
      |intervalExtension hV ((massField B.charge B.cosmological x.1 x.2.1
        (radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose) hx.choose) u) t - B.mass| +
      |-Real.exp (intervalExtension hV (x.1 u) t 2) /
        (4 * intervalExtension hV ((radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose) u) t) - 1|) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply ae_of_all
    intro t ht
    rw [uIoc_of_le (show (a : ℝ) ≤ b from hab)] at ht
    have htV : t ∈ Icc 0 V := ⟨a.property.1.trans ht.1.le, ht.2.trans b.property.2⟩
    have hh := herr ⟨t, htV⟩ ⟨ht.1.le, ht.2⟩
    simp only [intervalExtension_apply, projIcc_of_mem hV htV, hh.1, hh.2,
      sub_self, abs_zero, zero_add]
  rw [hzero, mul_zero] at hb
  exact le_antisymm hb (add_nonneg (abs_nonneg _) (abs_nonneg _))

end BackgroundNormalization

section OuterNormalization

variable {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
  (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
  {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
  (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)

-- Exact nu normalization integrates to the exact gap, including at the right endpoint.
example {S : ℝ} (hS : 0 < S) (v : Icc 0 V)
    (hν : ∀ q : Icc 0 U, -radialNuField hV e Λ zIn x.1 hr q v = S)
    (u : Icc 0 U) (hu : 0 < (u : ℝ)) :
    x.1 ⟨0, le_rfl, hU⟩ v 0 - x.1 u v 0 = (u : ℝ) * S := by
  have hb := hx.radial_gap_relative_bound hr hzin hinu hS v
    (ε := 0) (fun q => by simp only [hν q, div_self hS.ne', sub_self, abs_zero, le_refl]) u hu
  have he := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))
  simpa only [one_mul] using (div_eq_iff (mul_ne_zero hu.ne' hS.ne')).1 he

-- Reference conversion retains the correct signs and introduces no error when both tails vanish.
example {cν a rplus : ℝ} (hcν : 0 < cν) (v : Icc 0 V)
    (hν : ∀ q : Icc 0 U,
      -radialNuField hV e Λ zIn x.1 hr q v = cν * Real.exp (a * v))
    (htrace : x.1 ⟨0, le_rfl, hU⟩ v 0 = rplus)
    (u : Icc 0 U) (hu : 0 < (u : ℝ)) :
    (-radialNuField hV e Λ zIn x.1 hr u v) / (cν * Real.exp (a * v)) = 1 ∧
      (rplus - x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (a * v))) = 1 := by
  have hT : 0 < cν * Real.exp (a * v) := mul_pos hcν (Real.exp_pos _)
  have hb := hx.radial_outer_reference_bound hr hzin hinu hT hcν v
    (ε := 0) (η := 0) (a := a) (rplus := rplus)
    (fun q => by simp only [hν q, div_self hT.ne', sub_self, abs_zero, le_refl])
    (by simp only [div_self hT.ne', sub_self, abs_zero, le_refl]) u hu
  simp only [htrace, sub_self, abs_zero, zero_div, zero_mul, add_zero] at hb
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb.1 (abs_nonneg _))),
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb.2 (abs_nonneg _)))⟩

end OuterNormalization

section OuterNormalizationInfinity

-- The closed estimate specializes to L-infinity with the error C*(U+sigma), uniformly in time.
example {M e Λ a c ρ R nH NH H W A : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    (ha : 0 < a) (hc0 : 0 ≤ c) (hac : c < a) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (c * t) * |h t| ≤ H)
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass M h t) e Λ| ≤ W) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ C ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f ∞ (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (_hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
          (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x),
        (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ≤ A → U * Real.exp (a * V) ≤ δ →
        ∀ (u : Icc 0 U), 0 < (u : ℝ) → ∀ v : Icc 0 V,
          let S := -horizonNu (fun w => horizonK (r w) (horizonMass M h w) e Λ) v
          let σ := U * Real.exp (a * V)
          |(r v - x.1 u v 0) / ((u : ℝ) * S) - 1| ≤
            (1 + C * σ) * Real.exp (C * (U + σ)) - (1 - U / r 0) * Real.exp (-(C * (U + σ))) ∧
          |Real.exp (x.1 u v 2) / (4 * S) - 1| ≤
            (1 + C * σ) * Real.exp (C * (U + σ)) - (1 - U / r 0) * Real.exp (-(C * (U + σ))) +
              (1 - Real.exp (-(C * (U + σ)))) := by
  obtain ⟨δ, C, hδ, hδ1, hC, hb⟩ := exists_horizon_outer_normalization
    hc hi hrc hr0 hφ hrd ha hc0 hac hρ hnH hNH hH hW hA haxis hνaxis hout hlout
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro U V hU hV hUR f hf x hx hfn hwidth u hu v
  have hh := (hb U V hU hV hUR ∞ le_top f hf x hx hfn
    (by simpa only [ENNReal.toReal_top, div_zero, sub_zero, mul_one] using hac.le) hwidth)
  constructor
  · simpa only [ENNReal.toReal_top, div_zero, sub_zero, Real.rpow_one] using hh.2.1 u hu v
  · simpa only [ENNReal.toReal_top, div_zero, sub_zero, Real.rpow_one] using hh.2.2 u v

end OuterNormalizationInfinity

section MidpointNormalization

-- The original critical hypotheses supply the strict horizon-tail decay needed at half arrival time.
example (B : Background) {p : ℝ≥0∞} (hp : 4 ≤ p) {s : ℝ}
    (hcrit : B.criticalExponent = 1 - 1 / p.toReal) (hs : B.innerRate < s) :
    B.outerRate < 2 * s := by
  have hb : (3 / 4 : ℝ) ≤ B.innerRate / B.outerRate := by
    change (3 / 4 : ℝ) ≤ B.criticalExponent
    rw [hcrit]
    exact (incoming_exponent_bounds hp).1
  have hk := (le_div_iff₀ B.outerRate_pos).1 hb
  nlinarith only [hk, hs, B.outerRate_pos]

variable (B : Background) {s H dH A j D : ℝ}
  (hs : 0 < s) (hsa : B.outerRate < 2 * s) (hH : 0 ≤ H)
  (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hj : 0 < j) (hD : 0 < D)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

include hs hsa hH hdH hdHR hA hj hD hc hb hrc hrb hrd hrdec hOut

-- At p=4, the actual arriving ray is normalized at half its arrival time, inside any larger rectangle.
example {ε : ℝ} (hε : 0 < ε) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
      (hx : IsWaveIntegral hU hV B.charge B.cosmological
        (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR le_rfl hf) x),
      (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
      ∀ (u : Icc 0 U) (t : ℝ) (ht : 0 ≤ t) (htV : t ≤ V), T ≤ t →
        j ≤ (u : ℝ) * Real.exp (B.outerRate * t) → (u : ℝ) * Real.exp (B.outerRate * t) ≤ D →
        let v : Icc 0 V := ⟨t / 2, (by positivity), (half_le_self ht).trans htV⟩
        let ν := radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
        |(-ν u v) / (cν * Real.exp (B.outerRate * (t / 2))) - 1| < ε ∧
          |(B.event - x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (B.outerRate * (t / 2)))) - 1| < ε := by
  obtain ⟨T, hT, hnorm⟩ := B.exists_midpoint_normalization hs hsa hH hdH hdHR hA hj hD
    hc hb hrc hrb hrd hrdec hOut ε hε
  refine ⟨2 * T, by positivity, ?_⟩
  intro U V hU hV hUR f hf x hx hfn u t ht htV htt hjt hDt
  let v : Icc 0 V := ⟨t / 2, by positivity, (half_le_self ht).trans htV⟩
  have heq : 2 * B.outerRate * (t / 2) = B.outerRate * t := by ring
  exact hnorm U V hU hV hUR 4 le_rfl f hf x hx hfn u v
    (by dsimp only [v]; linarith only [htt])
    (by simpa only [v, heq] using hjt) (by simpa only [v, heq] using hDt)

-- The infinity endpoint also places the actual intermediate point strictly below the event radius.
example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (f : ℝ → ℝ) (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
      (_hx : IsWaveIntegral hU hV B.charge B.cosmological
        (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR le_top hf) x),
      (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ≤ A →
      ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
        j ≤ (u : ℝ) * Real.exp (2 * B.outerRate * v) →
        (u : ℝ) * Real.exp (2 * B.outerRate * v) ≤ D → x.1 u v 0 < B.event := by
  obtain ⟨T, hT, hnorm⟩ := B.exists_midpoint_normalization hs hsa hH hdH hdHR hA hj hD
    hc hb hrc hrb hrd hrdec hOut (1 / 2) (by norm_num)
  refine ⟨T, hT, ?_⟩
  intro U V hU hV hUR f hf x hx hfn u v ht hjv hDv
  have hh := (hnorm U V hU hV hUR ∞ le_top f hf x hx hfn u v ht hjv hDv).2
  have hu : 0 < (u : ℝ) := (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 (hj.trans_le hjv)
  have hratio := (abs_lt.1 hh).1
  have hpos : 0 < (B.event - x.1 u v 0) /
      ((u : ℝ) * (Real.exp (∫ t in Ioi 0,
        2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate) *
          Real.exp (B.outerRate * v))) := by linarith only [hratio]
  exact sub_pos.1 ((div_pos_iff_of_pos_right (by positivity)).1 hpos)

end MidpointNormalization

section OuterSectionNormalization

-- The background conversion has the correct sign and coefficient for an exactly normalized gap.
example (B : Background) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ u S : ℝ, 0 < u → 0 < S → u * S < η →
      |u * (-S) / B.F (B.event - u * S) - 1 / B.outerRate| < ε ∧
        |B.z (B.event - u * S) / (u * S) - 1| < ε := by
  obtain ⟨η, hη, _, _, hb⟩ := B.exists_outer_normalization_tolerance hε
  refine ⟨η, hη, ?_⟩
  intro u S hu hS hus
  apply (hb (B.event - u * S) u (-S) S hu hS ?_ ?_ ?_).2
  · simpa only [sub_sub_cancel_left, abs_neg, abs_of_pos (mul_pos hu hS)] using hus
  · simpa only [neg_neg, div_self hS.ne', sub_self, abs_zero] using hη
  · simpa only [sub_sub_cancel, div_self (mul_pos hu hS).ne', sub_self, abs_zero] using hη

variable (B : Background) {s H dH A : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

include hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut

-- The actual p=4 coefficient estimates also guarantee the denominator's negative sign.
example {cap ε : ℝ} (hcap : 0 < cap) (hε : 0 < ε) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ T : ℝ, 0 < δ ∧ δ < cap ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
        ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
          δ / 2 ≤ (u : ℝ) * Real.exp (B.outerRate * v) → (u : ℝ) * Real.exp (B.outerRate * v) ≤ δ →
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
          B.F (x.1 u v 0) < 0 ∧ |(u : ℝ) * ν u v / B.F (x.1 u v 0) - 1 / B.outerRate| < ε ∧
            |B.z (x.1 u v 0) / ((u : ℝ) * (cν * Real.exp (B.outerRate * v))) - 1| < ε := by
  obtain ⟨δ, T, hδ, hcap', hT, hδr, hnorm⟩ := B.exists_outer_section_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut cap ε hcap hε
  refine ⟨δ, T, hδ, hcap', hT, ?_⟩
  intro U V hU hV hUR f hf x hx hfn u v ht hlo hhi
  have hh := hnorm U V hU hV hUR 4 le_rfl f hf x hx hfn u v ht hlo hhi
  refine ⟨B.F_neg ⟨by linarith only [hh.1.2, hδr], ?_⟩, hh.2⟩
  have hp : 0 < Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate) * δ / 4 := by positivity
  linarith only [hh.1.1, hp]

-- At p=infinity the same cutoff can be placed above any fixed radius below the event horizon.
example {Y : ℝ} (hY : Y < B.event) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ T : ℝ, 0 < δ ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (_hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_top hf) x),
        (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ≤ A →
        ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
          δ / 2 ≤ (u : ℝ) * Real.exp (B.outerRate * v) → (u : ℝ) * Real.exp (B.outerRate * v) ≤ δ →
          x.1 u v 0 ∈ Ioo Y B.event := by
  let cν := Real.exp (∫ t in Ioi 0,
    2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
  have hcν : 0 < cν := Real.exp_pos _
  let cap := (B.event - Y) / (4 * cν)
  have hcap : 0 < cap := div_pos (sub_pos.2 hY) (by positivity)
  obtain ⟨δ, T, hδ, hδcap, hT, _, hnorm⟩ := B.exists_outer_section_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut cap 1 hcap zero_lt_one
  have hδY := (lt_div_iff₀ (by positivity : 0 < 4 * cν)).1 hδcap
  refine ⟨δ, T, hδ, hT, ?_⟩
  intro U V hU hV hUR f hf x hx hfn u v ht hlo hhi
  have hh := (hnorm U V hU hV hUR ∞ le_top f hf x hx hfn u v ht hlo hhi).1
  change cν * δ / 4 < B.event - x.1 u v 0 ∧ B.event - x.1 u v 0 < 2 * cν * δ at hh
  have hp := mul_pos hcν hδ
  constructor <;> nlinarith only [hh.1, hh.2, hδY, hp]

end OuterSectionNormalization

section PrearrivalNormalization

-- Logarithmic errors control both sides of each positive normalized ratio.
example {x ε : ℝ} (hx : 0 < x) (h : |Real.log x| < ε) :
    Real.exp (-ε) < x ∧ x < Real.exp ε := by
  constructor
  · simpa only [Real.exp_log hx] using Real.exp_lt_exp.2 (abs_lt.1 h).1
  · simpa only [Real.exp_log hx] using Real.exp_lt_exp.2 (abs_lt.1 h).2

variable (B : Background) {s H dH A : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

include hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut

-- At p=4 the actual Jacobian is normalized without an assumed trapped upper radius or mass bound.
example {Y j D ε : ℝ} (hY : B.inner < Y) (hYe : Y < B.event)
    (hj : 0 < j) (hD : 0 < D) (hε : 0 < ε) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
      (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
      (hx : IsWaveIntegral hU hV B.charge B.cosmological
        (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
        (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
        (incomingWaveVelocity hUR le_rfl hf) x),
      (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
      ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
        j ≤ (u : ℝ) * Real.exp (B.outerRate * v) → (u : ℝ) * Real.exp (B.outerRate * v) ≤ D →
        (∀ q ≤ u, ∀ t ≤ v, Y ≤ x.1 q t 0) →
        let ν := radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
        B.F (x.1 u v 0) < 0 ∧
          |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F (x.1 u v 0)))| < ε := by
  obtain ⟨T, hT, hnorm⟩ := B.exists_prearrival_normalization
    hs hH hdH hdHR hA hY hYe hj hD hc hb hrc hrb hrd hrdec hOut ε hε
  refine ⟨T, hT, ?_⟩
  intro U V hU hV hUR f hf x hx hfn u v ht hjv hDv hfloor
  have hh := hnorm U V hU hV hUR 4 le_rfl f hf x hx hfn u v ht hjv hDv hfloor
  exact ⟨B.F_neg hh.1, (le_add_of_nonneg_right (abs_nonneg _)).trans_lt hh.2⟩

-- The infinity endpoint has one constructed radius curve for every tolerance and every physical rectangle.
example (hrinit : B.inner < r 0) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ U₀ T : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ,
        0 < U₀ ∧ 0 < T ∧ (∀ ε, T ≤ τ ε) ∧
        ∀ f : ℝ → ℝ, MemLp f ∞ (volume.restrict (Icc 0 δ)) →
          (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (_hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_top hfU) x),
                ∀ t ∈ Icc T V, g t ≤ U →
                  x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 = Y ∧
                  ∀ ε : Ioi (0 : ℝ), τ ε ≤ t →
                    |Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t))))| < ε := by
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hnorm⟩ := B.exists_band_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨U₀, T, τ, hU₀, _hUδ, hT, hτ, hcurve⟩ := hnorm Y hY hYR
  refine ⟨U₀, T, τ, hU₀, hT, hτ, ?_⟩
  intro f hf hfn
  obtain ⟨g, _hgc, _hga, hgl, _hgdc, _hgp, hphysical⟩ := hcurve ∞ le_top f hf hfn
  refine ⟨g, hgl, ?_⟩
  intro U V hU hV hUR hUU hfU x hx t ht hgtU
  have hh := hphysical U V hU hV hUR hUU hfU x hx t ht hgtU
  exact ⟨hh.1, fun ε hε => (le_add_of_nonneg_left (abs_nonneg _)).trans_lt (hh.2 ε hε)⟩

end PrearrivalNormalization


section ArrivalPhase

-- The nominal lapse and mass reduce the speed formula to a/n.
example (B : Background) (Y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℝ, 0 < n → |Real.log n| < η →
      |B.outerRate / n - B.outerRate| < ε := by
  obtain ⟨η, hη, hb⟩ := B.exists_arrival_speed_tolerance Y hε
  refine ⟨η, hη, ?_⟩
  intro n hn hlog
  simpa only [sub_self, mul_zero, zero_div, sub_zero, mul_one] using
    hb n 1 B.mass hn hlog (by simpa only [sub_self, abs_zero, zero_add] using hη)

variable (B : Background) {s H dH A : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

include hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut

-- Actual p=4 arrival curves give a whole-half-line L2 pullback, uniformly before profiles and phase shifts.
example :
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ T : ℝ, 0 < T ∧
        ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
          (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
            ∀ (ℓ : ℝ) (F : ℝ → ℝ), Continuous F → Integrable (fun t => F t ^ 2) →
              MemLp (fun t => F (ℓ - Real.log (g t))) 2 (volume.restrict (Ici T)) ∧
                (∫ t in Ici T, F (ℓ - Real.log (g t)) ^ 2) ≤
                  (2 / B.outerRate) * ∫ t, F t ^ 2 := by
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hnorm⟩ := B.exists_arrival_phase_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨T, τ, hT, hτ, hsolve⟩ := hnorm Y hY hYR
  let ε : Ioi (0 : ℝ) := ⟨B.outerRate / 2, half_pos B.outerRate_pos⟩
  refine ⟨τ ε, hT.trans_le (hτ ε), ?_⟩
  intro f hf hfn
  obtain ⟨g, hgc, _hga, hgl, hpoint⟩ := hsolve 4 le_rfl f hf hfn
  refine ⟨g, hgl, ?_⟩
  intro ℓ F hFc hFi
  have hsub : Ici (τ ε) ⊆ Ici T := fun _ ht => (hτ ε).trans ht
  have hgp (t : ℝ) (ht : t ∈ Ici (τ ε)) : 0 < g t := (hpoint t (hsub ht)).1.1
  have hd (t : ℝ) (ht : t ∈ Ici (τ ε)) :
      HasDerivAt (fun w => ℓ - Real.log (g w)) (-deriv g t / g t) t := by
    simpa only [neg_div] using
      (((hpoint t (hsub ht)).2.1.hasDerivAt.log (hgp t ht).ne').const_sub ℓ)
  have hspeed (t : ℝ) (ht : t ∈ Ici (τ ε)) : B.outerRate / 2 ≤ -deriv g t / g t := by
    have hh := (hpoint t (hsub ht)).2.2.2.1 ε ht
    have he := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt hh
    have hlo := (abs_lt.1 he).1
    change -(B.outerRate / 2) < -deriv g t / g t - B.outerRate at hlo
    linarith only [hlo]
  have hh := timeChange_l2_halfline (half_pos B.outerRate_pos)
    (continuousOn_const.sub ((hgc.mono hsub).log (fun t ht => (hgp t ht).ne')))
    hd hspeed hFc hFi
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  field_simp

-- The infinity endpoint has uniform phase and speed normalization and the exact Jacobian in any larger physical rectangle.
example {ε : ℝ} (hε : 0 < ε) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y : ℝ, B.inner < Y → Y ≤ R → ∃ T : ℝ, 0 < T ∧
        ∀ f : ℝ → ℝ, MemLp f ∞ (volume.restrict (Icc 0 δ)) →
          (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ∀ t ∈ Ici T,
            |Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t))))| +
              |-deriv g t / g t - B.outerRate| < ε ∧
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
              (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
              (hx : IsWaveIntegral hU hV B.charge B.cosmological
                (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0))
                (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                (incomingWaveVelocity hUR le_top hfU) x), g t ≤ U → t ≤ V →
                let u := projIcc 0 U hU (g t)
                let v := projIcc 0 V hV t
                let ν := radialNuField hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0)) x.1 hx.choose
                x.1 u v 0 = Y ∧ HasDerivAt g (-x.2.1 u v 0 / ν u v) t ∧
                  |Real.log (B.outerRate * (g t * ν u v / B.F Y))| < ε := by
  obtain ⟨δ, R, hδ, _hδr, hR, _hRr, hnorm⟩ := B.exists_arrival_phase_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y hY hYR
  obtain ⟨T, τ, hT, hτ, hsolve⟩ := hnorm Y hY hYR
  let e : Ioi (0 : ℝ) := ⟨ε, hε⟩
  refine ⟨τ e, hT.trans_le (hτ e), ?_⟩
  intro f hf hfn
  obtain ⟨g, _hgc, _hga, _hgl, hpoint⟩ := hsolve ∞ le_top f hf hfn
  refine ⟨g, ?_⟩
  intro t ht
  have hh := hpoint t ((hτ e).trans ht)
  refine ⟨hh.2.2.2.1 e ht, ?_⟩
  intro U V hU hV hUR hfU x hx hgtU htV
  have hm := hh.2.2.2.2 U V hU hV hUR hfU x hx hgtU htV
  exact ⟨hm.1, hm.2.1, hm.2.2 e ht⟩

end ArrivalPhase



section RadiusTimeMap

-- Exact exponential arrival curves give the forward shift, fixing the map's orientation.
example : ∃ S : ℝ, 0 ≤ S ∧ ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Ici S) ∧
    ∀ t ∈ Ici S, ψ t = t + 1 := by
  let g := fun t : ℝ => Real.exp (1 - t)
  let h := fun t : ℝ => Real.exp (-t)
  have hgd (t : ℝ) : HasDerivAt g (-Real.exp (1 - t)) t := by
    simpa only [g, id_eq, zero_sub, mul_neg_one] using ((hasDerivAt_id t).const_sub 1).exp
  have hhd (t : ℝ) : HasDerivAt h (-Real.exp (-t)) t := by
    simpa only [h, Pi.neg_apply, id_eq, mul_neg_one] using (hasDerivAt_id t).neg.exp
  have hgc : ContinuousOn g (Ici 0) := by fun_prop
  have hhc : ContinuousOn h (Ici 0) := by fun_prop
  have hga : StrictAntiOn g (Ici 0) := by
    intro t _ w _ htw
    apply Real.exp_lt_exp.2
    linarith only [htw]
  have hgl : Tendsto g atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (Real.exp 1)
    convert hh using 1
    · ext t
      change Real.exp (1 - t) = Real.exp 1 * Real.exp (-t)
      rw [← Real.exp_add]
      rfl
    · simp only [mul_zero]
  have hge (t : ℝ) : 1 - Real.log (g t) - 1 * t = 0 := by dsimp only [g]; rw [Real.log_exp]; ring
  have hhe (t : ℝ) : 0 - Real.log (h t) - 1 * t = 0 := by dsimp only [h]; rw [Real.log_exp]; ring
  have hgs (t : ℝ) : -deriv g t / g t - 1 = 0 := by rw [(hgd t).deriv]; simp only [g, neg_neg, div_self (Real.exp_ne_zero _), sub_self]
  have hhs (t : ℝ) : -deriv h t / h t - 1 = 0 := by rw [(hhd t).deriv]; simp only [h, neg_neg, div_self (Real.exp_ne_zero _), sub_self]
  obtain ⟨S, σ, hS, _hσ, hmap⟩ := exists_normalized_arrival_time_map
    (a := 1) (T := 0) (d₁ := 1) (d₂ := 0) zero_lt_one (fun _ => 0) (fun _ => le_rfl)
  obtain ⟨ψ, hψc, hpoint, _herr⟩ := hmap g h hgc hga hgl hhc
    (fun t _ => ⟨Real.exp_pos _, (hgd t).differentiableAt, Real.exp_pos _, (hhd t).differentiableAt⟩) (by
      intro ε t _
      constructor <;> simpa only [hge, hhe, hgs, hhs, abs_zero, zero_add] using
        (show 0 < (ε : ℝ) from ε.property))
  refine ⟨S, hS, ψ, hψc, ?_⟩
  intro t ht
  have hh : 1 - ψ t = -t := Real.exp_injective (hpoint t ht).2.1
  linarith only [hh]

variable (B : Background) {s H dH A : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

include hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut

-- At p=4, the actual radius-to-radius map has a half-line L2 pullback with a common constant.
example :
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Z ≤ R → ∃ T : ℝ, 0 < T ∧
        ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
          (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ ψ : ℝ → ℝ, (∀ t ∈ Ici T, t < ψ t) ∧
            ∀ F : ℝ → ℝ, Continuous F → Integrable (fun t => F t ^ 2) →
              MemLp (fun t => F (ψ t)) 2 (volume.restrict (Ici T)) ∧
                (∫ t in Ici T, F (ψ t) ^ 2) ≤ 2 * ∫ t, F t ^ 2 := by
  obtain ⟨δ, R, hδ, _hδr, hR, hmaps⟩ := B.exists_radius_time_map
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hZR
  obtain ⟨T, τ, hT, hτ, hsolve⟩ := hmaps Y Z hY hYZ hZR
  let ε : Ioi (0 : ℝ) := ⟨1 / 2, by norm_num⟩
  refine ⟨τ ε, hT.trans_le (hτ ε), ?_⟩
  intro f hf hfn
  obtain ⟨_gY, _gZ, ψ, hψc, hpoint, herr, _hphysical⟩ := hsolve 4 le_rfl f hf hfn
  have hsub : Ici (τ ε) ⊆ Ici T := fun _ ht => (hτ ε).trans ht
  refine ⟨ψ, fun t ht => (hpoint t (hsub ht)).1, ?_⟩
  intro F hFc hFi
  have hspeed (t : ℝ) (ht : t ∈ Ici (τ ε)) : (1 / 2 : ℝ) ≤ deriv ψ t := by
    have hh := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt (herr ε t ht)
    have hlo := (abs_lt.1 hh).1
    change -(1 / 2 : ℝ) < deriv ψ t - 1 at hlo
    linarith only [hlo]
  have hh := timeChange_l2_halfline (by norm_num : 0 < (1 / 2 : ℝ)) (hψc.mono hsub)
    (fun t ht => (hpoint t (hsub ht)).2.2.2.1.hasDerivAt) hspeed hFc hFi
  exact ⟨hh.1, hh.2.trans_eq (by ring)⟩

-- At p=infinity, both physical endpoints lie on the same ray, including rectangle boundaries.
example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Z ≤ R → ∃ T : ℝ, 0 < T ∧
        ∀ f : ℝ → ℝ, MemLp f ∞ (volume.restrict (Icc 0 δ)) →
          (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g ψ : ℝ → ℝ, ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
            (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
            (_hx : IsWaveIntegral hU hV B.charge B.cosmological
              (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0))
              (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
              (incomingWaveVelocity hUR le_top hfU) x),
            ∀ t ∈ Ici T, g t ≤ U → ψ t ≤ V →
              t < ψ t ∧
                x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 = Z ∧
                x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV (ψ t)) 0 = Y := by
  obtain ⟨δ, R, hδ, _hδr, hR, hmaps⟩ := B.exists_radius_time_map
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hZR
  obtain ⟨T, _τ, hT, _hτ, hsolve⟩ := hmaps Y Z hY hYZ hZR
  refine ⟨T, hT, ?_⟩
  intro f hf hfn
  obtain ⟨_gY, gZ, ψ, _hψc, hpoint, _herr, hphysical⟩ := hsolve ∞ le_top f hf hfn
  refine ⟨gZ, ψ, ?_⟩
  intro U V hU hV hUR hfU x hx t ht hgt hψt
  have hh := hphysical U V hU hV hUR hfU x hx t ht hgt hψt
  exact ⟨(hpoint t ht).1, hh.1, hh.2.1⟩

end RadiusTimeMap


section CompactBandNormalization

variable (B : Background) {s H dH A : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

include hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut

-- Critical incoming data give a common late trapping time on the whole actual band.
example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Z ≤ R →
        ∃ U₀ T : ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧
          ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
            (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∃ gY gZ : ℝ → ℝ, Tendsto gY atTop (𝓝 0) ∧ Tendsto gZ atTop (𝓝 0) ∧
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
                ∀ (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                  (_hx : IsWaveIntegral hU hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR le_rfl hfU) x),
                  ∀ (u : Icc 0 U) (v : Icc 0 V), T ≤ (v : ℝ) →
                    gZ v ≤ (u : ℝ) → (u : ℝ) ≤ gY v → x.2.1 u v 0 < 0 := by
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ := B.exists_compact_band_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hZR
  obtain ⟨U₀, T, τ, _σ, hU₀, hUδ, hT, hτ, _hσ, hsolve⟩ := hband Y Z hY hYZ hZR
  let ε : Ioi (0 : ℝ) := ⟨B.outerRate / 2, half_pos B.outerRate_pos⟩
  refine ⟨U₀, τ ε, hU₀, hUδ, hT.trans_le (hτ ε), ?_⟩
  intro f hf hfn
  obtain ⟨gY, gZ, _hYc, _hYa, hYl, _hZc, _hZa, hZl, hpos, _hentry, hphysical⟩ := hsolve 4 le_rfl f hf hfn
  refine ⟨gY, gZ, hYl, hZl, ?_⟩
  intro U V hU hV hUR hUU hfU x hx u v hv hZu huY
  have hvT := (hτ ε).trans hv
  have hh := ((hphysical U V hU hV hUR hUU hfU x hx).2.2 u v hvT hZu huY).2 ε hv
  have hsp := (le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans_lt hh
  have hlo := (abs_lt.1 hsp).1
  let ν := radialNuField hV B.charge B.cosmological
    (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
  have hspeed : 0 < x.2.1 u v 0 / ((u : ℝ) * ν u v) := by
    change -(B.outerRate / 2) < x.2.1 u v 0 / ((u : ℝ) * ν u v) - B.outerRate at hlo
    linarith only [hlo, B.outerRate_pos]
  have hu : 0 < (u : ℝ) := (hpos v hvT).2.trans_le hZu
  have hφ := horizonPhi_integrable hs hH (sub_pos.2 hdHR) hc hrc hb hrb
  have hn : ν u v < 0 := (hx.interior_gauge hU hV hUR hc
    (horizon_mass_integrable hs hH hc hb) hrc
    (fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne') hφ hrd le_rfl hfU u v).2.2.1
  exact lt_of_not_ge (fun hnonneg => not_le_of_gt hspeed
    (div_nonpos_of_nonneg_of_nonpos hnonneg (mul_neg_of_pos_of_neg hu hn).le))

-- At p=infinity one cutoff, selected before the profile, gives every radius and its error.
example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Z ≤ R →
        ∃ U₀ : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧
          ∀ f : ℝ → ℝ, MemLp f ∞ (volume.restrict (Icc 0 δ)) →
            (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
                ∀ (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
                  (hx : IsWaveIntegral hU hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR le_top hfU) x),
                  ∀ (hUp : 0 < U) (ε : Ioi (0 : ℝ)) (v : Icc 0 V), τ ε ⟨U, hUp⟩ ≤ (v : ℝ) →
                    ∀ y ∈ Icc Y Z, ∃ u : Icc 0 U,
                      let ν := radialNuField hV B.charge B.cosmological
                        (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0)) x.1 hx.choose
                      x.1 u v 0 = y ∧
                        |Real.log (B.outerRate * ((u : ℝ) * ν u v / B.F y))| +
                          |Real.log (B.z y / ((u : ℝ) * (cν * Real.exp (B.outerRate * v))))| +
                            |x.2.1 u v 0 / ((u : ℝ) * ν u v) - B.outerRate| < ε := by
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ := B.exists_compact_band_normalization
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hZR
  obtain ⟨U₀, T, τ, σ, hU₀, hUδ, _hT, hτ, _hσ, hsolve⟩ := hband Y Z hY hYZ hZR
  refine ⟨U₀, fun ε W => max (τ ε) (σ W), hU₀, hUδ, ?_⟩
  intro f hf hfn
  obtain ⟨gY, gZ, _hYc, _hYa, _hYl, _hZc, _hZa, _hZl, _hpos, hentry, hphysical⟩ := hsolve ∞ le_top f hf hfn
  intro U V hU hV hUR hUU hfU x hx hUp ε v hv y hyz
  obtain ⟨hYv, hZv⟩ := hentry ⟨U, hUp⟩ v ((le_max_right _ _).trans hv)
  have hvε : τ ε ≤ (v : ℝ) := (le_max_left _ _).trans hv
  have hphys := hphysical U V hU hV hUR hUU hfU x hx
  have hvT := (hτ ε).trans hvε
  obtain ⟨u, hu, _hunique⟩ := hphys.2.1 v hvT hYv.le hZv.le y hyz
  have hh := (hphys.2.2 u v hvT hu.1 hu.2.1).2 ε hvε
  rw [hu.2.2] at hh
  exact ⟨u, hu.2.2, hh⟩

end CompactBandNormalization


section BandCoordinates

-- The two coordinate directions recover the reciprocal radial derivative and arrival speed.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ∈ Ioo 0 U) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hν : radialNuField hV e Λ zIn x.1 hr u v ≠ 0) :
    let ν := radialNuField hV e Λ zIn x.1 hr
    ∃ χ : ℝ × ℝ → ℝ, χ (x.1 u v 0, v) = u ∧
      HasStrictDerivAt (fun y => χ (y, v)) (ν u v)⁻¹ (x.1 u v 0) ∧
      HasStrictDerivAt (fun t => χ (x.1 u v 0, t)) (-x.2.1 u v 0 / ν u v) v := by
  obtain ⟨χ, hself, hd, _hnear⟩ := hx.exists_radial_coordinate_chart hr hzin hinu u v hu hv hν
  refine ⟨χ, hself, ?_, ?_⟩
  · have hh := hd.comp_hasStrictDerivAt (x.1 u v 0)
      ((hasStrictDerivAt_id (x.1 u v 0)).prodMk (hasStrictDerivAt_const (x.1 u v 0) (v : ℝ)))
    simpa only [Function.comp_def, id_eq, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, zero_mul, one_mul, sub_zero] using hh
  · have hh := hd.comp_hasStrictDerivAt (v : ℝ)
      ((hasStrictDerivAt_const (v : ℝ) (x.1 u v 0)).prodMk (hasStrictDerivAt_id (v : ℝ)))
    simpa only [Function.comp_def, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, zero_mul, one_mul, zero_sub, neg_div] using hh

variable (B : Background) {s H dH A : ℝ}
  (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
  {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
  (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
  (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
    (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
  (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
  (hOut : B.OutgoingEstimates h r s)

include hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut

-- At p=4 both partial derivatives hold on closed coordinate windows, including their endpoints.
example :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Z ≤ R →
        ∃ U₀ T : ℝ, ∃ σ : Ioi (0 : ℝ) → ℝ,
          0 < U₀ ∧ U₀ ≤ δ ∧ 0 < T ∧ (∀ W, T ≤ σ W) ∧
          ∀ f : ℝ → ℝ, MemLp f 4 (volume.restrict (Icc 0 δ)) →
            (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
              ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
                ∀ (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                  (hx : IsWaveIntegral hU hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR le_rfl hfU) x),
                  ∀ (hUp : 0 < U) (l S : ℝ), σ ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                    ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ (Icc Y Z ×ˢ Icc l S) ∧
                      ∀ q ∈ Icc Y Z ×ˢ Icc l S,
                        let u := projIcc 0 U hU (χ q)
                        let v := projIcc 0 V hV q.2
                        let ν := radialNuField hV B.charge B.cosmological
                          (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0)) x.1 hx.choose
                        χ q ∈ Ioo 0 U ∧ x.1 u v 0 = q.1 ∧
                          HasDerivWithinAt (fun y => χ (y, q.2)) (ν u v)⁻¹ (Icc Y Z) q.1 ∧
                          HasDerivWithinAt (fun t => χ (q.1, t)) (-x.2.1 u v 0 / ν u v) (Icc l S) q.2 := by
  obtain ⟨δ, R, hδ, _hδr, hR, hband⟩ := B.exists_band_coordinates
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hZR
  obtain ⟨U₀, T, _τ, σ, hU₀, hUδ, hT, _hτ, hσ, hsolve⟩ :=
    hband Y Z hY hYZ (hYZ.le.trans hZR) (hZR.trans_lt hR.2)
  refine ⟨U₀, T, σ, hU₀, hUδ, hT, hσ, ?_⟩
  intro f hf hfn U V hU hV hUR hUU hfU x hx hUp l S hσl hlS hSV
  obtain ⟨χ, hχc, _hJc, hpoint⟩ :=
    hsolve 4 le_rfl f hf hfn U V hU hV hUR hUU hfU x hx hUp l S hσl hlS hSV
  refine ⟨χ, hχc, ?_⟩
  intro q hq
  have hh := hpoint q hq
  refine ⟨hh.1, hh.2.1, ?_, ?_⟩
  · have hd := hh.2.2.1.comp_hasDerivWithinAt q.1
      ((hasDerivWithinAt_id q.1 (Icc Y Z)).prodMk (hasDerivWithinAt_const q.1 (Icc Y Z) q.2))
      (show MapsTo (fun y : ℝ => (y, q.2)) (Icc Y Z) (Icc Y Z ×ˢ Icc l S) from fun _ hy => ⟨hy, hq.2⟩)
    simpa only [Function.comp_def, id_eq, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, zero_mul, one_mul, sub_zero] using hd
  · have hd := hh.2.2.1.comp_hasDerivWithinAt q.2
      ((hasDerivWithinAt_const q.2 (Icc l S) q.1).prodMk (hasDerivWithinAt_id q.2 (Icc l S)))
      (show MapsTo (fun t : ℝ => (q.1, t)) (Icc l S) (Icc Y Z ×ˢ Icc l S) from fun _ ht => ⟨hq.1, ht⟩)
    simpa only [Function.comp_def, id_eq, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, zero_mul, one_mul, zero_sub, neg_div] using hd

end BandCoordinates


-- Two independently chosen charts agree on overlapping parameter sets in arbitrary rectangles.
example {M e Λ A B U V : ℝ} {h r : ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAR : A < r 0)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ}
    (hfA : MemLp f p (volume.restrict (Icc 0 A))) (hfU : MemLp f p (volume.restrict (Icc 0 U)))
    {x : WaveState A B} {y : WaveState U V}
    (hx : IsWaveIntegral hA hB e Λ (incomingWaveCurve hA hAR hp hfA (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ B hc hi hrc hr0) (incomingWaveVelocity hAR hp hfA) x)
    (hy : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hfU (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hfU) y)
    {D E : Set (ℝ × ℝ)} {χ ψ : ℝ × ℝ → ℝ}
    (hχ : ∀ q ∈ D, χ q ∈ Icc 0 A ∧ q.2 ∈ Icc 0 B ∧
      x.1 (projIcc 0 A hA (χ q)) (projIcc 0 B hB q.2) 0 = q.1)
    (hψ : ∀ q ∈ E, ψ q ∈ Icc 0 U ∧ q.2 ∈ Icc 0 V ∧
      y.1 (projIcc 0 U hU (ψ q)) (projIcc 0 V hV q.2) 0 = q.1) : EqOn χ ψ (D ∩ E) := by
  intro q hq
  obtain ⟨hχu, hχt, hχr⟩ := hχ q hq.1
  obtain ⟨hψu, hψt, hψr⟩ := hψ q hq.2
  rw [projIcc_of_mem hA hχu, projIcc_of_mem hB hχt] at hχr
  rw [projIcc_of_mem hU hψu, projIcc_of_mem hV hψt] at hψr
  exact hx.horizon_radius_coordinate_unique hA hB hAR hU hV hUR hc hi hrc hr0 hφ hrd hp hfA hfU hy
    ⟨χ q, hχu⟩ ⟨ψ q, hψu⟩ hχt hψt (hχr.trans hψr.symm)


section ScalarResidual

variable (B : Background) (hb : B.criticalExponent < 1)
  {U V : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
  {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
  {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
  (hx : IsWaveIntegral hU hV B.charge B.cosmological zIn vOut uIn x)
  {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
  (hinu : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 0 = -1)
  {f : ℝ → ℝ} (hc : ContinuousOn f (Ioi 0))
  (hif : ∀ᵐ t ∂volume.restrict (Icc 0 U), uIn t 1 = f t)
  (u : Icc 0 U) (v : Icc 0 V)

-- The envelope C*E(a*v+d) contributes exactly -a*c*W*C*E', with its sign and scale retained.
example (hu : 0 < (u : ℝ)) (hr : x.1 u v 0 ∈ Ioo B.inner B.event)
    (hnu : radialNuField hV B.charge B.cosmological zIn x.1 hx.choose u v ≠ 0)
    (hlam : x.2.1 u v 0 ≠ 0) {E : ℝ → ℝ} {E' Ch d : ℝ}
    (hE : HasDerivAt E E' (B.outerRate * v + d)) :
    let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
    let C := scalarTransportCorrection hV ν x.2.1
    let R := fun t => intervalExtension hV (x.1 u) t 0
    let ζ := fun t => zIn u 0 * f u + intervalExtension hV (C u) t
    let Θ := fun t => Real.exp (B.innerRate * t) * (R t * intervalExtension hV (x.2.1 u) t 1)
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).1 (B.event - y)
    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hb).2 (B.event - y)
    let H := fun t => Ch * E (B.outerRate * t + d)
    let P := fun t => Θ t - X (R t) * H t
    let Q := fun t => Real.exp (B.innerRate * t) * (u : ℝ) * ζ t / B.criticalWeight (R t) - W (R t) * H t
    let r₀ := x.1 u v 0
    let q₀ := B.criticalWeight r₀
    let Bc := (u : ℝ) * ν u v / (r₀ * x.2.1 u v 0)
    let c₀ := -1 / B.F r₀
    let c := -1 / x.2.1 u v 0
    HasDerivWithinAt Q
      (-x.2.1 u v 0 * (Bc / q₀ * P v + B.innerRate * (c - c₀) * Q v +
        (((Bc - 1 / (B.outerRate * r₀)) / q₀ * X r₀ + B.innerRate * (c - c₀) * W r₀) * H v -
          B.outerRate * c * W r₀ * Ch * E'))) (Icc 0 V) v := by
  intro ν C R ζ Θ X W H P Q r₀ q₀ Bc c₀ c
  have hH : HasDerivWithinAt H (Ch * (E' * B.outerRate)) (Icc 0 V) v := by
    simpa only [H, mul_one, Function.comp_def, id_eq] using
      ((hE.comp (v : ℝ) (((hasDerivAt_id (v : ℝ)).const_mul B.outerRate).add_const d)).const_mul Ch).hasDerivWithinAt
  have hh := (hx.radial_mode_residual B hb hzin hinu hc hif u v hu hr hH hnu hlam).2.2
  have hd : HasDerivWithinAt Q
      (-x.2.1 u v 0 * (Bc / q₀ * P v + B.innerRate * (c - c₀) * Q v +
        (((Bc - 1 / (B.outerRate * r₀)) / q₀ * X r₀ + B.innerRate * (c - c₀) * W r₀) * H v -
          c * W r₀ * (Ch * (E' * B.outerRate))))) (Icc 0 V) v := by
    simpa only [Q, P, Θ, ζ, R, X, W, Bc, c, c₀, q₀, r₀, intervalExtension_apply,
      projIcc_of_mem hU u.property] using hh
  apply hd.congr_deriv
  ring

-- Pullback through an actual radius chart gives the inward transport coefficient A*Z.
example (hu : (u : ℝ) ∈ Ioo 0 U) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hnu : radialNuField hV B.charge B.cosmological zIn x.1 hx.choose u v ≠ 0) :
    let ν := radialNuField hV B.charge B.cosmological zIn x.1 hx.choose
    let ζ := zIn u 0 * f u + scalarTransportCorrection hV ν x.2.1 u v
    ∃ χ : ℝ × ℝ → ℝ, χ (x.1 u v 0, v) = u ∧
      HasDerivAt (fun y => Real.exp (B.innerRate * v) *
        (intervalExtension hU x.1 (χ (y, v)) v 0 * intervalExtension hU x.2.1 (χ (y, v)) v 1))
        (-(x.2.1 u v 0 / (x.1 u v 0 * (u : ℝ) * ν u v)) *
          (Real.exp (B.innerRate * v) * (u : ℝ) * ζ)) (x.1 u v 0) := by
  intro ν ζ
  obtain ⟨χ, hχ, hd, _hnear⟩ := hx.exists_radial_coordinate_chart hx.choose hzin hinu u v hu hv hnu
  have hχd : HasDerivAt (fun y => χ (y, v)) (ν u v)⁻¹ (x.1 u v 0) := by
    have hh := hd.comp_hasStrictDerivAt (x.1 u v 0)
      ((hasStrictDerivAt_id (x.1 u v 0)).prodMk (hasStrictDerivAt_const (x.1 u v 0) (v : ℝ)))
    simpa only [Function.comp_def, id_eq, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, zero_mul, one_mul, sub_zero] using hh.hasDerivAt
  have hθ := ((hx.theta_hasDerivWithinAt_of_continuous hzin hinu hc hif
    (show (u : ℝ) ∈ Ioc 0 U from ⟨hu.1, hu.2.le⟩) v).hasDerivAt (Icc_mem_nhds hu.1 hu.2)).const_mul
      (Real.exp (B.innerRate * v))
  have hh := hθ.comp_of_eq (x.1 u v 0) hχd hχ.symm
  refine ⟨χ, hχ, ?_⟩
  apply hh.congr_deriv
  dsimp only [ζ, ν]
  field_simp [hx.choose u v, hnu, hu.1.ne']

end ScalarResidual

section BandResidual

-- No finite-measure assumption is needed to obtain actual L2 membership of both sources.
example {T ε C : ℝ} {a b c H D : ℝ → ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (ha : AEStronglyMeasurable a (volume.restrict (Ici T)))
    (hb : AEStronglyMeasurable b (volume.restrict (Ici T)))
    (hc : AEStronglyMeasurable c (volume.restrict (Ici T)))
    (hH : MemLp H 2 (volume.restrict (Ici T))) (hD : MemLp D 2 (volume.restrict (Ici T)))
    (he : ∀ᵐ t ∂volume.restrict (Ici T), |a t| + |b t| ≤ ε)
    (hbound : ∀ᵐ t ∂volume.restrict (Ici T), |c t| ≤ C) :
    MemLp (fun t => a t * H t) 2 (volume.restrict (Ici T)) ∧
      MemLp (fun t => b t * H t - c t * D t) 2 (volume.restrict (Ici T)) := by
  have hh := residual_energy_bound hε hC ha hb hc hH hD he hbound
  exact ⟨hh.1, hh.2.1⟩

-- At p=infinity the whole-line budgets cover every window with any fixed outer endpoint below r_plus.
example (B : Background) (hm : B.criticalExponent < 1) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let X := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).1 (B.event - y)
    let W := fun y => extendCurve B.radialLength_pos.le (B.radialMode hm).2 (B.event - y)
    ∃ δ R : ℝ, 0 < δ ∧ R ∈ Ioo B.inner B.event ∧
      ∀ Y Z : ℝ, B.inner < Y → Y < Z → Y ≤ R → Z < B.event →
        ∃ U₀ C : ℝ, ∃ τ : Ioi (0 : ℝ) → Ioi (0 : ℝ) → ℝ, 0 < U₀ ∧ U₀ ≤ δ ∧ 0 < C ∧
          ∀ f : ℝ → ℝ, MemLp f ∞ (volume.restrict (Icc 0 δ)) →
            (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0), U ≤ U₀ →
              ∀ (hfU : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
                (hx : IsWaveIntegral hU hV B.charge B.cosmological
                  (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0))
                  (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                  (incomingWaveVelocity hUR le_top hfU) x),
                ∀ (hUp : 0 < U) (ε : Ioi (0 : ℝ)) (l S : ℝ), τ ε ⟨U, hUp⟩ ≤ l → l ≤ S → S < V →
                  let ν := radialNuField hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR le_top hfU (horizonPhi h r 0)) x.1 hx.choose
                  ∃ χ : ℝ × ℝ → ℝ, ContinuousOn χ (Icc Y Z ×ˢ Icc l S) ∧
                    (∀ q ∈ Icc Y Z ×ˢ Icc l S,
                      x.1 (projIcc 0 U hU (χ q)) (projIcc 0 V hV q.2) 0 = q.1) ∧
                    ∀ y ∈ Icc Y Z,
                      let N := fun t => χ (y, t) * ν (projIcc 0 U hU (χ (y, t))) (projIcc 0 V hV t)
                      let L := fun t => x.2.1 (projIcc 0 U hU (χ (y, t))) (projIcc 0 V hV t) 0
                      let α := fun t => (L t / (y * N t) - B.outerRate / y) * B.criticalWeight y * W y
                      let β := fun t => (N t / (y * L t) - 1 / (B.outerRate * y)) / B.criticalWeight y * X y +
                        B.innerRate * (-1 / L t - -1 / B.F y) * W y
                      let γ := fun t => (-1 / L t) * W y
                      ∀ P D : ℝ → ℝ, MemLp P 2 volume → MemLp D 2 volume →
                        (∫ t in Icc l S, (α t * P t) ^ 2 + (β t * P t - γ t * D t) ^ 2) ≤
                          2 * (ε : ℝ) ^ 2 * (∫ t, P t ^ 2) + 2 * C ^ 2 * (∫ t, D t ^ 2) := by
  obtain ⟨δ, R, hδ, hR, hband⟩ := B.exists_band_residual_energy hm
    hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ, R, hδ, hR, ?_⟩
  intro Y Z hY hYZ hYR hZ
  obtain ⟨U₀, C, _T, τ, hU₀, hUδ, hC, _hT, _hτ, hsolve⟩ :=
    hband Y Z hY hYZ hYR hZ
  refine ⟨U₀, C, τ, hU₀, hUδ, hC, ?_⟩
  intro f hf hfn U V hU hV hUR hUU hfU x hx hUp ε l S hstart hlS hSV
  obtain ⟨χ, hχc, hpoint, henergy⟩ :=
    hsolve ∞ le_top f hf hfn U V hU hV hUR hUU hfU x hx hUp ε l S hstart hlS hSV
  refine ⟨χ, hχc, (fun q hq => (hpoint q hq).2.1), ?_⟩
  intro y hy N L α β γ P D hP hD
  have hh := (henergy y hy P D (hP.mono_measure Measure.restrict_le_self)
    (hD.mono_measure Measure.restrict_le_self)).2.2
  have hPi := (memLp_two_iff_integrable_sq hP.aestronglyMeasurable).1 hP
  have hDi := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).1 hD
  exact hh.trans (add_le_add
    (mul_le_mul_of_nonneg_left (setIntegral_le_integral hPi (Eventually.of_forall (fun t => sq_nonneg (P t))))
      (by positivity))
    (mul_le_mul_of_nonneg_left (setIntegral_le_integral hDi (Eventually.of_forall (fun t => sq_nonneg (D t))))
      (by positivity)))

end BandResidual

section OuterFeedback

-- The actual signed input, rather than its absolute value, occurs in the direct term.
example {m e Λ U V : ℝ} {h r f : ℝ → ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
      (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_rfl hf) x)
    (u : Icc 0 U) (v : Icc 0 V) :
    let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
    x.1 u v 0 * x.2.1 u v 1 = h v +
      (∫ t in (0 : ℝ)..u, -x.2.1 (projIcc 0 U hU t) v 0 *
        ((r 0 - t) / x.1 (projIcc 0 U hU t) v 0) * f t) +
      scalarRadiationFeedback hU hV x.1 x.2.1 ν hx.choose u v := by
  intro ν
  have hh := hx.theta_incoming_feedback hx.choose rfl
    (incomingWave_constraint_data hU hUR le_rfl hf (horizonPhi h r 0)).1 u v
  have htrace : x.1 ⟨0, le_rfl, hU⟩ v 0 * horizonWaveVelocity m e Λ V hc hi hrc hr0 v 1 = h v := by
    rw [(hx.horizon_traces hU hV hUR hc hi hrc hr0 hφ hrd le_rfl hf).2 v]
    change r v * (h v / r v) = h v
    field_simp [hr0 v]
  rw [htrace] at hh
  convert hh using 2
  congr 1
  simp only [intervalIntegral.integral_of_le u.property.1]
  apply integral_congr_ae
  have hs : Ioc (0 : ℝ) u ⊆ Icc 0 U := fun _ ht => ⟨ht.1.le, ht.2.trans u.property.2⟩
  filter_upwards [ae_mono (Measure.restrict_mono hs le_rfl) (incomingWaveVelocity_ae hUR le_rfl hf),
    ae_restrict_mem measurableSet_Ioc] with t ht htu
  rw [ht, incomingWaveCurve_apply, projIcc_of_mem hU (hs htu)]
  rfl

-- One scale, chosen before all p=infinity profiles and time windows, makes the feedback arbitrarily small.
example {m e Λ a k ρ R nH NH H W A ε : ℝ} {h r : ℝ → ℝ}
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass m h t) e Λ) (Ici 0) t)
    (hk : 0 ≤ k) (hka : k < a) (hρ : 0 < ρ)
    (hnH : 0 < nH) (hNH : 0 < NH) (hH : 0 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (haxis : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (2 * ρ) R)
    (hνaxis : ∀ t ∈ Ici (0 : ℝ),
      nH * Real.exp (a * t) ≤ -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ∧
      -horizonNu (fun w => horizonK (r w) (horizonMass m h w) e Λ) t ≤ NH * Real.exp (a * t))
    (hout : ∀ t ∈ Ici (0 : ℝ), Real.exp (k * t) * |h t| ≤ H)
    (hlout : ∀ t ∈ Ici (0 : ℝ), |horizonFunction (r t) (horizonMass m h t) e Λ| ≤ W)
    (hε : 0 < ε) :
    ∃ (δ : ℝ) (hδ : 0 < δ),
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f ∞ (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0))
          (horizonWaveVelocity m e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR le_top hf) x),
        (eLpNorm f ∞ (volume.restrict (Icc 0 U))).toReal ≤ A →
        let ν := radialNuField hV e Λ (incomingWaveCurve hU hUR le_top hf (horizonPhi h r 0)) x.1 hx.choose
        let F := scalarRadiationFeedback hU hV x.1 x.2.1 ν hx.choose
        let M := outerRadiationEnvelope hδ.le a k x
        ∀ (l S E : ℝ) (g : ℝ → ℝ), 0 ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
          (∀ t ∈ Icc l S, g t ∈ Icc 0 U ∧ g t ≤ δ * Real.exp (-a * t)) →
          (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤ E →
          (∫ t in l..S, (Real.exp (k * t) * F (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2) ≤
            ε ^ 2 * E := by
  obtain ⟨δ₀, L, N, hδ₀, _hδ₀1, _hδ₀r, hL, hN, hb⟩ :=
    exists_horizon_outer_feedback_energy hc hi hrc hr0 hφ hrd hk hka hρ hnH hNH hH hW hA
      haxis hνaxis hout hlout
  let δ := min δ₀ (ε * (ρ ^ 2 * (a - k)) / (L * N + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hd : 0 < ρ ^ 2 * (a - k) := by positivity
  have hsmall : L * N * δ / (ρ ^ 2 * (a - k)) ≤ ε := by
    apply (div_le_iff₀ hd).2
    have hh := (le_div_iff₀ (by positivity : 0 < L * N + 1)).1
      (show δ ≤ ε * (ρ ^ 2 * (a - k)) / (L * N + 1) from min_le_right _ _)
    nlinarith only [hh, hδ]
  refine ⟨δ, hδ, ?_⟩
  intro U V hU hV hUR f hf x hx hfn ν F M l S E g hl hlS hSV hgc hg hE
  have he := (hb δ hδ (min_le_left _ _) U V hU hV hUR ∞ le_top f hf x hx hfn
    (by simpa only [ENNReal.toReal_top, div_zero, sub_zero, mul_one] using hka.le)).2
    l S g hl hlS hSV hgc hg
  have hE0 : 0 ≤ E := (intervalIntegral.integral_nonneg hV (fun t _ => sq_nonneg (M (projIcc 0 V hV t)))).trans hE
  exact he.trans ((mul_le_mul_of_nonneg_left hE (sq_nonneg _)).trans
    (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (by positivity) hε.le).2 hsmall) hE0))

end OuterFeedback

section LogarithmicMatching

-- The moment retains the sign and normalization of a critical p=4 input, also at u=0.
example {u : ℝ} (hu : 0 ≤ u) (ℓ : ℝ) :
    (∫ x in (0 : ℝ)..u, x * logarithmicIncoming (3 / 4) ℓ
      (BoundedContinuousFunction.const ℝ (-2)) x) = -(6 / 7) * u ^ (7 / 4 : ℝ) := by
  rw [(logarithmicIncoming_first_moment (by norm_num : (0 : ℝ) < 3 / 4) hu ℓ
    (BoundedContinuousFunction.const ℝ (-2))).2, terminalGreen_const]
  norm_num
  ring

-- Only the derivative needs an L2 budget; a nonzero constant profile is permitted.
example {c : ℝ} (hc : 0 < c) (q : ℝ) :
    Integrable (fun t => (c * terminalGreen hc (BoundedContinuousFunction.const ℝ q) t - q) ^ 2) ∧
      (∫ t, (c * terminalGreen hc (BoundedContinuousFunction.const ℝ q) t - q) ^ 2) = 0 := by
  have hh := terminalGreen_approximation_energy hc (BoundedContinuousFunction.const ℝ q)
    (BoundedContinuousFunction.const ℝ 0) (fun t => hasDerivAt_const t q)
    (by simp [Integrable, HasFiniteIntegral]; exact aestronglyMeasurable_const)
  simp only [BoundedContinuousFunction.const_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    integral_zero, mul_zero] at hh
  exact ⟨hh.1, le_antisymm hh.2 (integral_nonneg (fun t => sq_nonneg _))⟩

-- The manuscript's signed coefficient and an arbitrary observation cutoff preserve the whole-line bound.
example {a b k δ cν r₀ rplus T : ℝ} (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hcrit : k = a * b) (ℓ : ℝ) (B D : ℝ →ᵇ ℝ)
    (hd : ∀ t, HasDerivAt B (D t) t) (hD : Integrable (fun t => D t ^ 2)) :
    let C := a * cν * (r₀ / rplus)
    let E := fun v => C * Real.exp ((a + k) * v) *
      (∫ x in (0 : ℝ)..(δ * Real.exp (-a * v)), x * logarithmicIncoming b ℓ B x) -
      C * (b * δ ^ (b + 1) / (b + 1)) * B (ℓ - Real.log δ + a * v)
    IntegrableOn (fun v => E v ^ 2) (Ici T) ∧
      (∫ v in Ici T, E v ^ 2) ≤
        C ^ 2 * ((b * δ ^ (b + 1) / (b + 1) ^ 2) ^ 2 / a * ∫ t, D t ^ 2) := by
  intro C E
  let F := fun v => Real.exp ((a + k) * v) *
    (∫ x in (0 : ℝ)..(δ * Real.exp (-a * v)), x * logarithmicIncoming b ℓ B x) -
    (b * δ ^ (b + 1) / (b + 1)) * B (ℓ - Real.log δ + a * v)
  have hh := logarithmicIncoming_first_moment_energy ha hb hδ hcrit ℓ B D hd hD
  have he (v : ℝ) : E v ^ 2 = C ^ 2 * F v ^ 2 := by dsimp only [E, F]; ring
  have hi : Integrable (fun v => E v ^ 2) := by simp_rw [he]; exact hh.1.const_mul _
  refine ⟨hi.integrableOn, (setIntegral_le_integral hi (Eventually.of_forall (fun v => sq_nonneg (E v)))).trans ?_⟩
  simp_rw [he]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hh.2 (sq_nonneg C)

end LogarithmicMatching

section OuterFluxNormalization

-- Zero flux error gives the signed coefficient exactly, retaining the horizon term also at u=0.
example {U V e Λ S A : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hS : 0 < S) (v : Icc 0 V)
    (hflux : ∀ q : Icc 0 U,
      x.1 q v 0 * (Real.exp (x.1 q v 2) * radialPotential (x.1 q v 0) e Λ) / S = -A)
    (u : Icc 0 U) :
    x.2.1 u v 0 / x.1 u v 0 =
      x.1 ⟨0, le_rfl, hU⟩ v 0 * vOut v 0 / (x.1 u v 0) ^ 2 - A * u * S / (x.1 u v 0) ^ 2 := by
  have hh := hx.outer_lambda_coefficient hr hzin hS v (A := A) (ε := 0)
    (fun q => by rw [hflux q]; simp only [neg_add_cancel, abs_zero, le_refl]) u
  simp only [zero_mul, zero_div, abs_nonpos_iff] at hh
  linarith only [hh]

-- One width and time cutoff control the relative coefficient for every actual p=4 profile.
example (B : Background) {s H dH A ε : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hε : 0 < ε)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ T : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (_hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A → U * Real.exp (B.outerRate * V) ≤ δ →
        ∀ (u : Icc 0 U) (v : Icc 0 V), 0 < (u : ℝ) → T ≤ (v : ℝ) →
          |(x.2.1 u v 0 / x.1 u v 0 -
            r v * horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological / (x.1 u v 0) ^ 2) /
            (u * (cν * Real.exp (B.outerRate * v))) + B.outerRate / B.event| ≤ ε := by
  intro hi hr0 cν
  obtain ⟨δ, T, hδ, hδ1, hT, hb⟩ :=
    B.exists_outer_flux_normalization hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut 1 ε zero_lt_one hε
  refine ⟨δ, T, hδ, hδ1, hT, ?_⟩
  intro U V hU hV hUR f hf x hx hfn hwidth u v hu hv
  have hh := (hb U V hU hV hUR 4 le_rfl f hf x hx hfn hwidth u v hv).2
  have hd : 0 < (u : ℝ) * (cν * Real.exp (B.outerRate * v)) :=
    mul_pos hu (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  have hcν : cν ≠ 0 := (Real.exp_pos _).ne'
  have heq (q : ℝ) : q / (u * (cν * Real.exp (B.outerRate * v))) + B.outerRate / B.event =
      (q + (B.outerRate / B.event) * u * (cν * Real.exp (B.outerRate * v))) /
        (u * (cν * Real.exp (B.outerRate * v))) := by field_simp [hu.ne', hcν, B.event_pos.ne']
  rw [heq, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  simpa only [mul_assoc] using hh

end OuterFluxNormalization

section MovingOuterFlux

-- A continuous observation curve needs no derivative and the incoming function needs only L2.
example {U V l S : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (K : C(Icc 0 U, C(Icc 0 V, ℝ))) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Icc 0 U))) (hgc : ContinuousOn g (Icc l S)) :
    ContinuousOn (fun t => ∫ w in (0 : ℝ)..(projIcc 0 U hU (g t) : ℝ),
      K (projIcc 0 U hU w) (projIcc 0 V hV t) * f w) (Icc l S) := by
  exact (continuous_kernel_primitive hU K hf).comp_continuousOn
    (((continuous_projIcc (a := (0 : ℝ)) (b := U) (h := hU)).comp_continuousOn hgc).prodMk
      (continuous_projIcc (a := (0 : ℝ)) (b := V) (h := hV)).continuousOn)

-- A single late cutoff makes the horizon contribution small on every later window, before all profiles and p.
example (B : Background) {s H dH A η : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hη : 0 < η)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ T : ℝ, 0 < δ ∧ δ < 1 ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (p : ℝ≥0∞) (hp : 4 ≤ p) (f : ℝ → ℝ) (hf : MemLp f p (volume.restrict (Icc 0 U)))
        (x : WaveState U V)
        (_hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR hp hf) x),
        (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A →
        let k := B.outerRate * (1 - 1 / p.toReal)
        let Q := fun (u : Icc 0 U) (v : Icc 0 V) =>
          r v * horizonFunction (r v) (horizonMass B.mass h v) B.charge B.cosmological *
            ∫ t in (0 : ℝ)..u, (r 0 - t) / (x.1 (projIcc 0 U hU t) v 0) ^ 2 * f t
        ∀ (l S : ℝ) (g : ℝ → ℝ), T ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
          (∀ t ∈ Icc l S, g t ∈ Icc 0 U ∧ g t * Real.exp (B.outerRate * t) ≤ δ) →
          IntegrableOn (fun t => (Real.exp (k * t) * Q (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2)
            (Icc l S) ∧
          (∫ t in l..S, (Real.exp (k * t) * Q (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2) ≤ η ^ 2 := by
  intro hi hr0
  obtain ⟨C, _hC, hb⟩ := B.exists_moving_outer_flux hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  obtain ⟨δ, T, hδ, hδ1, _hδ1le, hT, hm⟩ := hb 1 1 zero_lt_one zero_lt_one
  have hlim : Tendsto (fun t : ℝ => C ^ 2 / (4 * s) * Real.exp (-(4 * s) * t)) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-(4 * s) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith only [hs] : -(4 * s) < 0))
    simpa only [mul_zero] using he.const_mul (C ^ 2 / (4 * s))
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hlim.eventually_lt_const (sq_pos_of_pos hη))
  refine ⟨δ, max T T₁, hδ, hδ1, hT.trans (le_max_left _ _), ?_⟩
  intro U V hU hV hUR p hp f hf x hx hfn k Q l S g hl hlS hSV hgc hg
  have he := ((hm U V hU hV hUR p hp f hf x hx hfn).2 k le_rfl).2 l S g
    ((le_max_left _ _).trans hl) hlS hSV hgc hg
  exact ⟨he.1, he.2.trans (hT₁ l ((le_max_right _ _).trans hl)).le⟩

end MovingOuterFlux

section OuterMoment

-- On an exact scaled-width curve the physical leading coefficient gives the signed Green average.
example {a b k δ r₀ rplus cν : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hcrit : k = a * b)
    (ℓ : ℝ) (P : ℝ →ᵇ ℝ) (θ : ℝ → ℝ) (v : ℝ) :
    Real.exp (k * v) * (θ v - (a / rplus) * r₀ * (cν * Real.exp (a * v)) *
      (∫ t in (0 : ℝ)..(δ * Real.exp (-a * v)), t * logarithmicIncoming b ℓ P t)) =
      Real.exp (k * v) * θ v - (a / rplus) * r₀ * cν *
        (b * δ ^ (b + 1) * terminalGreen (by linarith : 0 < b + 1) P (ℓ - Real.log δ + a * v)) := by
  rw [mul_sub]
  congr 1
  calc
    _ = ((a / rplus) * r₀ * cν) * (Real.exp ((a + k) * v) *
        (∫ t in (0 : ℝ)..(δ * Real.exp (-a * v)), t * logarithmicIncoming b ℓ P t)) := by
      rw [add_mul, Real.exp_add]
      ring
    _ = _ := by rw [logarithmicIncoming_scaled_first_moment hb hδ hcrit ℓ P v]

-- The actual p=4 field retains its feedback, with a common profile-energy budget and no endpoint factor.
example (B : Background) {s H dH A ε E₀ : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A) (hε : 0 < ε)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ C δ T : ℝ, 0 ≤ C ∧ 0 < δ ∧ δ < 1 ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0) (ℓ : ℝ) (P : ℝ →ᵇ ℝ)
        (_hP : Integrable (fun t => P t ^ 2))
        (hf : MemLp (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
        (∫ t, P t ^ 2) ≤ E₀ →
        let k := B.outerRate * (3 / 4)
        let ν := radialNuField hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
        let F := scalarRadiationFeedback hU hV x.1 x.2.1 ν hx.choose
        let E := fun (u : Icc 0 U) (v : Icc 0 V) =>
          x.1 u v 0 * x.2.1 u v 1 - h v - F u v -
            (B.outerRate / B.event) * r 0 * (cν * Real.exp (B.outerRate * v)) *
              ∫ t in (0 : ℝ)..u, t * logarithmicIncoming (3 / 4) ℓ P t
        ∀ (l S : ℝ) (g : ℝ → ℝ), T ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
          (∀ t ∈ Icc l S, g t ∈ Icc 0 U ∧ g t * Real.exp (B.outerRate * t) ≤ δ) →
          IntegrableOn (fun t => (Real.exp (k * t) * E (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2)
            (Icc l S) ∧
          (∫ t in l..S, (Real.exp (k * t) * E (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2) ≤
            2 * (ε * δ) ^ 2 * δ ^ (3 / 2 : ℝ) / B.outerRate * E₀ + C * Real.exp (-(4 * s) * l) := by
  intro hi hr0 cν
  obtain ⟨C, hC, hm⟩ := B.exists_outer_moment_energy hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  obtain ⟨δ, T, hδ, hδ1, _hδ1le, hT, hm⟩ := hm 1 ε zero_lt_one hε
  refine ⟨C, δ, T, hC, hδ, hδ1, hT, ?_⟩
  intro U V hU hV hUR ℓ P hP hf x hx hfn hPE k ν F E l S g hl hlS hSV hgc hg
  have he := hm U V hU hV hUR 4 le_rfl (3 / 4) k ℓ P (by norm_num) rfl
    (by norm_num [k]) hP hf x hx hfn l S g hl hlS hSV hgc hg
  refine ⟨he.1, ?_⟩
  have hcoef : 0 ≤ 2 * (ε * δ) ^ 2 * δ ^ (2 * (3 / 4 : ℝ)) / B.outerRate := by
    positivity [B.outerRate_pos]
  have hfinal := he.2.trans (add_le_add (mul_le_mul_of_nonneg_left hPE hcoef) le_rfl)
  simpa only [show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] using hfinal

end OuterMoment

section LateOuterFeedback

-- Only the observation row needs a small lambda; the scalar history still begins at zero.
example {U V e Λ a k ρ R N L δ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {z₀ : WaveVector} (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hlo : ∀ u v, ρ ≤ x.1 u v 0) (hin : ∀ u, |zIn u 0| ≤ R)
    (hν : ∀ u v, |radialNuField hV e Λ zIn x.1 hr u v| ≤ N * Real.exp (a * v))
    (hwidth : ∀ (u : Icc 0 U) (v : Icc 0 V), (u : ℝ) * Real.exp (a * v) ≤ δ)
    (M : C(Icc 0 V, ℝ)) (hM0 : ∀ v, 0 ≤ M v)
    (hM : ∀ (u : Icc 0 U) (v : Icc 0 V), Real.exp (k * v) * |x.1 u v 0 * x.2.1 u v 1| ≤ M v)
    (u : Icc 0 U) (v : Icc 0 V) (hlam : ∀ w : Icc 0 U, w ≤ u → |x.2.1 w v 0| ≤ L * δ) :
    Real.exp (k * v) *
        |scalarRadiationFeedback hU hV x.1 x.2.1 (radialNuField hV e Λ zIn x.1 hr) hr u v| ≤
      (L * N / ρ ^ 2) * δ ^ 2 * causalExpIntegral hV (a - k) M v := by
  have hh := hx.outer_feedback_kernel_at hr hzin hinu hρ hN (mul_nonneg hL hδ)
    (fun _ => U) antitone_const (fun q w _ => hlo q w) hin (fun q w _ => hν q w)
    (fun q w _ => hwidth q w) M hM0 (fun q w _ => hM q w) u v u.property.2 hlam
  exact hh.trans_eq (by ring)

-- At critical p=4 the squared feedback, divided by the leading squared moment scale, gains delta^(1/2).
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ₀ C : ℝ, 0 < δ₀ ∧ 0 < C ∧
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ → ∃ T : ℝ, 0 ≤ T ∧
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (f : ℝ → ℝ) (hf : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR le_rfl hf) x),
          (eLpNorm f 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
          let k := B.outerRate * (3 / 4)
          let ν := radialNuField hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0)) x.1 hx.choose
          let F := scalarRadiationFeedback hU hV x.1 x.2.1 ν hx.choose
          let M := outerRadiationEnvelope hδ.le B.outerRate k x
          ∀ E₀ : ℝ, (∫ t in (0 : ℝ)..V, (M (projIcc 0 V hV t)) ^ 2) ≤ E₀ →
            ∀ (l S : ℝ) (g : ℝ → ℝ), T ≤ l → l ≤ S → S ≤ V → ContinuousOn g (Icc l S) →
              (∀ t ∈ Icc l S, g t ∈ Icc 0 U ∧ g t ≤ δ * Real.exp (-B.outerRate * t)) →
              (∫ t in l..S, (Real.exp (k * t) * F (projIcc 0 U hU (g t)) (projIcc 0 V hV t)) ^ 2) /
                  δ ^ (7 / 2 : ℝ) ≤ (4 * C / B.outerRate) ^ 2 * δ ^ (1 / 2 : ℝ) * E₀ := by
  intro hi hr0
  obtain ⟨δ₀, L, C, _Dt, hδ₀, _hδ₀1, _hL, hC, _hDt, hm⟩ :=
    B.exists_late_outer_feedback hs hH hdH hdHR hA hc hb hrc hrb hrd hrdec hOut
  refine ⟨δ₀, C, hδ₀, hC, ?_⟩
  intro δ hδ hδδ
  obtain ⟨T, hT, hm⟩ := hm δ hδ hδδ
  refine ⟨T, hT, ?_⟩
  intro U V hU hV hUR f hf x hx hfn k ν F M E₀ hME l S g hl hlS hSV hgc hg
  have hk : k < B.outerRate := by dsimp only [k]; linarith only [B.outerRate_pos]
  have he := (((hm U V hU hV hUR 4 le_rfl f hf x hx hfn).2 k hk).2.2 l S g hl hlS hSV hgc hg).2
  have hbound := he.trans (mul_le_mul_of_nonneg_left hME (sq_nonneg _))
  have hden : B.outerRate - k = B.outerRate / 4 := by dsimp only [k]; ring
  have hpw : δ ^ (4 : ℕ) / δ ^ (7 / 2 : ℝ) = δ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast δ 4, ← Real.rpow_sub hδ]
    norm_num
  have hh := div_le_div_of_nonneg_right hbound (Real.rpow_nonneg hδ.le (7 / 2 : ℝ))
  exact hh.trans_eq (by rw [hden, ← hpw]; ring)

end LateOuterFeedback

section OuterMomentComparison

-- A smaller moving width inherits the same finite-time energy budget, including zero-width intervals.
example {U V δ Δ a k : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hδ : 0 ≤ δ) (hΔ : 0 ≤ Δ) (hδΔ : δ ≤ Δ) (x : WaveState U V) :
    (∫ t in (0 : ℝ)..V, (outerRadiationEnvelope hδ a k x (projIcc 0 V hV t)) ^ 2) ≤
      ∫ t in (0 : ℝ)..V, (outerRadiationEnvelope hΔ a k x (projIcc 0 V hV t)) ^ 2 := by
  apply intervalIntegral.integral_mono_on (μ := volume) hV
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro t _
  exact (sq_le_sq₀ (outerRadiationEnvelope_nonneg hδ a k x _) (outerRadiationEnvelope_nonneg hΔ a k x _)).2
    (outerRadiationEnvelope_mono_width hU hδ hΔ hδΔ x _)

-- The actual critical p=4 trace matches the signed Green average without a feedback or radiation-energy premise.
example (B : Background) {s H dH A cap ε : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hks : B.outerRate * (3 / 4) < s) (hcap : 0 < cap) (hε : 0 < ε)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ T : ℝ, 0 < δ ∧ δ < cap ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (ℓ : ℝ) (P : ℝ →ᵇ ℝ) (_hP : Integrable (fun t => P t ^ 2))
        (hf : MemLp (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
        let k := B.outerRate * (3 / 4)
        let g := fun t => δ * Real.exp (-B.outerRate * t)
        let Θ := fun t => Real.exp (k * t) *
          (x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 *
            x.2.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 1)
        ∀ E₀ : ℝ, (∫ t, P t ^ 2) ≤ E₀ →
          ∀ l S : ℝ, T ≤ l → l ≤ S → S ≤ V → g l ≤ U →
            (∫ t in l..S, (Θ t - (B.outerRate / B.event) * r 0 * cν *
              ((3 / 4) * δ ^ (7 / 4 : ℝ) *
                terminalGreen (by norm_num : (0 : ℝ) < 7 / 4) P (ℓ - Real.log δ + B.outerRate * t))) ^ 2) /
              δ ^ (7 / 2 : ℝ) ≤ ε * (1 + E₀) := by
  intro hi hr0 cν
  obtain ⟨δ, T, hδ, hδcap, _hδ1, hT, hm⟩ := B.exists_outer_radiation_moment_comparison
    hs hH hdH hdHR hA (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    rfl hks hc hb hrc hrb hrd hrdec hOut cap ε hcap hε
  refine ⟨δ, T, hδ, hδcap, hT, ?_⟩
  intro U V hU hV hUR ℓ P hP hf x hx hfn k g Θ E₀ hPE l S hl hlS hSV hgl
  have hg (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Icc 0 U ∧ g t * Real.exp (B.outerRate * t) ≤ δ := by
    have hgt : g t ≤ g l := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.2 B.outerRate_pos.le))) hδ.le
    refine ⟨⟨mul_nonneg hδ.le (Real.exp_pos _).le, hgt.trans hgl⟩, ?_⟩
    simp only [g, mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one, le_refl]
  have he := (hm U V hU hV hUR 4 le_rfl ℓ P (by norm_num [k]) hP hf x hx hfn
    l S g hl hlS hSV (by fun_prop) hg).2
  have heq (t : ℝ) (ht : t ∈ Icc l S) :
      Real.exp (k * t) *
        (x.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 0 *
          x.2.1 (projIcc 0 U hU (g t)) (projIcc 0 V hV t) 1 -
          (B.outerRate / B.event) * r 0 * (cν * Real.exp (B.outerRate * projIcc 0 V hV t)) *
            ∫ w in (0 : ℝ)..(projIcc 0 U hU (g t) : ℝ), w * logarithmicIncoming (3 / 4) ℓ P w) =
        Θ t - (B.outerRate / B.event) * r 0 * cν *
          ((3 / 4) * δ ^ (7 / 4 : ℝ) *
            terminalGreen (by norm_num : (0 : ℝ) < 7 / 4) P (ℓ - Real.log δ + B.outerRate * t)) := by
    have htV : t ∈ Icc 0 V := ⟨hT.trans (hl.trans ht.1), ht.2.trans hSV⟩
    rw [mul_sub]
    change Θ t - _ = _
    congr 1
    rw [projIcc_of_mem hV htV, projIcc_of_mem hU (hg t ht).1]
    calc
      _ = ((B.outerRate / B.event) * r 0 * cν) * (Real.exp ((B.outerRate + k) * t) *
          ∫ w in (0 : ℝ)..(g t), w * logarithmicIncoming (3 / 4) ℓ P w) := by
        rw [add_mul, Real.exp_add]
        ring
      _ = _ := by
        rw [logarithmicIncoming_scaled_first_moment (by norm_num : (0 : ℝ) < 3 / 4) hδ rfl ℓ P t]
        norm_num
  have hI := intervalIntegral.integral_congr (μ := volume) (a := l) (b := S) (fun t ht => congrArg (fun z : ℝ => z ^ 2)
    (heq t (by simpa only [uIcc_of_le hlS] using ht)))
  change (∫ t in l..S, _) ≤ _ at he
  rw [hI] at he
  norm_num only [show (2 : ℝ) * (3 / 4 + 1) = 7 / 2 by norm_num] at he
  have hfin := he.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hPE)
    (mul_nonneg hε.le (Real.rpow_nonneg hδ.le (7 / 2 : ℝ))))
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hδ (7 / 2 : ℝ))).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hfin

end OuterMomentComparison

section OuterTransverseComparison

-- The signed trace identity also covers the endpoint exponent b=1 and arbitrary profiles.
example {a δ r₀ : ℝ} (hδ : 0 < δ) (ℓ : ℝ) (P : ℝ → ℝ) (v : ℝ) :
    (δ * Real.exp (-a * v)) * Real.exp (a * v) * (r₀ - δ * Real.exp (-a * v)) *
        logarithmicIncoming 1 ℓ P (δ * Real.exp (-a * v)) =
      (r₀ - δ * Real.exp (-a * v)) * δ * P (ℓ - Real.log δ + a * v) := by
  have hh := logarithmicIncoming_scaled_trace (b := 1) hδ (by ring : a = a * 1) ℓ P v
  simp only [Real.rpow_one, one_mul] at hh
  calc
    _ = (r₀ - δ * Real.exp (-a * v)) * ((δ * Real.exp (-a * v)) * Real.exp (a * v) *
        logarithmicIncoming 1 ℓ P (δ * Real.exp (-a * v))) := by ring
    _ = _ := by rw [hh]; ring

-- Every sufficiently small exact section gives a small relative error for the actual p=4 derivative.
example (B : Background) {s H dH A cap ε : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hks : B.outerRate * (3 / 4) < s) (hcap : 0 < cap) (hε : 0 < ε)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < cap ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
          (ℓ : ℝ) (P : ℝ →ᵇ ℝ) (_hP : Integrable (fun t => P t ^ 2))
          (hf : MemLp (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
          (hx : IsWaveIntegral hU hV B.charge B.cosmological
            (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
            (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
            (incomingWaveVelocity hUR le_rfl hf) x),
          (eLpNorm (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
          let k := B.outerRate * (3 / 4)
          let g := fun t => δ * Real.exp (-B.outerRate * t)
          let Z := fun t => g t * Real.exp (k * t) *
            (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
              derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
                (Icc 0 U) (g t))
          ∀ E₀ : ℝ, (∫ t, P t ^ 2) ≤ E₀ →
            ∀ l S : ℝ, 0 ≤ l → l ≤ S → S ≤ V → g l ≤ U →
              (∫ t in l..S, (Z t - (3 / 4) * (r 0 - g t) * δ ^ (3 / 4 : ℝ) *
                P (ℓ - Real.log δ + B.outerRate * t)) ^ 2) / δ ^ (3 / 2 : ℝ) ≤ ε * (1 + E₀) := by
  intro hi hr0
  obtain ⟨d, K, hd, hK, hm⟩ := B.exists_outer_transverse_comparison
    hs hH hdH hdHR hA (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    rfl hks hc hb hrc hrb hrd hrdec hOut
  have hsmall : ∀ᶠ w : ℝ in 𝓝 0, K * w ^ (1 / 2 : ℝ) < ε :=
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).const_mul K).continuousAt.tendsto.eventually_lt_const
      (by simpa only [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_zero] using hε)
  obtain ⟨δ₀, hδ₀, hsm⟩ := (hsmall.and ((eventually_lt_nhds hd).and (eventually_lt_nhds hcap))).exists_gt
  refine ⟨δ₀, hδ₀, hsm.2.2, ?_⟩
  intro δ hδ hδδ U V hU hV hUR ℓ P hP hf x hx hfn k g Z E₀ hPE l S hl hlS hSV hgl
  have hg (t : ℝ) (ht : t ∈ Icc l S) : g t ∈ Ioc 0 U ∧ g t * Real.exp (B.outerRate * t) ≤ δ := by
    have hgt : g t ≤ g l := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.2 B.outerRate_pos.le))) hδ.le
    refine ⟨⟨mul_pos hδ (Real.exp_pos _), hgt.trans hgl⟩, ?_⟩
    simp only [g, mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one, le_refl]
  have he := (hm δ hδ (hδδ.trans hsm.2.1.le) U V hU hV hUR 4 le_rfl ℓ P
    (by norm_num [k]) hP hf x hx hfn l S g hl hlS hSV (by fun_prop) hg).2.2
  have heq (t : ℝ) :
      g t * Real.exp (k * t) *
        (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
          derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
            (Icc 0 U) (g t) - (r 0 - g t) * logarithmicIncoming (3 / 4) ℓ P (g t)) =
        Z t - (3 / 4) * (r 0 - g t) * δ ^ (3 / 4 : ℝ) *
          P (ℓ - Real.log δ + B.outerRate * t) := by
    have hh := logarithmicIncoming_scaled_trace (b := (3 / 4)) (a := B.outerRate) hδ rfl ℓ P t
    rw [mul_sub]
    change Z t - _ = _
    congr 1
    calc
      _ = (r 0 - g t) * (g t * Real.exp (k * t) * logarithmicIncoming (3 / 4) ℓ P (g t)) := by ring
      _ = _ := by rw [hh]; ring
  have hI := intervalIntegral.integral_congr (μ := volume) (a := l) (b := S)
    (fun t _ => congrArg (fun z : ℝ => z ^ 2) (heq t))
  rw [hI] at he
  simp only [show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num,
    show (2 : ℝ) * (1 - 3 / 4) = 1 / 2 by norm_num] at he
  have hcoef : K * δ ^ (1 / 2 : ℝ) ≤ ε :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hδδ (by norm_num : (0 : ℝ) ≤ 1 / 2)) hK.le).trans hsm.1.le
  have hPI : 0 ≤ ∫ t, P t ^ 2 := integral_nonneg (fun t => sq_nonneg _)
  exact he.trans ((mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hPE) hε.le))

end OuterTransverseComparison

section OuterSectionMatching

-- The two section coefficients agree with the paper's leading radial mode and normalized average.
example {a b cν δ r₀ rp G : ℝ} (hb : 0 < b) (hcν : 0 < cν) (hδ : 0 < δ) (hrp : rp ≠ 0) :
    (r₀ / (rp * cν ^ b)) * (a * b / (b + 1) * (cν * δ) ^ (b + 1)) * ((b + 1) * G) =
      (a / rp) * r₀ * cν * b * δ ^ (b + 1) * G ∧
    (r₀ / (rp * cν ^ b)) * (rp * b * (cν * δ) ^ b) = b * r₀ * δ ^ b := by
  have hbc : b + 1 ≠ 0 := (by linarith : 0 < b + 1).ne'
  have hp : cν ^ b ≠ 0 := (Real.rpow_pos_of_pos hcν b).ne'
  constructor
  · rw [Real.mul_rpow hcν.le hδ.le, Real.rpow_add hcν, Real.rpow_one]
    field_simp [hrp, hp, hbc]
  · rw [Real.mul_rpow hcν.le hδ.le]
    field_simp [hrp, hp]

-- One choice of section and time works for both actual p=4 traces and every profile in an energy budget.
example (B : Background) {s H dH A cap ε : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    (hks : B.outerRate * (3 / 4) < s) (hcap : 0 < cap) (hε : 0 < ε)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ T : ℝ, 0 < δ ∧ δ < cap ∧ 0 ≤ T ∧
      ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
        (ℓ : ℝ) (P : ℝ →ᵇ ℝ) (_hP : Integrable (fun t => P t ^ 2))
        (hf : MemLp (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
        (hx : IsWaveIntegral hU hV B.charge B.cosmological
          (incomingWaveCurve hU hUR le_rfl hf (horizonPhi h r 0))
          (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
          (incomingWaveVelocity hUR le_rfl hf) x),
        (eLpNorm (logarithmicIncoming (3 / 4) ℓ P) 4 (volume.restrict (Icc 0 U))).toReal ≤ A →
        let k := B.outerRate * (3 / 4)
        let g := fun t => δ * Real.exp (-B.outerRate * t)
        let Eθ := fun t => Real.exp (k * t) *
          (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
            intervalExtension hV (intervalExtension hU x.2.1 (g t)) t 1) -
          (B.outerRate / B.event) * r 0 * cν * (3 / 4) * δ ^ (7 / 4 : ℝ) *
            terminalGreen (by norm_num : (0 : ℝ) < 7 / 4) P (ℓ - Real.log δ + B.outerRate * t)
        let Eζ := fun t => g t * Real.exp (k * t) *
          (intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 *
            derivWithin (fun u => intervalExtension hV (intervalExtension hU x.1 u) t 1)
              (Icc 0 U) (g t)) - (3 / 4) * r 0 * δ ^ (3 / 4 : ℝ) * P (ℓ - Real.log δ + B.outerRate * t)
        ∀ E₀ : ℝ, (∫ t, P t ^ 2) ≤ E₀ →
          ∀ l S : ℝ, T ≤ l → l ≤ S → S ≤ V → g l ≤ U →
            (∫ t in l..S, Eθ t ^ 2) / δ ^ (7 / 2 : ℝ) +
              (∫ t in l..S, Eζ t ^ 2) / δ ^ (3 / 2 : ℝ) ≤ ε * (1 + E₀) := by
  intro hi hr0 cν
  obtain ⟨δ, T, hδ, hδcap, _hδ1, hT, hm⟩ := B.exists_outer_section_matching
    hs hH hdH hdHR hA (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    rfl hks hc hb hrc hrb hrd hrdec hOut cap ε hcap hε
  refine ⟨δ, T, hδ, hδcap, hT, ?_⟩
  intro U V hU hV hUR ℓ P hP hf x hx hfn k g Eθ Eζ E₀ hPE l S hl hlS hSV hgl
  have he := (hm U V hU hV hUR 4 le_rfl ℓ P (by norm_num [k]) hP hf x hx hfn l S hl hlS hSV hgl).2.2
  have hh := he.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hPE) hε.le)
  simpa only [show (3 / 4 : ℝ) + 1 = 7 / 4 by norm_num,
    show (2 : ℝ) * (7 / 4) = 7 / 2 by norm_num, show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] using hh

end OuterSectionMatching

section OuterArrivalFamily

-- Every prescribed sufficiently near-event radius is realized in every containing physical rectangle.
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let hi := horizon_mass_integrable hs hH hc hb
    let hr0 := fun t => ((sub_pos.2 hdHR).trans_le (hrb t)).ne'
    ∃ δ₀ α : ℝ, 0 < δ₀ ∧ 0 < α ∧
      ∀ Y ∈ Ico (B.event - α * δ₀) B.event,
        let δ := (B.event - Y) / α
        0 < δ ∧ δ ≤ δ₀ ∧ Y ∈ Ioo B.inner B.event ∧ ∃ T : ℝ, 0 ≤ T ∧
          ∀ (f : ℝ → ℝ) (_hf : MemLp f 4 (volume.restrict (Icc 0 δ))),
            (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
            ∃ g : ℝ → ℝ, ContinuousOn g (Ioi T) ∧ StrictAntiOn g (Ioi T) ∧
              ∀ t ∈ Ioi T, 0 < g t ∧
                ∀ (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
                  (hfU : MemLp f 4 (volume.restrict (Icc 0 U))) (x : WaveState U V)
                  (_hx : IsWaveIntegral hU hV B.charge B.cosmological
                    (incomingWaveCurve hU hUR le_rfl hfU (horizonPhi h r 0))
                    (horizonWaveVelocity B.mass B.charge B.cosmological V hc hi hrc hr0)
                    (incomingWaveVelocity hUR le_rfl hfU) x),
                  g t ≤ U → t ≤ V →
                    intervalExtension hV (intervalExtension hU x.1 (g t)) t 0 = Y := by
  intro hi hr0
  obtain ⟨δ₀, α, β, η, hδ₀, _hδ₀r, hα, _hβ, _hη, hfamily⟩ :=
    B.exists_outer_arrival_family hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut
      le_rfl B.outerRate_pos hs.le hA
  refine ⟨δ₀, α, hδ₀, hα, ?_⟩
  intro Y hY δ
  have hδ : 0 < δ := div_pos (sub_pos.2 hY.2) hα
  have hδδ : δ ≤ δ₀ := (div_le_iff₀ hα).2 (by linarith only [hY.1])
  obtain ⟨Y', T, j, J, b, C, ε, hYeq, _hjeq, _hJeq, _hspeed,
    hY', hT, _hj, _hJ, _hJδ, _hb, _hC, _hε, hsolve⟩ := hfamily δ hδ hδδ
  have heq : Y' = Y := by rw [hYeq]; dsimp only [δ]; field_simp; ring
  rw [heq] at hY' hsolve
  refine ⟨hδ, hδδ, hY', T, hT, ?_⟩
  intro f hf hfn
  have hcp : (0 : ℝ) ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    norm_num
    positivity [B.outerRate_pos]
  obtain ⟨g, inv, hgc, hga, _hgl, _hic, _hil, _hir, _hil', hpoint⟩ := hsolve 4 le_rfl f hf hfn hcp
  refine ⟨g, hgc, hga, ?_⟩
  intro t ht
  have hp := hpoint t ht
  refine ⟨hp.1, ?_⟩
  intro U V hU hV hUR hfU x hx hgtU htV
  obtain ⟨W, Z, hW, hZ, hWR, hfW, z, hz, u, v, hu, hv, _hui, _hvi, hhit, _hw, _hd, _hjac⟩ := hp.2.2.2.2.2
  have hgu : g t ∈ Icc 0 U := ⟨hp.1.le, hgtU⟩
  have htv : t ∈ Icc 0 V := ⟨hT.trans ht.le, htV⟩
  have huW : g t ∈ Icc 0 W := by rw [← hu]; exact u.property
  have hvZ : t ∈ Icc 0 Z := by rw [← hv]; exact v.property
  have ho := hz.horizon_overlap hW hZ hWR hU hV hUR hc hi hrc hr0 le_rfl hfW hfU hx huW hgu hvZ htv
  have hh : z.1 ⟨g t, huW⟩ ⟨t, hvZ⟩ 0 = Y := by
    rw [show (⟨g t, huW⟩ : Icc 0 W) = u from Subtype.ext hu.symm,
      show (⟨t, hvZ⟩ : Icc 0 Z) = v from Subtype.ext hv.symm]
    exact hhit
  rw [intervalExtension_apply, intervalExtension_apply, projIcc_of_mem hU hgu, projIcc_of_mem hV htv]
  exact (congrArg (fun q : WaveVector => q 0) ho.1).symm.trans hh

-- The logarithmic phase has a width-independent positive Jacobian and a uniform L2 time-change bound.
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    ∃ δ₀ α β η : ℝ, 0 < δ₀ ∧ 0 < α ∧ 0 < β ∧ 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ Y T : ℝ, Y = B.event - α * δ ∧
        Y ∈ Ioo B.inner B.event ∧ 0 ≤ T ∧
        ∀ (f : ℝ → ℝ) (_hf : MemLp f 4 (volume.restrict (Icc 0 δ))),
          (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ioi T) ∧
            (∀ t ∈ Ioi T, 0 < g t ∧ DifferentiableAt ℝ g t ∧
              β * δ ≤ g t * Real.exp (B.outerRate * t) ∧
              g t * Real.exp (B.outerRate * t) ≤ 3 * δ / 16 ∧ η ≤ -deriv g t / g t) ∧
            ∀ (ℓ : ℝ) (P : ℝ →ᵇ ℝ), Integrable (fun t => P t ^ 2) →
              ∀ l S : ℝ, T < l → l ≤ S →
                (∫ t in l..S, P (ℓ - Real.log (g t)) ^ 2) ≤ (∫ t, P t ^ 2) / η := by
  obtain ⟨δ₀, α, β, η, hδ₀, _hδ₀r, hα, hβ, hη, hfamily⟩ :=
    B.exists_outer_arrival_family hs hH hdH hdHR hc hb hrc hrb hrd hrdec hOut
      le_rfl B.outerRate_pos hs.le hA
  refine ⟨δ₀, α, β, η, hδ₀, hα, hβ, hη, ?_⟩
  intro δ hδ hδδ
  obtain ⟨Y, T, j, J, b, C, ε, hYeq, hjeq, hJeq, hηb,
    hY, hT, _hj, _hJ, _hJδ, _hb, _hC, _hε, hsolve⟩ := hfamily δ hδ hδδ
  refine ⟨Y, T, hYeq, hY, hT, ?_⟩
  intro f hf hfn
  have hcp : (0 : ℝ) ≤ B.outerRate * (1 - 1 / (4 : ℝ≥0∞).toReal) := by
    norm_num
    positivity [B.outerRate_pos]
  obtain ⟨g, inv, hgc, _hga, _hgl, _hic, _hil, _hir, _hil', hpoint⟩ := hsolve 4 le_rfl f hf hfn hcp
  have hdiff (t : ℝ) (ht : t ∈ Ioi T) : DifferentiableAt ℝ g t := by
    obtain ⟨W, Z, hW, hZ, hWR, hfW, z, hz, u, v, _hu, _hv, _hui, _hvi, _hr, _hw, hd, _hjac⟩ :=
      (hpoint t ht).2.2.2.2.2
    exact hd.differentiableAt
  have hspeed (t : ℝ) (ht : t ∈ Ioi T) : η ≤ -deriv g t / g t := hηb.trans (hpoint t ht).2.2.2.1
  refine ⟨g, hgc, fun t ht => ⟨(hpoint t ht).1, hdiff t ht,
    by simpa only [hjeq] using (hpoint t ht).2.1,
    by simpa only [hJeq] using (hpoint t ht).2.2.1, hspeed t ht⟩, ?_⟩
  intro ℓ P hP l S hl hlS
  have hsub : Icc l S ⊆ Ioi T := fun _ ht => hl.trans_le ht.1
  have hphase (t : ℝ) (ht : t ∈ Icc l S) :
      HasDerivAt (fun w => ℓ - Real.log (g w)) (-deriv g t / g t) t := by
    simpa only [neg_div] using ((hdiff t (hsub ht)).hasDerivAt.log (hpoint t (hsub ht)).1.ne').const_sub ℓ
  exact timeChange_l2_bound hlS hη
    (continuousOn_const.sub ((hgc.mono hsub).log (fun t ht => (hpoint t (hsub ht)).1.ne')))
    hphase (fun t ht => hspeed t (hsub ht)) P.continuous hP

end OuterArrivalFamily

section OuterPhaseFamily

-- Every sufficiently near-event radius has the exact affine phase, also at p = infinity.
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    let cν := Real.exp (∫ t in Ioi 0,
      2 * horizonK (r t) (horizonMass B.mass h t) B.charge B.cosmological - B.outerRate)
    ∃ δ₀ α : ℝ, 0 < δ₀ ∧ 0 < α ∧
      ∀ Y ∈ Ico (B.event - α * δ₀) B.event,
        let δ := (B.event - Y) / α
        0 < δ ∧ δ ≤ δ₀ ∧ Y ∈ Ioo B.inner B.event ∧
          ∃ T : ℝ, ∃ τ : Ioi (0 : ℝ) → ℝ, 0 < T ∧ (∀ ε, T ≤ τ ε) ∧
            ∀ (f : ℝ → ℝ), MemLp f ∞ (volume.restrict (Icc 0 δ)) →
              (eLpNorm f ∞ (volume.restrict (Icc 0 δ))).toReal ≤ A →
              ∃ g : ℝ → ℝ, ContinuousOn g (Ici T) ∧ StrictAntiOn g (Ici T) ∧
                (∀ t ∈ Ici T, 0 < g t ∧ DifferentiableAt ℝ g t) ∧
                ∀ ℓ : ℝ,
                  let E := fun t => ℓ - Real.log (g t) -
                    (B.outerRate * t + ℓ + Real.log cν - Real.log (B.z Y))
                  (∀ ε : Ioi (0 : ℝ), ∀ t ≥ τ ε,
                    |E t| + |-deriv g t / g t - B.outerRate| < ε) ∧
                  Tendsto (fun t => |E t| + |-deriv g t / g t - B.outerRate|) atTop (𝓝 0) := by
  intro cν
  obtain ⟨δ₀, α, β, η, hδ₀, _hδ₀r, hα, _hβ, _hη, hfamily⟩ :=
    B.exists_outer_phase_family hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ₀, α, hδ₀, hα, ?_⟩
  intro Y hY δ
  have hδ : 0 < δ := div_pos (sub_pos.2 hY.2) hα
  have hδδ : δ ≤ δ₀ := (div_le_iff₀ hα).2 (by linarith only [hY.1])
  obtain ⟨Y', T, τ, hYeq, hY', hT, hτ, hsolve⟩ := hfamily δ hδ hδδ
  have heq : Y' = Y := by rw [hYeq]; dsimp only [δ]; field_simp; ring
  rw [heq] at hY' hsolve
  refine ⟨hδ, hδδ, hY', T, τ, hT, hτ, ?_⟩
  intro f hf hfn
  obtain ⟨g, hgc, hga, _hgl, hpoint⟩ := hsolve ∞ (by simp) f hf hfn
  refine ⟨g, hgc, hga, fun t ht => ⟨(hpoint t ht).1.1, (hpoint t ht).2.1⟩, ?_⟩
  intro ℓ E
  have hbound (ε : Ioi (0 : ℝ)) (t : ℝ) (ht : τ ε ≤ t) :
      |E t| + |-deriv g t / g t - B.outerRate| < ε := by
    have hpt := hpoint t ((hτ ε).trans ht)
    have he : E t = Real.log (B.z Y / (g t * (cν * Real.exp (B.outerRate * t)))) := by
      rw [Real.log_div (B.z_pos hY').ne' (mul_pos hpt.1.1 (mul_pos (Real.exp_pos _) (Real.exp_pos _))).ne',
        Real.log_mul hpt.1.1.ne' (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne',
        Real.log_mul (Real.exp_pos _).ne' (Real.exp_ne_zero _)]
      dsimp only [E]
      simp only [cν, Real.log_exp]
      ring
    rw [he]
    exact hpt.2.2.2.2.2.2.1 ε ht
  refine ⟨hbound, Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  refine ⟨τ ⟨ε, hε⟩, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (add_nonneg (abs_nonneg (E t)) (abs_nonneg _))]
  exact hbound ⟨ε, hε⟩ t ht

-- A cutoff selected before the p = 4 data gives the near-background half-line Jacobian.
example (B : Background) {s H dH A : ℝ}
    (hs : 0 < s) (hH : 0 ≤ H) (hdH : 0 ≤ dH) (hdHR : dH < B.event) (hA : 0 ≤ A)
    {h r : ℝ → ℝ} (hc : Continuous h) (hb : ∀ t, ‖h t‖ ≤ H * Real.exp (-s * t))
    (hrc : Continuous r) (hrb : ∀ t, B.event - dH ≤ r t) (hrinit : B.inner < r 0)
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass B.mass h t) B.charge B.cosmological) (Ici 0) t)
    (hrdec : ∀ t ∈ Ici (0 : ℝ), ‖r t - B.event‖ ≤ dH * Real.exp (-(2 * s) * t))
    (hOut : B.OutgoingEstimates h r s) :
    ∃ δ₀ α : ℝ, 0 < δ₀ ∧ 0 < α ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ Y L : ℝ, Y = B.event - α * δ ∧
        Y ∈ Ioo B.inner B.event ∧ 0 < L ∧
        ∀ (f : ℝ → ℝ), MemLp f 4 (volume.restrict (Icc 0 δ)) →
          (eLpNorm f 4 (volume.restrict (Icc 0 δ))).toReal ≤ A →
          ∃ g : ℝ → ℝ, ContinuousOn g (Ici L) ∧
            (∀ t ∈ Ici L, 0 < g t ∧ B.outerRate / 2 ≤ -deriv g t / g t) ∧
            ∀ (ℓ : ℝ) (P : ℝ →ᵇ ℝ), Integrable (fun t => P t ^ 2) →
              ∀ l : ℝ, L ≤ l →
                MemLp (fun t => P (ℓ - Real.log (g t))) 2 (volume.restrict (Ici l)) ∧
                (∫ t in Ici l, P (ℓ - Real.log (g t)) ^ 2) ≤ (2 / B.outerRate) * ∫ t, P t ^ 2 := by
  obtain ⟨δ₀, α, β, η, hδ₀, _hδ₀r, hα, _hβ, _hη, hfamily⟩ :=
    B.exists_outer_phase_family hs hH hdH hdHR hA hc hb hrc hrb hrinit hrd hrdec hOut
  refine ⟨δ₀, α, hδ₀, hα, ?_⟩
  intro δ hδ hδδ
  obtain ⟨Y, T, τ, hYeq, hY, hT, hτ, hsolve⟩ := hfamily δ hδ hδδ
  let ε : Ioi (0 : ℝ) := ⟨B.outerRate / 2, half_pos B.outerRate_pos⟩
  let L := τ ε
  have hTL : T ≤ L := hτ ε
  refine ⟨Y, L, hYeq, hY, hT.trans_le hTL, ?_⟩
  intro f hf hfn
  obtain ⟨g, hgc, _hga, _hgl, hpoint⟩ := hsolve 4 le_rfl f hf hfn
  have hspeed (t : ℝ) (ht : L ≤ t) : B.outerRate / 2 ≤ -deriv g t / g t := by
    have hpt := hpoint t (hTL.trans ht)
    have hh := hpt.2.2.2.2.2.2.1 ε ht
    have hsp := (le_add_of_nonneg_left (abs_nonneg _)).trans_lt hh
    have hlo := (abs_lt.1 hsp).1
    change -(B.outerRate / 2) < -deriv g t / g t - B.outerRate at hlo
    linarith only [hlo]
  refine ⟨g, hgc.mono (Ici_subset_Ici.2 hTL),
    fun t ht => ⟨(hpoint t (hTL.trans ht)).1.1, hspeed t ht⟩, ?_⟩
  intro ℓ P hP l hl
  have hsub : Ici l ⊆ Ici T := Ici_subset_Ici.2 (hTL.trans hl)
  have hphase (t : ℝ) (ht : t ∈ Ici l) :
      HasDerivAt (fun w => ℓ - Real.log (g w)) (-deriv g t / g t) t := by
    have hpt := hpoint t (hsub ht)
    simpa only [neg_div] using (hpt.2.1.hasDerivAt.log hpt.1.1.ne').const_sub ℓ
  have hh := timeChange_l2_halfline (half_pos B.outerRate_pos)
    (continuousOn_const.sub ((hgc.mono hsub).log (fun t ht => (hpoint t (hsub ht)).1.1.ne')))
    hphase (fun t ht => hspeed t (hl.trans ht)) P.continuous hP
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  field_simp

end OuterPhaseFamily

end CauchyHorizon.Tests
