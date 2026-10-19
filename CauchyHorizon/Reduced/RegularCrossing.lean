import CauchyHorizon.Reduced.RegularContinuationBounds
import CauchyHorizon.Reduced.IntegralRegularity
import CauchyHorizon.Analysis.IntervalRebase
import CauchyHorizon.Reduced.RegularOverlap
import CauchyHorizon.Reduced.RegularConstraint
import CauchyHorizon.Reduced.LongitudinalConstraint
import CauchyHorizon.Reduced.IncomingConstraintRebase
import CauchyHorizon.Reduced.GeneralRadialConstraint
import CauchyHorizon.Reduced.WeakFirstDerivative
import CauchyHorizon.Reduced.MetricCoefficients
import CauchyHorizon.Reduced.CoordinateMetric
import CauchyHorizon.Reduced.CoordinateConnection
import CauchyHorizon.Reduced.CoordinateRicci
import CauchyHorizon.Reduced.NullRicciSources
import CauchyHorizon.Reduced.MixedRicciSources
import CauchyHorizon.Reduced.AngularRicciSources
import CauchyHorizon.Reduced.OffDiagonalRicciSources
import CauchyHorizon.Reduced.EinsteinEquation
import CauchyHorizon.Reduced.ScalarDivergence
import CauchyHorizon.Reduced.SphericalEinstein
import CauchyHorizon.Reduced.SphericalConnection
import CauchyHorizon.Reduced.SphericalMatter

/-! A positive-radius nonlinear solution on a rectangle crossing regular time zero. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

def HasRegularCrossingSolution {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (e Λ : ℝ)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector)) (T₀ u₀ : ℝ) : Prop :=
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let W := compactifiedTransverseRow χ D Dh
  ∃ ua L T b : ℝ, ε < ua ∧ ua < u₀ ∧ u₀ < ua + L ∧ ua + L < U ∧
    T₀ ≤ T ∧ 0 < T ∧ V T < 0 ∧ 0 < b ∧
    ∃ hL : 0 ≤ L, ∃ hV : 0 ≤ b - V T,
    ∃ zIn : C(Icc 0 (b - V T), WaveVector), ∃ vOut : C(Icc 0 L, WaveVector),
    ∃ uIn : Lp WaveVector 2 (volume.restrict (Icc 0 (b - V T))),
    ∃ y : WaveState (b - V T) L,
      IsWaveIntegral hV hL e Λ zIn vOut uIn y ∧
      zIn = ContinuousMap.const (Icc 0 (b - V T)) (Ψ (V T) (projIcc ε U hεU ua)) +
        horizontalPrimitive hV uIn ∧
      (∀ t : Icc 0 (b - V T), V T + (t : ℝ) ≤ 0 → zIn t = Ψ (V T + t) (projIcc ε U hεU ua)) ∧
      (∀ t : Icc 0 (b - V T), 0 ≤ V T + (t : ℝ) → zIn t = Ψ 0 (projIcc ε U hεU ua) +
        (V T + t) • radialHorizonVelocity hεU Z O (projIcc ε U hεU ua)) ∧
      (∀ s, vOut s = W (V T) (projIcc ε U hεU (ua + s))) ∧
      (∀ t, y.1 t ⟨0, le_rfl, hL⟩ = zIn t) ∧
      (∀ s, y.1 ⟨0, le_rfl, hV⟩ s = Ψ (V T) (projIcc ε U hεU (ua + s))) ∧
      (∀ t s, 0 < y.1 t s 0) ∧
      (∀ t : Icc 0 (b - V T), V T + (t : ℝ) ≤ 0 → ∀ s,
        y.1 t s = Ψ (V T + t) (projIcc ε U hεU (ua + s)) ∧
        y.2.1 t s = W (V T + t) (projIcc ε U hεU (ua + s))) ∧
      (∀ A : ℝ, 0 < A → V T + A < 0 →
        ∀ ht : 0 + A ≤ b - V T, ∀ hs : 0 + L ≤ L,
        ∀ᵐ t ∂volume.restrict (Icc 0 A), ∀ s : Icc 0 L,
          transverseTranslate (a := 0) (b := 0) le_rfl ht le_rfl hs y.2.2 t s =
            waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ (V T + t))
              (projIcc ε U hεU (ua + s))) ∧
      (∀ t s, HasDerivWithinAt (fun x => intervalExtension hL (y.2.1 t) x 0)
        (y.2.1 t s 2 * y.2.1 t s 0 - y.1 t s 0 * (y.2.1 t s 1) ^ 2) (Icc 0 L) s) ∧
      (∀ t s, y.2.1 t s 0 * Real.exp (-y.1 t s 2) =
        y.2.1 t ⟨0, le_rfl, hL⟩ 0 * Real.exp (-y.1 t ⟨0, le_rfl, hL⟩ 2) -
          ∫ x in (0 : ℝ)..(s : ℝ), intervalExtension hL (y.1 t) x 0 *
            Real.exp (-intervalExtension hL (y.1 t) x 2) * (intervalExtension hL (y.2.1 t) x 1) ^ 2) ∧
      HasWeakWaveEquation hV hL e Λ y ∧
      HasDistributionalWaveEquation hV hL e Λ y ∧
      HasL2WaveDerivatives hV hL y ∧
      HasL2MetricCoefficients hV hL y ∧
      HasL2CoordinateMetric hV hL y ∧
      HasL2CoordinateConnection hV hL y ∧
      HasCoordinateRicci hV hL y ∧
      HasNullRicciSources hV hL y ∧
      HasMixedRicciSources hV hL e Λ y ∧
      HasAngularRicciSources hV hL e Λ y ∧
      HasOffDiagonalRicciSources hV hL y ∧
      HasCoordinateMaxwell hV hL e y ∧
      HasCoordinateEinsteinEquation hV hL e Λ y ∧
      HasCoordinateScalarEquation hV hL y ∧
      HasSphericalRicci hV hL e Λ y ∧
      HasSphericalConnectionTransition hV hL y ∧
      HasSphericalFieldEquations hV hL e Λ y ∧
      ∃ N : C(Icc 0 (b - V T), C(Icc 0 L, ℝ)),
        (∀ᵐ t ∂volume.restrict (Icc 0 (b - V T)), ∀ s,
          y.2.2 t s 0 = N (projIcc 0 (b - V T) hV t) s) ∧
        (∀ t s, HasDerivWithinAt (fun x => intervalExtension hV y.1 x s 0)
          (N t s) (Icc 0 (b - V T)) t) ∧
        (∀ᵐ t ∂volume.restrict (Icc 0 (b - V T)), ∀ s,
          HasDerivWithinAt (fun x => intervalExtension hV N x s)
            (y.2.2 t s 2 * N (projIcc 0 (b - V T) hV t) s -
              y.1 (projIcc 0 (b - V T) hV t) s 0 * (y.2.2 t s 1) ^ 2) (Icc 0 (b - V T)) t) ∧
        ∀ s, AbsolutelyContinuousOnInterval (fun t => intervalExtension hV N t s *
            Real.exp (-intervalExtension hV y.1 t s 2)) 0 (b - V T) ∧
          IntervalIntegrable (fun t => intervalExtension hV y.1 t s 0 *
            Real.exp (-intervalExtension hV y.1 t s 2) * (y.2.2 t s 1) ^ 2) volume 0 (b - V T) ∧
          ∀ t, N t s * Real.exp (-y.1 t s 2) =
            N ⟨0, le_rfl, hV⟩ s * Real.exp (-y.1 ⟨0, le_rfl, hV⟩ s 2) -
              ∫ x in (0 : ℝ)..(t : ℝ), intervalExtension hV y.1 x s 0 *
                Real.exp (-intervalExtension hV y.1 x s 2) * (y.2.2 x s 1) ^ 2

set_option maxHeartbeats 1000000 in
theorem exists_regular_crossing_solution {U ε ρ T₀ u₀ : ℝ}
    (hε : 0 ≤ ε) (hεU : ε ≤ U) (e Λ : ℝ) (hρ : 0 < ρ)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (O : C(Icc ε U, ℝ))
    {χ : ℝ → ℝ} (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh)
    (hE : IsRegularWaveEvolution hε hεU e Λ X χ Z D Dh)
    (hC : IsRegularSpatialConstraint hε hεU X χ Z D Dh)
    (hQ : ContinuousOn (regularWaveVelocityRow hε hεU X χ)
      (Ioo (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0))
    (hr : ∀ (S : Ici (0 : ℝ)) u v, 0 < (X S).1 u v 0)
    (hdata : HasBoundedRegularContinuationData hε hεU X χ Z O D Dh ρ T₀)
    (hu₀ : u₀ ∈ Ioo ε U) :
    HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀ := by
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let W := compactifiedTransverseRow χ D Dh
  obtain ⟨b₀, R, M, hb₀, hR, hM, hdata, hbound⟩ := hdata
  obtain ⟨δ, _hδ, hδr, d, hd, _hd1, hlocal⟩ :=
    exists_local_wave_integral e Λ (ρ / 2) R M (half_pos hρ) hR.le hM.le
  let b := min b₀ (d / 4)
  have hb : 0 < b := lt_min hb₀ (by positivity)
  have hbb : b ≤ b₀ := min_le_left _ _
  have hbd : b ≤ d / 4 := min_le_right _ _
  let η := min ((u₀ - ε) / 2) (min ((U - u₀) / 2) (d / 4))
  have hη : 0 < η := lt_min (by linarith [hu₀.1]) (lt_min (by linarith [hu₀.2]) (by positivity))
  have hηl : η ≤ (u₀ - ε) / 2 := min_le_left _ _
  have hηr : η ≤ (U - u₀) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηd : η ≤ d / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let ua := u₀ - η
  let L := 2 * η
  have hleft : ε < ua := by dsimp only [ua]; linarith [hu₀.1]
  have hmid : ua < u₀ ∧ u₀ < ua + L := by dsimp only [ua, L]; constructor <;> linarith
  have hright : ua + L < U := by dsimp only [ua, L]; linarith [hu₀.2]
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hLd : L ≤ d := by dsimp only [L]; linarith
  have htend : Tendsto V atTop (𝓝 (0 : ℝ)) :=
    hχ.2.2.2.2.2.2.1.mono_right nhdsWithin_le_nhds
  obtain ⟨T, hT, hVT⟩ := ((eventually_ge_atTop (max T₀ 1)).and
    (htend.eventually_const_lt (by linarith : -(d / 2) < (0 : ℝ)))).exists
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hT)
  have hVneg : V T < 0 := hχ.2.2.2.2.2.1 T
  have hVb : V T ≤ b := hVneg.le.trans hb.le
  have hV : 0 ≤ b - V T := sub_nonneg.2 hVb
  have hVd : b - V T ≤ d := by linarith
  obtain ⟨z, dz, hz, hfloor, _habData, hincomingConstraint⟩ := hdata T hT₀ hTpos
  obtain ⟨d', hd'ae, hd'norm, _hznorm, hprim⟩ :=
    rebase_characteristic_data hVb hbb z dz hz.1.choose_spec
  let uA : Icc ε U := ⟨ua, hleft.le, by linarith [hright, hL]⟩
  let ev : C(Icc ε U, WaveVector) →L[ℝ] WaveVector := ContinuousMap.evalCLM ℝ uA
  let zIn := ContinuousLinearMap.compLeftContinuous ℝ (Icc 0 (b - V T)) ev
    (z.comp (intervalRebase hbb))
  let uIn := ev.compLpL 2 (volume.restrict (Icc 0 (b - V T))) d'
  obtain ⟨n, hn, hnAC, hnd⟩ := hincomingConstraint.rebase hVb hbb hd'ae uA
  let ι : C(Icc 0 L, Icc ε U) := ⟨fun s => ⟨ua + s,
    hleft.le.trans (le_add_of_nonneg_right s.property.1),
    (add_le_add_right s.property.2 ua).trans hright.le⟩, by fun_prop⟩
  let vOut := (W (V T)).comp ι
  let bottom := (Ψ (V T)).comp ι
  have huA : projIcc ε U hεU ua = uA := projIcc_of_mem hεU uA.property
  have hι (s : Icc 0 L) : projIcc ε U hεU (ua + s) = ι s :=
    projIcc_of_mem hεU (ι s).property
  have hzIn : zIn = ContinuousMap.const _ (Ψ (V T) uA) + horizontalPrimitive hV uIn := by
    dsimp only [zIn, uIn]
    rw [hprim, map_add, horizontalPrimitive_compLp]
    rfl
  have hev : ‖ev‖ ≤ 1 := ev.opNorm_le_bound zero_le_one (fun f => by
    change ‖f uA‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using f.norm_coe_le_norm uA)
  have hzR : ‖zIn‖ ≤ R := (ContinuousMap.norm_le _ hR.le).2 (fun t =>
    ((z (intervalRebase hbb t)).norm_coe_le_norm uA).trans
      ((z.norm_coe_le_norm _).trans ((hbound T hT).2 z dz hz).1))
  have hvR : ‖vOut‖ ≤ R := (ContinuousMap.norm_le _ hR.le).2 (fun s =>
    ((W (V T)).norm_coe_le_norm (ι s)).trans (hbound T hT).1)
  have huM : ‖uIn‖ ≤ M := (ev.norm_compLp_le d').trans
    ((mul_le_mul_of_nonneg_right hev (norm_nonneg d')).trans (by
      simpa only [one_mul] using hd'norm.trans ((hbound T hT).2 z dz hz).2))
  have hzinr : ∀ t, ρ / 2 ≤ zIn t 0 := fun t => hfloor (intervalRebase hbb t) uA
  obtain ⟨y, ⟨hyball, hy⟩, _huniq⟩ := hlocal hV hL hVd hLd zIn vOut uIn hzinr hzR hvR huM
  have hbottom : bottom = ContinuousMap.const _ (Ψ (V T) uA) + continuousPrimitive hL vOut := by
    have hder (s : Icc 0 L) :
        HasDerivWithinAt (intervalExtension hL bottom) (vOut s) (Icc 0 L) s := by
      have hmem : V T ∈ Ioc (V 0) 0 := ⟨hχ.2.2.2.1 hTpos, hVneg.le⟩
      have hi : ε < ua + (s : ℝ) ∧ ua + (s : ℝ) < U :=
        ⟨hleft.trans_le (le_add_of_nonneg_right s.property.1),
          (add_le_add_right s.property.2 ua).trans_lt hright⟩
      have hh := (hB.2.2.2.2 (V T) hmem (ι s)).hasDerivAt (Icc_mem_nhds hi.1 hi.2)
      change HasDerivAt (intervalExtension hεU (Ψ (V T))) (vOut s) (ua + (s : ℝ)) at hh
      have hc := hh.scomp (s : ℝ) ((hasDerivAt_id (s : ℝ)).const_add ua)
      simp only [one_smul] at hc
      apply hc.hasDerivWithinAt.congr_of_mem _ s.property
      intro t ht
      simp only [intervalExtension_apply, projIcc_of_mem hL ht]
      change Ψ (V T) (ι ⟨t, ht⟩) = Ψ (V T) (projIcc ε U hεU (ua + t))
      rw [hι ⟨t, ht⟩]
    have he := (continuous_derivative_limit (l := atTop) hL
      (f := fun _ : ℕ => bottom) (d := fun _ : ℕ => vOut)
      tendsto_const_nhds tendsto_const_nhds (Eventually.of_forall fun _ => hder)).1
    simpa only [continuousPrimitiveL_apply, bottom, ContinuousMap.comp_apply,
      show ι ⟨0, le_rfl, hL⟩ = uA from Subtype.ext (add_zero ua)] using he
  have hxin (t : Icc 0 (b - V T)) : y.1 t ⟨0, le_rfl, hL⟩ = zIn t := by
    have hh := waveIteration_incoming_value hV hL e Λ zIn vOut uIn y hy.choose t
    rwa [hy.choose_spec] at hh
  have hyout : y.2.1 ⟨0, le_rfl, hV⟩ = vOut := by
    have hh := waveIteration_outgoing_derivative hV hL e Λ zIn vOut uIn y hy.choose
    rwa [hy.choose_spec] at hh
  have hyr (t) (s) : 0 < y.1 t s 0 := by
    have hrange := waveSeed_ball_range zIn vOut uIn hzinr hzR hvR hyball t s
    have hlow : ρ / 2 - δ ≤ y.1 t s 0 := hrange.1.1 0
    exact (sub_pos.2 hδr).trans_le hlow
  have hpast (t : Icc 0 (b - V T)) (ht : V T + (t : ℝ) ≤ 0) :
      zIn t = Ψ (V T + t) (projIcc ε U hεU ua) := by
    change z (intervalRebase hbb t) uA = _
    rw [hz.2.1 (intervalRebase hbb t) ht, huA]
    rfl
  have hout (s) : vOut s = W (V T) (projIcc ε U hεU (ua + s)) := by
    change W (V T) (ι s) = W (V T) (projIcc ε U hεU (ua + s))
    rw [hι]
  have hpref (A : ℝ) (hA : 0 < A) (haA : V T + A < 0) :=
    regular_wave_prefix_eq hε hεU hA hV hL (by linarith : A ≤ b - V T) X hχ hB hE hQ hr
      (hχ.2.2.2.1 hTpos) haA hleft hright hy hzIn hpast hout hyr
  have hmatch (t : Icc 0 (b - V T)) (ht : V T + (t : ℝ) ≤ 0) (s : Icc 0 L) :
      y.1 t s = Ψ (V T + t) (projIcc ε U hεU (ua + s)) ∧
      y.2.1 t s = W (V T + t) (projIcc ε U hεU (ua + s)) := by
    let u := projIcc ε U hεU (ua + s)
    let f := fun w : ℝ => (y.1 (projIcc 0 (b - V T) hV w) s,
      y.2.1 (projIcc 0 (b - V T) hV w) s)
    let g := fun w : ℝ => (Ψ (V T + w) u, W (V T + w) u)
    have he : EqOn f g (Ico 0 (-V T)) := by
      intro w hw
      let A := (w - V T) / 2
      have hA : 0 < A := by dsimp only [A]; linarith [hw.1]
      have hwA : w ≤ A := by dsimp only [A]; linarith [hw.2]
      have haA : V T + A < 0 := by dsimp only [A]; linarith [hw.2]
      have hwB : w ∈ Icc 0 (b - V T) := ⟨hw.1, by linarith [hw.2]⟩
      have hi : intervalTranslate (a := 0) le_rfl (by linarith : 0 + A ≤ b - V T)
          ⟨w, hw.1, hwA⟩ = projIcc 0 (b - V T) hV w := by
        rw [projIcc_of_mem hV hwB]
        exact Subtype.ext (zero_add _)
      have he := hpref A hA haA
      exact Prod.ext (by simpa only [hi] using he.1 ⟨w, hw.1, hwA⟩ s)
        (by simpa only [hi] using he.2.1 ⟨w, hw.1, hwA⟩ s)
    have hf : ContinuousOn f (Icc 0 (-V T)) := by fun_prop
    have hshift : MapsTo (fun w => V T + w) (Icc 0 (-V T)) (Ioc (V 0) 0) := by
      intro w hw
      exact ⟨(hχ.2.2.2.1 hTpos).trans_le (le_add_of_nonneg_right hw.1), by linarith [hw.2]⟩
    have hcΨ : ContinuousOn (fun w => Ψ (V T + w)) (Icc 0 (-V T)) :=
      hB.2.2.1.comp (by fun_prop) hshift
    have hcW : ContinuousOn (fun w => W (V T + w)) (Icc 0 (-V T)) :=
      hB.2.2.2.1.comp (by fun_prop) hshift
    let E : C(Icc ε U, WaveVector) →L[ℝ] WaveVector := ContinuousMap.evalCLM ℝ u
    have hg : ContinuousOn g (Icc 0 (-V T)) := by
      intro w hw
      exact (E.continuous.continuousAt.comp_continuousWithinAt (hcΨ w hw)).prodMk
        (E.continuous.continuousAt.comp_continuousWithinAt (hcW w hw))
    have hh := he.of_subset_closure hf hg Ico_subset_Icc_self
      (by rw [closure_Ico (ne_of_lt (neg_pos.2 hVneg))])
      (show (t : ℝ) ∈ Icc 0 (-V T) from ⟨t.property.1, by linarith⟩)
    change (y.1 (projIcc 0 (b - V T) hV t) s, y.2.1 (projIcc 0 (b - V T) hV t) s) = _ at hh
    rw [projIcc_of_mem hV t.property] at hh
    exact Prod.mk.inj hh
  have hconstraint : ∀ s (hs : s ∈ Icc 0 L),
      HasDerivWithinAt (fun x => intervalExtension hL vOut x 0)
        (vOut ⟨s, hs⟩ 2 * vOut ⟨s, hs⟩ 0 -
          y.1 ⟨0, le_rfl, hV⟩ ⟨s, hs⟩ 0 * (vOut ⟨s, hs⟩ 1) ^ 2) (Icc 0 L) s := by
    intro s hs
    let p : Icc 0 L := ⟨s, hs⟩
    have hi : ε < ua + s ∧ ua + s < U :=
      ⟨hleft.trans_le (le_add_of_nonneg_right hs.1),
        (add_le_add_right hs.2 ua).trans_lt hright⟩
    have hd := (hC (V T) ⟨hχ.2.2.2.1 hTpos, hVneg⟩ (ι p)).hasDerivAt
      (Icc_mem_nhds hi.1 hi.2)
    have hh := hd.comp s ((hasDerivAt_id s).const_add ua)
    simp only [mul_one] at hh
    have he := (hmatch ⟨0, le_rfl, hV⟩ (by simpa only [add_zero] using hVneg.le) p).1
    simp only [add_zero, hι] at he
    rw [he]
    apply hh.hasDerivWithinAt.congr_of_mem _ hs
    intro x hx
    simp only [Function.comp_apply, intervalExtension_apply, projIcc_of_mem hL hx]
    change W (V T) (ι ⟨x, hx⟩) 0 = W (V T) (projIcc ε U hεU (ua + x)) 0
    rw [hι ⟨x, hx⟩]
  refine ⟨ua, L, T, b, hleft, hmid.1, hmid.2, hright, hT₀, hTpos, hVneg, hb,
    hL, hV, zIn, vOut, uIn, y, hy, ?_, hpast, ?_, hout, hxin, ?_, hyr, hmatch, ?_⟩
  · simpa only [huA] using hzIn
  · intro t ht
    change z (intervalRebase hbb t) uA = _
    rw [hz.2.2.1 (intervalRebase hbb t) ht, huA]
    rfl
  · intro s
    have hh := congrArg (fun q : WaveState (b - V T) L => q.1 ⟨0, le_rfl, hV⟩ s) hy.choose_spec
    change zIn ⟨0, le_rfl, hV⟩ + continuousPrimitive hL (y.2.1 ⟨0, le_rfl, hV⟩) s = _ at hh
    rw [hyout] at hh
    have hz0 : zIn ⟨0, le_rfl, hV⟩ = Ψ (V T) uA := by
      rw [hzIn]
      change Ψ (V T) uA + (∫ t in (0 : ℝ)..0, uIn t) = _
      simp only [intervalIntegral.integral_same, add_zero]
    rw [hz0] at hh
    rw [← hh, hι]
    exact (congrArg (fun f : C(Icc 0 L, WaveVector) => f s) hbottom).symm
  · have hnull := hy.null_ricci_sources hzIn n hn hnAC hnd hconstraint
    have hEinstein := hy.coordinate_einstein_equation hzIn hnull
    have hRicci := hEinstein.spherical_ricci hy.choose
    have hMaxwell := hy.coordinate_maxwell hzIn
    have hScalar := hy.coordinate_scalar_equation hzIn
    exact ⟨fun A hA haA _ht _hs => (hpref A hA haA).2.2,
      (fun t s => hy.longitudinal_constraint hy.choose hzIn s.property (hconstraint s s.property) t),
      hy.longitudinal_constraint_integral hy.choose hzIn hconstraint,
      hy.weak_wave_equation,
      hy.distributional_wave_equation,
      hy.weak_first_derivatives hzIn,
      hy.metric_coefficients hzIn,
      hy.coordinate_metric hzIn,
      hy.coordinate_connection hzIn,
      hy.coordinate_ricci hzIn,
      hnull,
      hy.mixed_ricci_sources hzIn,
      hy.angular_ricci_sources hzIn,
      hy.off_diagonal_ricci_sources hzIn,
      hMaxwell,
      hEinstein,
      hScalar,
      hRicci,
      hy.spherical_connection_transition,
      hRicci.spherical_field_equations hEinstein hMaxwell hScalar,
      radialVelocityField hL e Λ n zIn y.1 hy.choose,
      (hy.general_radial_constraint hy.choose hzIn n hn hnd).1,
      (hy.general_radial_constraint hy.choose hzIn n hn hnd).2.1,
      (hy.general_radial_constraint hy.choose hzIn n hn hnd).2.2,
      hy.general_radial_constraint_integral hy.choose hzIn n hn hnAC hnd⟩

end CauchyHorizon
