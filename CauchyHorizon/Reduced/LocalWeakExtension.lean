import CauchyHorizon.Reduced.RegularCrossing
import CauchyHorizon.Geometry.RegularSpacetime
import CauchyHorizon.Reduced.SphericalCausalBoundary
import CauchyHorizon.Reduced.CharacteristicCausalBoundary

/-! The same nonlinear crossing solution gives a local weak extension at every horizon point. -/

open Set MeasureTheory
open scoped Manifold

namespace CauchyHorizon

def HasSphericalWeakSolution {W L : ℝ} (hW : 0 ≤ W) (hL : 0 ≤ L)
    (e Λ : ℝ) (y : WaveState W L) : Prop :=
  (∀ t s, 0 < y.1 t s 0) ∧ HasL2CoordinateMetric hW hL y ∧
    HasL2CoordinateConnection hW hL y ∧ HasSphericalConnectionTransition hW hL y ∧
    HasSphericalFieldEquations hW hL e Λ y

def HasLocalSphericalWeakExtension {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U) (e Λ : ℝ)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ) (T₀ u₀ : ℝ) : Prop :=
  let a := anchoringLapse (hε.trans hεU) X
  let V := regularTime a
  IsRegularTimeCoordinate a 0 χ ∧
  ∃ ua L T b : ℝ, ε < ua ∧ ua < u₀ ∧ u₀ < ua + L ∧ ua + L < U ∧
    T₀ ≤ T ∧ 0 < T ∧ V T < 0 ∧ 0 < b ∧
    ∃ hL : 0 ≤ L, ∃ hW : 0 ≤ b - V T, ∃ y : WaveState (b - V T) L,
      HasSphericalWeakSolution hW hL e Λ y ∧
      V '' Ioi T = Ioo (V T) 0 ∧
      ∃ E : OpenPartialHomeomorph ((ℝ × ℝ) × UnitSphere) ((ℝ × ℝ) × UnitSphere),
      IsRegularSpacetimeEmbedding a χ T ua (ua + L) E ∧
      E.target ⊆ (Ioo (V T) b ×ˢ Ioo ua (ua + L)) ×ˢ univ ∧
      (∀ p : UnitSphere, ((0, u₀), p) ∈ frontier E.target) ∧
      HasSphericalCauchyHorizon hW hL y (V T) ua E.target ∧
      HasCharacteristicCauchyHorizon (hε.trans hεU) X hW hL y (V T) ua ∧
      (∀ p : UnitSphere, ∃ A : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient,
        ∃ c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ), ∃ δ : ℝ,
        IsSphericalSolutionChart hW hL e Λ y p A c δ ∧
        let C := sphericalRectangleChart (b - V T) L (2 * δ) (2 * δ) (V T, ua)
          (Real.pi / 2 - δ, Real.pi / 2 - δ) c
        C.target = openRectangleProduct (b - V T) L (2 * δ) (2 * δ) ∧
        ((0, u₀), p) ∈ C.source ∧
        C ((0, u₀), p) = ((-V T, u₀ - ua), (δ, δ)) ∧
        ∀ v ∈ Ioo (V T) b, ((v, u₀), p) ∈ C.source) ∧
      ∀ (S : Ici (0 : ℝ)) (t : ℝ), T < t → t ≤ S → ∀ s : Icc 0 L,
        let z := y.1 (projIcc 0 (b - V T) hW (V t - V T)) s
        let x := (X S).1 (projIcc 0 U (hε.trans hεU) (ua + s))
          (projIcc 0 (S : ℝ) S.property t)
        z = x - (fun i => if i = 2 then
          (X S).1 ⟨U, hε.trans hεU, le_rfl⟩ (projIcc 0 (S : ℝ) S.property t) 2 else 0) ∧
        Real.exp (z 2) * a t = Real.exp (x 2) ∧
        ∀ (p : UnitSphere) (ξ η : (ℝ × ℝ) × TangentSpace (𝓡 2) p),
          let d := mfderiv (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 2))
            E ((t, ua + s), p)
          sphereSpacetimeMetric (Real.exp (z 2)) (z 0 ^ 2) p (d ξ) (d η) =
              sphereSpacetimeMetric (Real.exp (x 2)) (x 0 ^ 2) p ξ η ∧
            sphereElectricForm (e * Real.exp (z 2) / (2 * z 0 ^ 2)) p ![d ξ, d η] =
              sphereElectricForm (e * Real.exp (x 2) / (2 * x 0 ^ 2)) p ![ξ, η]

theorem HasRegularCrossingSolution.local_weak_extension {U ε e Λ T₀ u₀ : ℝ}
    {hε : 0 ≤ ε} {hεU : ε ≤ U} {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    {Z : C(Icc ε U, WaveVector)} {O : C(Icc ε U, ℝ)}
    {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hrX : ∀ (S : Ici (0 : ℝ)) u v, 0 < (X S).1 u v 0)
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh) :
    HasLocalSphericalWeakExtension hε hεU e Λ X χ T₀ u₀ := by
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  obtain ⟨ua, L, T, b, hea, ham, hmr, hrU, hT₀, hT, hn, hb,
    hL, hW, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, _hfuture, _hout, _hxin, _hbottom,
    hr, hmatch, _hvelocity, _hc, _hi, _hweak, _hdistribution, _hL2, _hmetric, hcoord, hconnection,
    _hRicci, _hsource, _hmixed, _hangular, _hoffdiag, _hmaxwell, _heinstein, _hscalar, _hsphere,
    htransition, hfields, _rest⟩ := hcross
  refine ⟨hχ, ua, L, T, b, hea, ham, hmr, hrU, hT₀, hT, hn, hb, hL, hW, y,
    ⟨hr, hcoord, hconnection, htransition, hfields⟩, hχ.late_image hT.le,
    regularSpacetimeEmbedding hχ hT.le ua (ua + L), regularSpacetimeEmbedding_spec hχ hT.le ua (ua + L),
    (fun _ hw => ⟨⟨⟨hw.1.1.1, hw.1.1.2.trans hb⟩, hw.1.2⟩, hw.2⟩),
    regularSpacetimeEmbedding_frontier hχ hT.le ⟨ham, hmr⟩, ?_, ?_, ?_, ?_⟩
  · exact crossing_spherical_cauchy_horizon y hn (by linarith) (by linarith)
  · exact crossing_characteristic_cauchy_horizon hε hεU hW hL X y hX hrX hχ hB
      (hχ.2.2.2.1 hT) hn (by linarith) hea (by linarith) hrU hr
      (fun t ht s => (hmatch t ht s).1)
  · intro p
    obtain ⟨A, c, δ, hsolution⟩ := hfields p
    refine ⟨A, c, δ, hsolution, ?_⟩
    obtain ⟨hδ, _hδπ, hp, hcenter, _hparam, _hc, _hci, hbox, _hsource, _hmatter⟩ := hsolution
    have hchart := sphericalRectangleChart_null_line (vT := V T) (b := b) hδ ham hmr c hp hcenter hbox
    refine ⟨hchart.1, hchart.2 0 ⟨hn, hb⟩, ?_, hchart.2⟩
    simp only [sphericalRectangleChart_apply, hcenter, Prod.sub_def, zero_sub]
    congr 2 <;> ring
  · intro S t ht htS s
    have ht0 : 0 < t := hT.trans ht
    have hvt : 0 ≤ V t - V T := sub_nonneg.2 (hχ.2.2.2.1 ht).le
    have hvtW : V t - V T ≤ b - V T := sub_le_sub_right ((hχ.2.2.2.2.2.1 t).le.trans hb.le) _
    have htproj := projIcc_of_mem S.property (show t ∈ Icc 0 (S : ℝ) from ⟨ht0.le, htS⟩)
    have hu : ua + (s : ℝ) ∈ Icc ε U :=
      ⟨hea.le.trans (le_add_of_nonneg_right s.property.1),
        by linarith [s.property.2]⟩
    have hu0 : ua + (s : ℝ) ∈ Icc 0 U := ⟨hε.trans hu.1, hu.2⟩
    have he := (hmatch ⟨V t - V T, hvt, hvtW⟩
      (by change V T + (V t - V T) ≤ 0; linarith [hχ.2.2.2.2.2.1 t]) s).1
    have hsum : V T + (V t - V T) = V t := by ring
    change y.1 ⟨V t - V T, hvt, hvtW⟩ s =
      compactifiedWaveRow hε hεU X χ Z (V T + (V t - V T)) (projIcc ε U hεU (ua + s)) at he
    rw [hsum, projIcc_of_mem hεU hu] at he
    rw [hB.1 S t ht0 htS ⟨ua + s, hu⟩] at he
    have ha : anchoringLapse (hε.trans hεU) X t =
        Real.exp ((X S).1 ⟨U, hε.trans hεU, le_rfl⟩ ⟨t, ht0.le, htS⟩ 2) := by
      unfold anchoringLapse
      rw [max_eq_right ht0.le, renormalizedWaveRow_apply (hε.trans hεU) X hX S ht0.le htS]
      simp
    dsimp only
    rw [projIcc_of_mem hW ⟨hvt, hvtW⟩, htproj,
      projIcc_of_mem (hε.trans hεU) hu0]
    have hExp : Real.exp (y.1 ⟨V t - V T, hvt, hvtW⟩ s 2) *
        anchoringLapse (hε.trans hεU) X t =
          Real.exp ((X S).1 ⟨ua + s, hu0⟩ ⟨t, ht0.le, htS⟩ 2) := by
      rw [he, Pi.sub_apply, if_pos rfl, ha, ← Real.exp_add]
      congr 1
      ring
    refine ⟨he, hExp, ?_⟩
    intro p ξ η
    have hradius : y.1 ⟨V t - V T, hvt, hvtW⟩ s 0 =
        (X S).1 ⟨ua + s, hu0⟩ ⟨t, ht0.le, htS⟩ 0 := by simpa using congrFun he (0 : Fin 3)
    simp only [regularSpacetimeEmbedding_mfderiv]
    rw [hradius]
    refine ⟨sphereSpacetimeMetric_time_change hExp p ξ η, ?_⟩
    apply sphereElectricForm_time_change
    calc
      _ = e * (Real.exp (y.1 ⟨V t - V T, hvt, hvtW⟩ s 2) *
          anchoringLapse (hε.trans hεU) X t) / (2 * (X S).1 ⟨ua + s, hu0⟩ ⟨t, ht0.le, htS⟩ 0 ^ 2) := by ring
      _ = _ := by rw [hExp]

end CauchyHorizon
