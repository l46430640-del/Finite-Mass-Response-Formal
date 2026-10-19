import CauchyHorizon.Reduced.OriginalSpacetimeField
import CauchyHorizon.Reduced.RegularBoundary
import CauchyHorizon.Geometry.CharacteristicCauchyHorizon

/-! The original characteristic sides and the same nonlinear crossing solution in one causal region. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon

def HasCharacteristicCauchyHorizon {U W L : ℝ} (hU : 0 ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (y : WaveState W L) (va ua : ℝ) : Prop :=
  let V := regularTime (anchoringLapse hU X)
  let M := characteristicCrossingRegion (V (-1)) U va (va + W) ua (ua + L)
  let N := sphericalOpenRectangle va (va + W) ua (ua + L)
  ∃ F : SphericalSpacetime → WaveVector, ContinuousOn F M ∧
    (∀ p ∈ M, 0 < F p 0) ∧
    (∀ (S : Ici (0 : ℝ)) (t : ℝ) (ht : 0 ≤ t) (htS : t ≤ S)
        (u : Icc 0 U) (ω : UnitSphere),
      F ((V t, u), ω) = (X S).1 u ⟨t, ht, htS⟩ -
        (fun i => if i = 2 then (X S).1 ⟨U, hU, le_rfl⟩ ⟨t, ht, htS⟩ 2 else 0)) ∧
    (∀ p ∈ N, F p = crossingSpacetimeField hW hL y va ua p) ∧
    let H := fun p => Real.exp (F p 2)
    let R := fun p => F p 0 ^ 2
    N ∩ futureDomainOfDependence M H R (characteristicInitialSides (V 0) U) =
        sphericalOpenRectangle va 0 ua (ua + L) ∧
      N ∩ futureCauchyHorizon M H R (characteristicInitialSides (V 0) U) =
        ({0} ×ˢ Ioo ua (ua + L)) ×ˢ univ

theorem compactifiedWaveRow_eq_originalSpacetimeField {U ε : ℝ}
    (hε : 0 ≤ ε) (hεU : ε ≤ U) (X : (S : Ici (0 : ℝ)) → WaveState U S)
    {χ ψ : ℝ → ℝ} {Z : C(Icc ε U, WaveVector)}
    {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hψ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) (-1) ψ)
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh)
    {w : ℝ} (hw : w ∈ Ioo (regularTime (anchoringLapse (hε.trans hεU) X) 0) 0)
    (u : Icc ε U) (ω : UnitSphere) :
    compactifiedWaveRow hε hεU X χ Z w u =
      originalSpacetimeField (hε.trans hεU) X ψ ((w, u), ω) := by
  let V := regularTime (anchoringLapse (hε.trans hεU) X)
  have hm := hψ.2.2.2.1
  have hw' : w ∈ Ioo (V (-1)) 0 := ⟨(hm (by norm_num : (-1 : ℝ) < 0)).trans hw.1, hw.2⟩
  have he : V (ψ w) = w := (hψ.2.2.2.2.2.2.2.2.2.2.1 w hw').2.1
  have ht : 0 < ψ w := hm.lt_iff_lt.mp (by
    change V 0 < V (ψ w)
    rw [he]
    exact hw.1)
  have hraw := originalSpacetimeField_apply (hε.trans hεU) X hX hψ
    ⟨ψ w, ht.le⟩ (ψ w) ht.le le_rfl ⟨u, hε.trans u.property.1, u.property.2⟩ ω
  have hcomp := hB.1 ⟨ψ w, ht.le⟩ (ψ w) ht le_rfl u
  change V (ψ w) = w at he
  rw [show regularTime (anchoringLapse (hε.trans hεU) X) (ψ w) = w from he] at hraw hcomp
  exact hcomp.trans hraw.symm

theorem crossing_characteristic_cauchy_horizon {U ε W L va ua : ℝ}
    (hε : 0 ≤ ε) (hεU : ε ≤ U) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) {χ : ℝ → ℝ}
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)}
    {Dh : C(Icc ε U, WaveVector)} (y : WaveState W L)
    (hX : ∀ (S T : Ici (0 : ℝ)) (hST : S ≤ T),
      waveTranslate (a := 0) (U := U) (b := 0) (V := (S : ℝ)) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using (show (S : ℝ) ≤ T from hST)) (X T) = X S)
    (hrX : ∀ (S : Ici (0 : ℝ)) u v, 0 < (X S).1 u v 0)
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh)
    (hva : regularTime (anchoringLapse (hε.trans hεU) X) 0 < va)
    (ha : va < 0) (hb : 0 < va + W) (hua : ε < ua) (hLp : 0 < L) (huU : ua + L < U)
    (hry : ∀ t s, 0 < y.1 t s 0)
    (hmatch : ∀ t : Icc 0 W, va + (t : ℝ) ≤ 0 → ∀ s : Icc 0 L,
      y.1 t s = compactifiedWaveRow hε hεU X χ Z (va + t) (projIcc ε U hεU (ua + s))) :
    HasCharacteristicCauchyHorizon (hε.trans hεU) X hW hL y va ua := by
  classical
  let a := anchoringLapse (hε.trans hεU) X
  let V := regularTime a
  obtain ⟨ψ, hψ⟩ := exists_regular_time_coordinate hχ.1 hχ.2.1 hχ.2.2.1 (-1)
  let P := sphericalOpenRectangle (V (-1)) 0 (-1) U
  let N := sphericalOpenRectangle va (va + W) ua (ua + L)
  let M := characteristicCrossingRegion (V (-1)) U va (va + W) ua (ua + L)
  let G := originalSpacetimeField (hε.trans hεU) X ψ
  let Q := crossingSpacetimeField hW hL y va ua
  have hG : ContinuousOn G P := originalSpacetimeField_continuousOn (hε.trans hεU) X ψ hX
    hψ.2.2.2.2.2.2.2.2.1
  have hQ : Continuous Q := by
    change Continuous (fun p : SphericalSpacetime =>
      y.1 (projIcc 0 W hW (p.1.1 - va)) (projIcc 0 L hL (p.1.2 - ua)))
    fun_prop
  have he (p : SphericalSpacetime) (hp : p ∈ N) (hp0 : p.1.1 < 0) : Q p = G p := by
    have ht : p.1.1 - va ∈ Icc 0 W := ⟨by linarith [hp.1.1.1], by linarith [hp.1.1.2]⟩
    have hs : p.1.2 - ua ∈ Icc 0 L := ⟨by linarith [hp.1.2.1], by linarith [hp.1.2.2]⟩
    have hu : p.1.2 ∈ Icc ε U := ⟨hua.le.trans hp.1.2.1.le, hp.1.2.2.le.trans huU.le⟩
    have hh := hmatch ⟨p.1.1 - va, ht⟩ (by dsimp; linarith) ⟨p.1.2 - ua, hs⟩
    have hvt : va + (p.1.1 - va) = p.1.1 := by ring
    have hus : ua + (p.1.2 - ua) = p.1.2 := by ring
    change y.1 ⟨p.1.1 - va, ht⟩ ⟨p.1.2 - ua, hs⟩ =
      compactifiedWaveRow hε hεU X χ Z (va + (p.1.1 - va))
        (projIcc ε U hεU (ua + (p.1.2 - ua))) at hh
    rw [hvt, hus, projIcc_of_mem hεU hu] at hh
    change y.1 (projIcc 0 W hW (p.1.1 - va)) (projIcc 0 L hL (p.1.2 - ua)) = G p
    rw [projIcc_of_mem hW ht, projIcc_of_mem hL hs, hh]
    exact compactifiedWaveRow_eq_originalSpacetimeField hε hεU X hX hψ hB
      ⟨hva.trans hp.1.1.1, hp0⟩ ⟨p.1.2, hu⟩ p.2
  let F : SphericalSpacetime → WaveVector := fun p => if p ∈ N then Q p else G p
  have hFN (p : SphericalSpacetime) (hp : p ∈ N) : F p = Q p := if_pos hp
  have hFP (p : SphericalSpacetime) (hp : p ∈ P) : F p = G p := by
    by_cases hn : p ∈ N
    · exact (hFN p hn).trans (he p hn hp.1.1.2)
    · exact if_neg hn
  have hcF : ContinuousOn F M :=
    (hG.congr (fun p hp => (hFP p hp))).union_of_isOpen
      (hQ.continuousOn.congr (fun p hp => hFN p hp))
      ((isOpen_Ioo.prod isOpen_Ioo).prod isOpen_univ)
      ((isOpen_Ioo.prod isOpen_Ioo).prod isOpen_univ)
  have hrF (p : SphericalSpacetime) (hp : p ∈ M) : 0 < F p 0 := by
    rcases hp with hp | hp
    · rw [hFP p hp]
      exact originalSpacetimeField_radius_pos (hε.trans hεU) X ψ hrX p
    · rw [hFN p hp]
      exact hry _ _
  refine ⟨F, hcF, hrF, ?_, hFN, ?_⟩
  · intro S t ht htS u ω
    have hf : F ((V t, u), ω) = G ((V t, u), ω) := by
      by_cases hn : ((V t, (u : ℝ)), ω) ∈ N
      · exact (hFN _ hn).trans (he _ hn (hχ.2.2.2.2.2.1 t))
      · exact if_neg hn
    exact hf.trans (originalSpacetimeField_apply (hε.trans hεU) X hX hψ S t ht htS u ω)
  · have hH : ∀ p ∈ M, 0 < Real.exp (F p 2) := fun _ _ => Real.exp_pos _
    have hR : ∀ p ∈ M, 0 < F p 0 ^ 2 := fun p hp => sq_pos_of_pos (hrF p hp)
    have hcH := Real.continuous_exp.comp_continuousOn ((continuous_apply 2).comp_continuousOn hcF)
    have hcR := ((continuous_apply 0).comp_continuousOn hcF).pow 2
    have hmi : V (-1) < V 0 := hχ.2.2.2.1 (by norm_num : (-1 : ℝ) < 0)
    refine ⟨?_, characteristic_cauchy_horizon_on_crossing hmi hva ha hb
      (hε.trans_lt hua) (by linarith) huU hH hR hcH hcR⟩
    simpa only [min_eq_right hb.le] using
      characteristic_future_domain_on_crossing hmi hva ha (hε.trans_lt hua) huU hH hR hcH hcR

end CauchyHorizon
