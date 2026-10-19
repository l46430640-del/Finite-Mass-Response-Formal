import CauchyHorizon.Reduced.RegularIncomingConstraint
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Compactness and a fixed finite energy give continuation bounds independent of the late cut. -/

open MeasureTheory Set Filter
open scoped Topology

namespace CauchyHorizon

def HasBoundedRegularContinuationData {U ε : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    (X : (S : Ici (0 : ℝ)) → WaveState U S) (χ : ℝ → ℝ)
    (Z : C(Icc ε U, WaveVector)) (O : C(Icc ε U, ℝ))
    (D : ℝ → C(Icc ε U, WaveVector)) (Dh : C(Icc ε U, WaveVector)) (ρ T₀ : ℝ) : Prop :=
  ∃ b R M : ℝ, 0 < b ∧ 0 < R ∧ 0 < M ∧
    (∀ T, T₀ ≤ T → 0 < T →
      ∃ z : C(Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b, C(Icc ε U, WaveVector)),
      ∃ d : Lp C(Icc ε U, WaveVector) 2
        (volume.restrict (Icc (regularTime (anchoringLapse (hε.trans hεU) X) T) b)),
        IsRegularContinuationData hε hεU X χ Z O T b z d ∧
        (∀ w u, ρ / 2 ≤ z w u 0) ∧
        ∃ hab : regularTime (anchoringLapse (hε.trans hεU) X) T ≤ b,
          IsIncomingRadialConstraint hab z d) ∧
    ∀ T, max T₀ 1 ≤ T →
      ‖compactifiedTransverseRow χ D Dh
        (regularTime (anchoringLapse (hε.trans hεU) X) T)‖ ≤ R ∧
      ∀ z d, IsRegularContinuationData hε hεU X χ Z O T b z d → ‖z‖ ≤ R ∧ ‖d‖ ≤ M

set_option maxHeartbeats 800000 in
theorem bounded_regular_continuation_data {U ε k ρ T₀ C : ℝ}
    (hε : 0 ≤ ε) (hεU : ε ≤ U) (X : (S : Ici (0 : ℝ)) → WaveState U S)
    (O : C(Icc ε U, ℝ)) {χ : ℝ → ℝ}
    (hχ : IsRegularTimeCoordinate (anchoringLapse (hε.trans hεU) X) 0 χ)
    {Z : C(Icc ε U, WaveVector)} {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hB : IsRegularWaveBoundary hε hεU X χ Z D Dh)
    (hO : IsRegularOpticalConstraint hε hεU X χ Z O)
    (hE : IsRegularWaveEnergy hε hεU k X χ Z T₀ C)
    (hdata : HasRegularContinuationData hε hεU X χ Z O ρ T₀) :
    HasBoundedRegularContinuationData hε hεU X χ Z O D Dh ρ T₀ := by
  let a := anchoringLapse (hε.trans hεU) X
  let Ψ := compactifiedWaveRow hε hεU X χ Z
  let F := fun w => waveNormalize ⟨U, hεU, le_rfl⟩ (regularWaveVelocityRow hε hεU X χ w)
  let Q := radialHorizonVelocity hεU Z O
  let S := max T₀ 1
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hVS := hχ.2.2.2.1 hS
  have hsub : Icc (regularTime a S) 0 ⊆ Ioc (regularTime a 0) 0 :=
    fun _ hw => ⟨hVS.trans_le hw.1, hw.2⟩
  obtain ⟨Rψ, hRψ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB.2.2.1.mono hsub)
  obtain ⟨RW, hRW⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB.2.2.2.1.mono hsub)
  have hLp : MemLp F 2 (volume.restrict (Icc (regularTime a S) 0)) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact (hE.2.1 S (le_max_left _ _)).1
  have hi := (memLp_two_iff_integrable_sq_norm hLp.1).1 hLp
  obtain ⟨b, hb, hd⟩ := hdata
  let R := |Rψ| + |RW| + b * ‖Q‖ + 1
  let M := Real.sqrt ((∫ w in Icc (regularTime a S) 0, ‖F w‖ ^ 2) + b * ‖Q‖ ^ 2) + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hM : 0 < M := by dsimp only [M]; positivity
  have hψR : Rψ + b * ‖Q‖ ≤ R := by
    dsimp only [R]
    linarith [le_abs_self Rψ, abs_nonneg RW]
  have hwR : RW ≤ R := by
    dsimp only [R]
    linarith [le_abs_self RW, abs_nonneg Rψ, mul_nonneg hb.le (norm_nonneg Q)]
  have hd' : ∀ T, T₀ ≤ T → 0 < T →
      ∃ z d, IsRegularContinuationData hε hεU X χ Z O T b z d ∧
        (∀ w u, ρ / 2 ≤ z w u 0) ∧
        ∃ hab : regularTime a T ≤ b, IsIncomingRadialConstraint hab z d := by
    intro T hT hTp
    obtain ⟨z, d, hz, hr⟩ := hd T hT hTp
    exact ⟨z, d, hz, hr, _, hz.incoming_radial_constraint hε hεU hTp hb.le hχ hO⟩
  refine ⟨b, R, M, hb, hR, hM, hd', ?_⟩
  intro T hT
  have hVT : regularTime a S ≤ regularTime a T := hχ.2.2.2.1.monotone hT
  have hVneg := (hχ.2.2.2.2.2.1 T).le
  refine ⟨(hRW _ ⟨hVT, hVneg⟩).trans hwR, ?_⟩
  intro z d hz
  change IsAffineCharacteristicData _ _ Ψ F Q z d at hz
  constructor
  · apply (ContinuousMap.norm_le _ hR.le).2
    intro w
    by_cases hw : (w : ℝ) ≤ 0
    · rw [hz.2.1 w hw]
      exact (hRψ _ ⟨hVT.trans w.property.1, hw⟩).trans
        ((le_add_of_nonneg_right (mul_nonneg hb.le (norm_nonneg Q))).trans hψR)
    · have hw0 := (lt_of_not_ge hw).le
      rw [hz.2.2.1 w hw0]
      calc
        ‖Ψ 0 + (w : ℝ) • Q‖ ≤ ‖Ψ 0‖ + ‖(w : ℝ) • Q‖ := norm_add_le _ _
        _ ≤ Rψ + b * ‖Q‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
          exact add_le_add (hRψ _ ⟨(hχ.2.2.2.2.2.1 S).le, le_rfl⟩)
            (mul_le_mul_of_nonneg_right w.property.2 (norm_nonneg Q))
        _ ≤ R := hψR
  · have henergy : (∫ w in Icc (regularTime a T) 0, ‖F w‖ ^ 2) ≤
        ∫ w in Icc (regularTime a S) 0, ‖F w‖ ^ 2 :=
      setIntegral_mono_set hi (Eventually.of_forall fun w => sq_nonneg ‖F w‖)
        (Eventually.of_forall fun _ hw => ⟨hVT.trans hw.1, hw.2⟩)
    have hn : ‖d‖ = Real.sqrt (∫ w in Icc (regularTime a T) b, ‖d w‖ ^ 2) := by
      rw [Lp.norm_def, toReal_eLpNorm (Lp.memLp d).1,
        lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) (Lp.memLp d).1]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div]
      rfl
    rw [hn, hz.2.2.2.2.2]
    exact (Real.sqrt_le_sqrt (add_le_add henergy le_rfl)).trans (le_add_of_nonneg_right zero_le_one)

end CauchyHorizon
