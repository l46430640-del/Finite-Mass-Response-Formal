import CauchyHorizon.Reduced.RadialFlux

/-! The recovered radial derivative commutes with horizontal restriction. -/

open MeasureTheory Set

namespace CauchyHorizon

theorem radialNuField_comp_left {A U V : ℝ} (hV : 0 ≤ V) (e Λ : ℝ)
    (zIn : C(Icc 0 A, WaveVector)) (z : WaveRectangle A V)
    (hr : ∀ u v, z u v 0 ≠ 0) (g : C(Icc 0 U, Icc 0 A)) :
    radialNuField hV e Λ (zIn.comp g) (z.comp g) (fun u v => hr (g u) v) =
      (radialNuField hV e Λ zIn z hr).comp g := by
  ext u v
  rfl

theorem radialNuField_prefix_eq {U V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W) (hVW : V ≤ W)
    (e Λ : ℝ) (zIn : C(Icc 0 U, WaveVector)) (z : WaveRectangle U W) (y : WaveRectangle U V)
    (hr : ∀ u v, z u v 0 ≠ 0) (hy : ∀ u v, y u v 0 ≠ 0)
    (he : ∀ u v, y u v = z u ⟨v, v.property.1, v.property.2.trans hVW⟩)
    (u : Icc 0 U) (v : Icc 0 V) :
    radialNuField hV e Λ zIn y hy u v =
      radialNuField hW e Λ zIn z hr u ⟨v, v.property.1, v.property.2.trans hVW⟩ := by
  have hi : continuousPrimitive hV (radialFluxField e Λ y hy u) v =
      continuousPrimitive hW (radialFluxField e Λ z hr u) ⟨v, v.property.1, v.property.2.trans hVW⟩ := by
    change (∫ t in (0 : ℝ)..v, intervalExtension hV (radialFluxField e Λ y hy u) t) =
      ∫ t in (0 : ℝ)..v, intervalExtension hW (radialFluxField e Λ z hr u) t
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le v.property.1] at ht
    have htV : t ∈ Icc 0 V := ⟨ht.1, ht.2.trans v.property.2⟩
    have htW : t ∈ Icc 0 W := ⟨ht.1, htV.2.trans hVW⟩
    simp only [intervalExtension_apply, projIcc_of_mem hV htV, projIcc_of_mem hW htW,
      radialFluxField_apply, he]
  rw [radialNuField_apply, radialNuField_apply, hi, he]

end CauchyHorizon
