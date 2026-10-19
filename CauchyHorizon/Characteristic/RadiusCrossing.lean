import CauchyHorizon.Characteristic.RadiusContact
import CauchyHorizon.Characteristic.PhysicalOverlap
import CauchyHorizon.Characteristic.TrappedLevel

/-! Positive-radius continuation beyond a trapped contact and ordering of first-contact times. -/

open MeasureTheory Set
open scoped ENNReal

namespace CauchyHorizon

theorem IsWaveIntegral.extend_past_trapped_level {M e Λ U V Y A : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hU1 : U ≤ 1) (hUR : U < r 0) (hY : 0 < Y) (hA : 0 ≤ A)
    (hc : Continuous h) (hi : ∀ t, IntegrableOn (fun w => h w ^ 2) (Ioi t))
    (hrc : Continuous r) (hr0 : ∀ t, r t ≠ 0)
    (hφ : ∀ t, IntegrableOn (fun w => h w / r w) (Ioi t))
    (hrd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r
      (horizonFunction (r t) (horizonMass M h t) e Λ) (Ici 0) t)
    {p : ℝ≥0∞} (hp : 4 ≤ p) {f : ℝ → ℝ} (hf : MemLp f p (volume.restrict (Icc 0 U)))
    (hfn : (eLpNorm f p (volume.restrict (Icc 0 U))).toReal ≤ A) {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
      (horizonWaveVelocity M e Λ V hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) x)
    (hlo : ∀ u v, Y ≤ x.1 u v 0)
    (hhit : x.1 ⟨U, hU, le_rfl⟩ ⟨V, hV, le_rfl⟩ 0 = Y)
    (hlam : x.2.1 ⟨U, hU, le_rfl⟩ ⟨V, hV, le_rfl⟩ 0 < 0) :
    ∃ H : ℝ, ∃ hH : 0 < H, ∃ y : WaveState U (V + H),
      IsWaveIntegral hU (add_nonneg hV hH.le) e Λ (incomingWaveCurve hU hUR hp hf (horizonPhi h r 0))
        (horizonWaveVelocity M e Λ (V + H) hc hi hrc hr0) (incomingWaveVelocity hUR hp hf) y ∧
      waveTranslate (a := 0) (U := U) (b := 0) (V := V) le_rfl (by simp)
        le_rfl (by simpa only [zero_add] using le_add_of_nonneg_right hH.le) y = x ∧
      (∀ u v, Y / 2 ≤ y.1 u v 0) ∧
      ∀ v : Icc 0 (V + H), V < (v : ℝ) → y.1 ⟨U, hU, le_rfl⟩ v 0 < Y := by
  obtain ⟨d, hd, hd1, hext⟩ := exists_horizon_row_extension (Vmax := V + 1) (by linarith)
    (hU.trans_lt hUR) hc hi hrc hr0 hφ hrd hY hA
  obtain ⟨y, hy, hmatch, hlow⟩ := hext hU hV hd.le hU1 le_rfl (by linarith only [hd1]) hUR hp hf hfn hx hlo
  let uU : Icc 0 U := ⟨U, hU, le_rfl⟩
  let vV : Icc 0 (V + d) := ⟨V, hV, le_add_of_nonneg_right hd.le⟩
  have hsame := hy.horizon_overlap hU (add_nonneg hV hd.le) hUR hU hV hUR hc hi hrc hr0 hp hf hf hx
    uU.property uU.property vV.property (show V ∈ Icc 0 V from ⟨hV, le_rfl⟩)
  have hrad : y.1 uU vV 0 = Y := (congrArg (fun z : WaveVector => z 0) hsame.1).trans hhit
  have hvel : y.2.1 uU vV 0 < 0 := by rw [hsame.2]; exact hlam
  refine ⟨d, hd, y, hy, hmatch, hlow, ?_⟩
  intro v hv
  have hh := hy.outgoing_trapped_radius_lt hU (add_nonneg hV hd.le) hUR hc hi hrc hr0 hφ hrd hp hf
    uU vV v hv hvel
  simpa only [hrad] using hh

theorem IsWaveIntegral.first_contact_time_order {M e Λ U V W S Y : ℝ} {h r : ℝ → ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUR : U < r 0)
    (hW : 0 ≤ W) (hS : 0 ≤ S) (hWR : W < r 0) (hWU : W ≤ U)
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
    (hyhit : y.1 ⟨W, hW, le_rfl⟩ ⟨S, hS, le_rfl⟩ 0 = Y) :
    V ≤ S ∧ (W < U → V < S) := by
  have hle : V ≤ S := by
    by_contra hnot
    have hSV : S < V := lt_of_not_ge hnot
    have he := hx.horizon_overlap hU hV hUR hW hS hWR hc hi hrc hr0 hp hfU hfW hy
      ⟨hW, hWU⟩ ⟨hW, le_rfl⟩ ⟨hS, hSV.le⟩ ⟨hS, le_rfl⟩
    have hr : x.1 ⟨W, hW, hWU⟩ ⟨S, hS, hSV.le⟩ 0 = Y :=
      (congrArg (fun z : WaveVector => z 0) he.1).trans hyhit
    exact (hxfirst _ _ hSV).ne' hr
  refine ⟨hle, ?_⟩
  intro hWU'
  apply lt_of_le_of_ne hle
  intro hVS
  have hv : V ∈ Icc 0 S := ⟨hV, hVS.le⟩
  have he := hx.horizon_overlap hU hV hUR hW hS hWR hc hi hrc hr0 hp hfU hfW hy
    ⟨hW, hWU⟩ ⟨hW, le_rfl⟩ ⟨hV, le_rfl⟩ hv
  have hr : x.1 ⟨W, hW, hWU⟩ ⟨V, hV, le_rfl⟩ 0 = Y := by
    rw [he.1]
    have ht : (⟨V, hv⟩ : Icc 0 S) = ⟨S, hS, le_rfl⟩ := Subtype.ext hVS
    rw [ht]
    exact hyhit
  have hanti := hx.radial_strictAnti hx.choose rfl
    (incomingWave_constraint_data hU hUR hp hfU (horizonPhi h r 0)).1
    ⟨V, hV, le_rfl⟩ (fun u => (hx.interior_gauge hU hV hUR hc hi hrc hr0 hφ hrd hp hfU u _).2.2.1)
  have hh := hanti (show (⟨W, hW, hWU⟩ : Icc 0 U) < ⟨U, hU, le_rfl⟩ from hWU')
  change x.1 ⟨U, hU, le_rfl⟩ ⟨V, hV, le_rfl⟩ 0 < x.1 ⟨W, hW, hWU⟩ ⟨V, hV, le_rfl⟩ 0 at hh
  rw [hr, hxhit] at hh
  exact hh.false

end CauchyHorizon
