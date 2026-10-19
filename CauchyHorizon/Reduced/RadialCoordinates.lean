import CauchyHorizon.Reduced.RadialLevel
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-! Joint radius and time coordinates from the actual first radial derivatives. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CauchyHorizon

theorem IsWaveIntegral.exists_radial_coordinate_chart {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (u : Icc 0 U) (v : Icc 0 V) (hu : (u : ℝ) ∈ Ioo 0 U) (hv : (v : ℝ) ∈ Ioo 0 V)
    (hν : radialNuField hV e Λ zIn x.1 hr u v ≠ 0) :
    let ν := radialNuField hV e Λ zIn x.1 hr
    ∃ ψ : ℝ × ℝ → ℝ, ψ (x.1 u v 0, v) = u ∧
      HasStrictFDerivAt ψ
        ((ContinuousLinearMap.toSpanSingleton ℝ (ν u v)⁻¹).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
          (ContinuousLinearMap.toSpanSingleton ℝ (x.2.1 u v 0 / ν u v)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ))
        (x.1 u v 0, (v : ℝ)) ∧
      ∀ᶠ p in 𝓝 (x.1 u v 0, (v : ℝ)), ψ p ∈ Ioo 0 U ∧ p.2 ∈ Ioo 0 V ∧
        intervalExtension hV (intervalExtension hU x.1 (ψ p)) p.2 0 = p.1 := by
  let ν := radialNuField hV e Λ zIn x.1 hr
  have hνn : ν u v ≠ 0 := hν
  let R := fun t z : ℝ => intervalExtension hV (intervalExtension hU x.1 z) t 0
  let F := fun (p : ℝ × ℝ) z => R p.2 z - p.1
  let L := fun (p : ℝ × ℝ) z =>
    (ContinuousLinearMap.toSpanSingleton ℝ
      (intervalExtension hV (intervalExtension hU x.2.1 z) p.2 0)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ) -
        ContinuousLinearMap.fst ℝ ℝ ℝ
  let N := fun (p : ℝ × ℝ) z => ContinuousLinearMap.toSpanSingleton ℝ
    (intervalExtension hV (intervalExtension hU ν z) p.2)
  have hcL : Continuous (Function.uncurry L) := by
    change Continuous (fun p : (ℝ × ℝ) × ℝ =>
      (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ
        (intervalExtension hV (intervalExtension hU x.2.1 p.2) p.1.2 0)).comp
          (ContinuousLinearMap.snd ℝ ℝ ℝ) - ContinuousLinearMap.fst ℝ ℝ ℝ)
    fun_prop
  have hcN : Continuous (Function.uncurry N) := by
    change Continuous (fun p : (ℝ × ℝ) × ℝ => ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ
      (intervalExtension hV (intervalExtension hU ν p.2) p.1.2))
    fun_prop
  have hnb : ∀ᶠ p : (ℝ × ℝ) × ℝ in 𝓝 ((x.1 u v 0, (v : ℝ)), (u : ℝ)),
      p.1.2 ∈ Ioo 0 V ∧ p.2 ∈ Ioo 0 U := by
    have hh : ∀ᶠ p : (ℝ × ℝ) × ℝ in 𝓝 ((x.1 u v 0, (v : ℝ)), (u : ℝ)),
        p ∈ (univ ×ˢ Ioo 0 V) ×ˢ Ioo 0 U :=
      ((isOpen_univ.prod isOpen_Ioo).prod isOpen_Ioo).mem_nhds ⟨⟨mem_univ _, hv⟩, hu⟩
    exact hh.mono (fun _ hp => ⟨hp.1.2, hp.2⟩)
  have dL : ∀ᶠ p : (ℝ × ℝ) × ℝ in 𝓝 ((x.1 u v 0, (v : ℝ)), (u : ℝ)),
      HasFDerivAt (F · p.2) (L p.1 p.2) p.1 := by
    filter_upwards [hnb] with p hp
    have hpU : p.2 ∈ Icc 0 U := ⟨hp.2.1.le, hp.2.2.le⟩
    have hpV : p.1.2 ∈ Icc 0 V := ⟨hp.1.1.le, hp.1.2.le⟩
    have hd := (ContinuousLinearMap.proj (0 : Fin 3) : WaveVector →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivWithinAt p.1.2
      (hx.longitudinal_derivative ⟨p.2, hpU⟩ hpV)
    change HasDerivWithinAt (fun t => intervalExtension hV (x.1 ⟨p.2, hpU⟩) t 0)
      (x.2.1 ⟨p.2, hpU⟩ ⟨p.1.2, hpV⟩ 0) (Icc 0 V) p.1.2 at hd
    have hh := ((hd.hasDerivAt (Icc_mem_nhds hp.1.1 hp.1.2)).hasFDerivAt.comp p.1
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt).sub (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
    simpa only [F, R, L, intervalExtension_apply, projIcc_of_mem hU hpU, projIcc_of_mem hV hpV,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', Function.comp_def, Pi.sub_def] using hh
  have dN : ∀ᶠ p : (ℝ × ℝ) × ℝ in 𝓝 ((x.1 u v 0, (v : ℝ)), (u : ℝ)),
      HasFDerivAt (F p.1 ·) (N p.1 p.2) p.2 := by
    filter_upwards [hnb] with p hp
    have hpU : p.2 ∈ Icc 0 U := ⟨hp.2.1.le, hp.2.2.le⟩
    have hpV : p.1.2 ∈ Icc 0 V := ⟨hp.1.1.le, hp.1.2.le⟩
    simpa only [F, R, N, ν, intervalExtension_apply, projIcc_of_mem hU hpU, projIcc_of_mem hV hpV] using
      (((hx.radial_hasDerivWithinAt hr hzin hinu ⟨p.1.2, hpV⟩ hpU).hasDerivAt
        (Icc_mem_nhds hp.2.1 hp.2.2)).sub_const p.1.1).hasFDerivAt
  have hNu : N (x.1 u v 0, v) u = ContinuousLinearMap.toSpanSingleton ℝ (ν u v) := by
    simp only [N, intervalExtension_apply, projIcc_of_mem hU u.property, projIcc_of_mem hV v.property]
  have hinv : (N (x.1 u v 0, v) u).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := ContinuousLinearMap.toSpanSingleton ℝ (ν u v)⁻¹)
    · apply ContinuousLinearMap.ext
      intro z
      simp only [hNu, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, ContinuousLinearMap.id_apply]
      field_simp [hνn]
    · apply ContinuousLinearMap.ext
      intro z
      simp only [hNu, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, ContinuousLinearMap.id_apply]
      field_simp [hνn]
  let ψ := implicitFunctionOfBivariate dL dN hcL.continuousAt hcN.continuousAt hinv
  have ht := tendsto_implicitFunctionOfBivariate dL dN hcL.continuousAt hcN.continuousAt hinv
  have hdf := hasStrictFDerivAt_implicitFunctionOfBivariate dL dN hcL.continuousAt hcN.continuousAt hinv
  have hinverse (z : ℝ) : (N (x.1 u v 0, v) u).inverse z = z / ν u v := hinv.inverse_apply_eq.2 (by
    rw [hNu]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    exact (div_mul_cancel₀ _ hνn).symm)
  have hcoeff : -((N (x.1 u v 0, v) u).inverse.comp (L (x.1 u v 0, v) u)) =
      (ContinuousLinearMap.toSpanSingleton ℝ (ν u v)⁻¹).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
        (ContinuousLinearMap.toSpanSingleton ℝ (x.2.1 u v 0 / ν u v)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    apply ContinuousLinearMap.ext
    intro p
    simp only [neg_apply, ContinuousLinearMap.comp_apply, hinverse,
      L, sub_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', smul_eq_mul,
      intervalExtension_apply, projIcc_of_mem hU u.property, projIcc_of_mem hV v.property]
    ring
  rw [hcoeff] at hdf
  have hself : ψ (x.1 u v 0, v) = u := by
    have he := eventually_apply_eq_iff_implicitFunctionOfBivariate dL dN hcL.continuousAt hcN.continuousAt hinv
    exact he.self_of_nhds.1 rfl
  refine ⟨ψ, hself, hdf, ?_⟩
  have hψ := ht (Ioo_mem_nhds hu.1 hu.2)
  have hv' : ∀ᶠ p : ℝ × ℝ in 𝓝 (x.1 u v 0, (v : ℝ)), p.2 ∈ Ioo 0 V :=
    continuous_snd.continuousAt (Ioo_mem_nhds hv.1 hv.2)
  filter_upwards [hψ, hv', eventually_apply_implicitFunctionOfBivariate dL dN hcL.continuousAt hcN.continuousAt hinv]
    with p hpu hpv hFp
  refine ⟨hpu, hpv, ?_⟩
  have he : F (x.1 u v 0, v) u = 0 := by
    simp only [F, R, intervalExtension_apply, projIcc_of_mem hU u.property,
      projIcc_of_mem hV v.property, sub_self]
  rw [he] at hFp
  exact sub_eq_zero.1 hFp

set_option maxHeartbeats 400000 in
theorem IsWaveIntegral.radial_coordinates_regular {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) (hr : ∀ u v, x.1 u v 0 ≠ 0)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    (hν : ∀ u v, radialNuField hV e Λ zIn x.1 hr u v < 0)
    {D : Set (ℝ × ℝ)} {χ : ℝ × ℝ → ℝ}
    (hcoord : ∀ p ∈ D, χ p ∈ Ioo 0 U ∧ p.2 ∈ Ioo 0 V ∧
      intervalExtension hV (intervalExtension hU x.1 (χ p)) p.2 0 = p.1) :
    let ν := radialNuField hV e Λ zIn x.1 hr
    let J := fun p : ℝ × ℝ =>
      let u := projIcc 0 U hU (χ p)
      let v := projIcc 0 V hV p.2
      (ContinuousLinearMap.toSpanSingleton ℝ (ν u v)⁻¹).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
        (ContinuousLinearMap.toSpanSingleton ℝ (x.2.1 u v 0 / ν u v)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    ContinuousOn χ D ∧ ContinuousOn J D ∧ ∀ p ∈ D, HasFDerivWithinAt χ (J p) D p := by
  let ν := radialNuField hV e Λ zIn x.1 hr
  have hder (p : ℝ × ℝ) (hp : p ∈ D) :
      let u := projIcc 0 U hU (χ p)
      let v := projIcc 0 V hV p.2
      HasFDerivWithinAt χ
        ((ContinuousLinearMap.toSpanSingleton ℝ (ν u v)⁻¹).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) -
          (ContinuousLinearMap.toSpanSingleton ℝ (x.2.1 u v 0 / ν u v)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ))
        D p := by
    have hc := hcoord p hp
    have hu : χ p ∈ Icc 0 U := ⟨hc.1.1.le, hc.1.2.le⟩
    have hv : p.2 ∈ Icc 0 V := ⟨hc.2.1.1.le, hc.2.1.2.le⟩
    let u : Icc 0 U := ⟨χ p, hu⟩
    let v : Icc 0 V := ⟨p.2, hv⟩
    have hhit : x.1 u v 0 = p.1 := by
      simpa only [intervalExtension_apply, projIcc_of_mem hU hu, projIcc_of_mem hV hv] using hc.2.2
    have hcenter : (x.1 u v 0, (v : ℝ)) = p := Prod.ext hhit rfl
    obtain ⟨ψ, hself, hd, hnear⟩ := hx.exists_radial_coordinate_chart hr hzin hinu u v hc.1 hc.2.1 (hν u v).ne
    rw [hcenter] at hself hd hnear
    have heq : χ =ᶠ[𝓝[D] p] ψ := by
      filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with q hq hψ
      have hχ := hcoord q hq
      have hχU : χ q ∈ Icc 0 U := ⟨hχ.1.1.le, hχ.1.2.le⟩
      have hψU : ψ q ∈ Icc 0 U := ⟨hψ.1.1.le, hψ.1.2.le⟩
      have hqV : q.2 ∈ Icc 0 V := ⟨hψ.2.1.1.le, hψ.2.1.2.le⟩
      have hh := hχ.2.2.trans hψ.2.2.symm
      simp only [intervalExtension_apply, projIcc_of_mem hU hχU, projIcc_of_mem hU hψU,
        projIcc_of_mem hV hqV] at hh
      exact congrArg Subtype.val ((hx.radial_strictAnti hr hzin hinu ⟨q.2, hqV⟩ (fun z => hν z _)).injective hh)
    have hh := hd.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq heq hself.symm
    simpa only [projIcc_of_mem hU hu, projIcc_of_mem hV hv] using hh
  have hcχ : ContinuousOn χ D := fun p hp => (hder p hp).continuousWithinAt
  have hcoeff : Continuous (fun q : ℝ × ℝ =>
      (ContinuousLinearMap.toSpanSingleton ℝ (ν (projIcc 0 U hU q.1) (projIcc 0 V hV q.2))⁻¹).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ) -
      (ContinuousLinearMap.toSpanSingleton ℝ
        (x.2.1 (projIcc 0 U hU q.1) (projIcc 0 V hV q.2) 0 /
          ν (projIcc 0 U hU q.1) (projIcc 0 V hV q.2))).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
    have hN : Continuous (fun q : ℝ × ℝ => ν (projIcc 0 U hU q.1) (projIcc 0 V hV q.2)) := by fun_prop
    have hL : Continuous (fun q : ℝ × ℝ => x.2.1 (projIcc 0 U hU q.1) (projIcc 0 V hV q.2) 0) := by fun_prop
    have hnonzero (q : ℝ × ℝ) : ν (projIcc 0 U hU q.1) (projIcc 0 V hV q.2) ≠ 0 :=
      (hν (projIcc 0 U hU q.1) (projIcc 0 V hV q.2)).ne
    have hInv := (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp (hN.inv₀ hnonzero)
    have hDiv := (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp (hL.div hN hnonzero)
    exact (hInv.clm_comp (continuous_const : Continuous (fun _ : ℝ × ℝ => ContinuousLinearMap.fst ℝ ℝ ℝ))).sub
      (hDiv.clm_comp (continuous_const : Continuous (fun _ : ℝ × ℝ => ContinuousLinearMap.snd ℝ ℝ ℝ)))
  have hpair : ContinuousOn (fun q : ℝ × ℝ => (χ q, q.2)) D :=
    hcχ.prodMk (continuous_snd.continuousOn : ContinuousOn (fun q : ℝ × ℝ => q.2) D)
  refine ⟨hcχ, ?_, hder⟩
  simpa only [Function.comp_def] using hcoeff.comp_continuousOn hpair

end CauchyHorizon
