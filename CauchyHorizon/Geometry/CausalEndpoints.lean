import CauchyHorizon.Analysis.CausalMonotonicity
import CauchyHorizon.Geometry.SphericalCausality

/-! Null-coordinate monotonicity and past endpoints for spherical causal curves. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CauchyHorizon

theorem IsFutureCausalVelocity.null_components_nonneg {H R : ℝ} {z : SpacetimeAmbient}
    (h : IsFutureCausalVelocity H R z) (hH : 0 < H) (hR : 0 ≤ R) :
    0 ≤ z.1.1 ∧ 0 ≤ z.1.2 := by
  have hp : 0 ≤ z.1.1 * z.1.2 := by
    have hn := mul_nonneg hR (sq_nonneg ‖z.2‖)
    have hq := h.2
    dsimp [sphericalVelocitySquare] at hq
    nlinarith
  obtain hpos | hneg := mul_nonneg_iff.mp hp
  · exact hpos
  · have hs := h.1
    constructor <;> linarith [hneg.1, hneg.2]

theorem IsFutureCausalVelocity.angular_norm_le {H R C : ℝ} {z : SpacetimeAmbient}
    (h : IsFutureCausalVelocity H R z) (hH : 0 < H) (hR : 0 < R)
    (hC : 0 ≤ C) (hbound : H ≤ R * C ^ 2) :
    ‖z.2‖ ≤ C * (z.1.1 + z.1.2) := by
  obtain ⟨hv, hu⟩ := h.null_components_nonneg hH hR.le
  have hq : R * ‖z.2‖ ^ 2 ≤ H * (z.1.1 * z.1.2) := by
    have hh := h.2
    dsimp [sphericalVelocitySquare] at hh
    nlinarith
  have hx : z.1.1 * z.1.2 ≤ (z.1.1 + z.1.2) ^ 2 := by
    nlinarith [sq_nonneg z.1.1, sq_nonneg z.1.2, mul_nonneg hv hu]
  have hb := hq.trans ((mul_le_mul_of_nonneg_right hbound (mul_nonneg hv hu)).trans
    (mul_le_mul_of_nonneg_left hx (mul_nonneg hR.le (sq_nonneg C))))
  have he : R * C ^ 2 * (z.1.1 + z.1.2) ^ 2 =
      R * (C * (z.1.1 + z.1.2)) ^ 2 := by ring
  rw [he, mul_le_mul_iff_right₀ hR] at hb
  nlinarith [norm_nonneg z.2, mul_nonneg hC (add_nonneg hv hu)]

theorem locallyLipschitzOn_linear_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set ℝ} {f : ℝ → E}
    (hf : LocallyLipschitzOn s f) (L : E →L[ℝ] ℝ) :
    LocallyLipschitzOn s (fun t => L (f t)) := by
  intro t ht
  obtain ⟨K, u, hu, hK⟩ := hf ht
  exact ⟨‖L‖₊ * K, u, hu, L.lipschitz.comp_lipschitzOnWith hK⟩

theorem IsPastInextendibleCausalCurve.null_coordinates_monotone
    {M : Set SphericalSpacetime} {H R : SphericalSpacetime → ℝ}
    {γ : ℝ → SphericalSpacetime} (hγ : IsPastInextendibleCausalCurve M H R γ)
    (hH : ∀ p ∈ M, 0 < H p) (hR : ∀ p ∈ M, 0 ≤ R p) :
    MonotoneOn (fun t => (γ t).1.1) (Iic 0) ∧
      MonotoneOn (fun t => (γ t).1.2) (Iic 0) := by
  let Lv : SpacetimeAmbient →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) SphereAmbient)
  let Lu : SpacetimeAmbient →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) SphereAmbient)
  have hd : ∀ᵐ t ∂volume.restrict (Iio (0 : ℝ)),
      0 ≤ deriv (fun t => (γ t).1.1) t ∧ 0 ≤ deriv (fun t => (γ t).1.2) t := by
    filter_upwards [hγ.2.2.2.1, ae_restrict_mem measurableSet_Iio] with t ht hm
    obtain ⟨z, hz, hv⟩ := ht
    have ht0 : t ≤ 0 := le_of_lt hm
    have hp := hγ.2.1 ht0
    have hc := hv.null_components_nonneg (hH _ hp) (hR _ hp)
    have hzv : HasDerivAt (fun t => (γ t).1.1) z.1.1 t := hz.fst.fst
    have hzu : HasDerivAt (fun t => (γ t).1.2) z.1.2 t := hz.fst.snd
    exact ⟨by rw [hzv.deriv]; exact hc.1, by rw [hzu.deriv]; exact hc.2⟩
  exact ⟨monotoneOn_Iic_of_locallyLipschitz_ae_deriv_nonneg
      (locallyLipschitzOn_linear_comp hγ.2.2.1 Lv) (hd.mono fun _ h => h.1),
    monotoneOn_Iic_of_locallyLipschitz_ae_deriv_nonneg
      (locallyLipschitzOn_linear_comp hγ.2.2.1 Lu) (hd.mono fun _ h => h.2)⟩

theorem IsPastInextendibleCausalCurve.not_trapped_in_compact
    {M K : Set SphericalSpacetime} {H R : SphericalSpacetime → ℝ}
    {γ : ℝ → SphericalSpacetime} (hγ : IsPastInextendibleCausalCurve M H R γ)
    (hH : ∀ p ∈ M, 0 < H p) (hR : ∀ p ∈ M, 0 < R p)
    (hK : IsCompact K) (hKM : K ⊆ M) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ p ∈ K, H p ≤ R p * C ^ 2) :
    ¬MapsTo γ (Iic 0) K := by
  intro htrap
  have hb (f : SphericalSpacetime → ℝ) (hc : Continuous f) :
      ∃ b : ℝ, ∀ t ≤ 0, b ≤ f (γ t) := by
    obtain ⟨b, hb⟩ := hK.bddBelow_image hc.continuousOn
    exact ⟨b, fun t ht => hb (mem_image_of_mem f (htrap ht))⟩
  obtain ⟨hv, hu⟩ := hγ.null_coordinates_monotone hH (fun p hp => (hR p hp).le)
  obtain ⟨bv, hbv⟩ := hb (fun p => p.1.1) (by fun_prop)
  obtain ⟨bu, hbu⟩ := hb (fun p => p.1.2) (by fun_prop)
  obtain ⟨v, hvl⟩ := exists_past_limit_of_monotoneOn hv hbv
  obtain ⟨u, hul⟩ := exists_past_limit_of_monotoneOn hu hbu
  let L (i : Fin 3) : SpacetimeAmbient →L[ℝ] ℝ :=
    C • ((ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) SphereAmbient)) +
      (EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) SphereAmbient)
  have hL (i : Fin 3) : MonotoneOn (fun t => L i (spacetimeInclusion (γ t))) (Iic 0) := by
    apply monotoneOn_Iic_of_locallyLipschitz_ae_deriv_nonneg
      (locallyLipschitzOn_linear_comp hγ.2.2.1 (L i))
    filter_upwards [hγ.2.2.2.1, ae_restrict_mem measurableSet_Iio] with t ht hm
    obtain ⟨z, hz, hzcone⟩ := ht
    have hdL : HasDerivAt (fun t => L i (spacetimeInclusion (γ t))) (L i z) t :=
      (L i).hasFDerivAt.comp_hasDerivAt t hz
    change 0 ≤ deriv (fun t => L i (spacetimeInclusion (γ t))) t
    rw [hdL.deriv]
    have ht0 : t ≤ 0 := le_of_lt hm
    have hpt := htrap ht0
    have hn := hzcone.angular_norm_le (hH _ (hKM hpt)) (hR _ (hKM hpt)) hC (hbound _ hpt)
    have hi : |z.2 i| ≤ ‖z.2‖ := PiLp.norm_apply_le z.2 i
    change 0 ≤ C * (z.1.1 + z.1.2) + z.2 i
    linarith [(abs_le.mp hi).1]
  have hlim (i : Fin 3) : ∃ l : ℝ,
      Tendsto (fun t => L i (spacetimeInclusion (γ t))) atBot (𝓝 l) := by
    obtain ⟨b, hb⟩ := hb (fun p => L i (spacetimeInclusion p)) (by
      apply (L i).continuous.comp
      exact continuous_fst.prodMk continuous_snd.subtype_val)
    exact exists_past_limit_of_monotoneOn (hL i) hb
  choose l hl using hlim
  let ω : SphereAmbient := WithLp.toLp 2 (fun i => l i - C * (v + u))
  have hω : Tendsto (fun t => ((γ t).2 : SphereAmbient)) atBot (𝓝 ω) := by
    have hh : Tendsto (fun t i => ((γ t).2 : SphereAmbient) i) atBot
        (𝓝 (fun i => l i - C * (v + u))) := by
      apply tendsto_pi_nhds.2
      intro i
      convert (hl i).sub ((hvl.add hul).const_mul C) using 1
      ext t
      change ((γ t).2 : SphereAmbient) i =
        C * ((γ t).1.1 + (γ t).1.2) + ((γ t).2 : SphereAmbient) i -
          C * ((γ t).1.1 + (γ t).1.2)
      ring
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.tendsto.comp hh
  have hωmem : ω ∈ Metric.sphere (0 : SphereAmbient) 1 :=
    Metric.isClosed_sphere.mem_of_tendsto hω (Eventually.of_forall fun t => (γ t).2.property)
  let q : SphericalSpacetime := ((v, u), ⟨ω, hωmem⟩)
  have hq : Tendsto γ atBot (𝓝 q) :=
    (hvl.prodMk_nhds hul).prodMk_nhds (tendsto_subtype_rng.2 hω)
  have hqK : q ∈ K := hK.isClosed.mem_of_tendsto hq
    ((eventually_le_atBot (0 : ℝ)).mono fun _ ht => htrap ht)
  exact hγ.2.2.2.2 q (hKM hqK) hq

theorem IsPastInextendibleCausalCurve.not_trapped_in_compact_of_continuous
    {M K : Set SphericalSpacetime} {H R : SphericalSpacetime → ℝ}
    {γ : ℝ → SphericalSpacetime} (hγ : IsPastInextendibleCausalCurve M H R γ)
    (hH : ∀ p ∈ M, 0 < H p) (hR : ∀ p ∈ M, 0 < R p)
    (hK : IsCompact K) (hKM : K ⊆ M)
    (hcH : ContinuousOn H K) (hcR : ContinuousOn R K) :
    ¬MapsTo γ (Iic 0) K := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (hcH.div hcR (fun p hp => (hR p (hKM hp)).ne'))
  let C := max 1 B
  have hC : 1 ≤ C := le_max_left _ _
  apply hγ.not_trapped_in_compact hH hR hK hKM (by linarith : 0 ≤ C)
  intro p hp
  have hb : H p / R p ≤ B := hB (mem_image_of_mem _ hp)
  have hBC : B ≤ C := le_max_right _ _
  have hCs : C ≤ C ^ 2 := by nlinarith
  have hh := (div_le_iff₀ (hR p (hKM hp))).mp (hb.trans (hBC.trans hCs))
  simpa only [mul_comm] using hh

end CauchyHorizon
