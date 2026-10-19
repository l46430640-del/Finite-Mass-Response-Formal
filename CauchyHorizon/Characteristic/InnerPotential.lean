import CauchyHorizon.Characteristic.HorizonBounds

/-! A fixed two-sided inner neighborhood has a positive radial potential. -/

open Set Filter
open scoped Topology

namespace CauchyHorizon.Background

theorem exists_positive_radial_potential (B : Background) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc (B.inner - δ) (B.inner + δ),
      B.innerRate / 4 ≤ radialPotential r B.charge B.cosmological := by
  have hd := horizonFunction_hasDerivAt (hasDerivAt_id B.inner)
    (hasDerivAt_const B.inner B.mass) B.inner_pos.ne' B.charge B.cosmological
  have hk := hd.unique B.hasDerivAt_F_inner
  simp only [id_eq, mul_one, mul_zero, zero_div, sub_zero] at hk
  have he : -4 * radialPotential B.inner B.charge B.cosmological =
      horizonFunction B.inner B.mass B.charge B.cosmological / B.inner +
        2 * horizonK B.inner B.mass B.charge B.cosmological := by
    unfold radialPotential horizonFunction horizonK
    field_simp [B.inner_pos.ne']
    ring
  rw [B.root_inner, zero_div, zero_add] at he
  have hcenter : radialPotential B.inner B.charge B.cosmological = B.innerRate / 2 := by
    linarith only [hk, he]
  have hp : ContinuousAt (fun r => radialPotential r B.charge B.cosmological) B.inner := by
    unfold radialPotential
    fun_prop (disch := positivity [B.inner_pos])
  have hnear : ∀ᶠ r in 𝓝 B.inner, B.innerRate / 4 < radialPotential r B.charge B.cosmological :=
    hp.tendsto.eventually_const_lt (by rw [hcenter]; linarith only [B.innerRate_pos])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnear
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro r hr
  have hm : r ∈ Metric.ball B.inner ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith only [hr.1, hr.2, hε]
  exact (hball hm).le

end CauchyHorizon.Background
